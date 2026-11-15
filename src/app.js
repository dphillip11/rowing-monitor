// Pure ES Module Web Bluetooth Live Monitor for Heart Rate & Rowing Machines

const BLE_UUIDS = {
  HEART_RATE_SERVICE: 0x180d,
  HEART_RATE_MEASUREMENT: 0x2a37,
  BATTERY_SERVICE: 0x180f,
  BATTERY_LEVEL: 0x2a19,
  FITNESS_MACHINE_SERVICE: 0x1826,
  FTMS_ROWER_DATA: 0x2ad1,
  CONCEPT2_PM5_DISCOVERY: 'ce060000-43e5-11e4-916c-0800200c9a66',
  CONCEPT2_PM5_ROWING_SERVICE: 'ce060030-43e5-11e4-916c-0800200c9a66',
  CONCEPT2_PM5_GENERAL_STATUS: 'ce060031-43e5-11e4-916c-0800200c9a66',
  CONCEPT2_PM5_ADDITIONAL_STATUS_1: 'ce060032-43e5-11e4-916c-0800200c9a66',
  CONCEPT2_PM5_ADDITIONAL_STATUS_2: 'ce060033-43e5-11e4-916c-0800200c9a66',
};

const HR_ZONES = [
  { zone: 1, name: 'Recovery', minPct: 50, maxPct: 60 },
  { zone: 2, name: 'Steady State', minPct: 60, maxPct: 70 },
  { zone: 3, name: 'Tempo', minPct: 70, maxPct: 80 },
  { zone: 4, name: 'Threshold', minPct: 80, maxPct: 90 },
  { zone: 5, name: 'Peak / VO2', minPct: 90, maxPct: 100 },
];

const state = {
  devices: [],
  btHandles: new Map(), // deviceId -> { btDevice, characteristics }
  knownBtDevices: new Map(), // deviceId -> btDevice
  isRunning: false,
  isScanning: false,
  blePolicyBlocked: false,
  maxHrBpm: 190,
  countdownRemaining: 0,
  countdownTimerId: null,

  // Live metrics
  hrBpm: null,
  hrvMs: null,
  rrBuffer: [],
  paceSec: null,
  watts: null,
  peakWatts: 0,
  spm: null,
  dragFactor: null,

  // Raw device totals & reset baseline offsets
  rawDistance: 0,
  rawStrokes: 0,
  rawCalories: 0,
  offsetDistance: 0,
  offsetStrokes: 0,
  offsetCalories: 0,

  // Session accumulators
  elapsedSeconds: 0,
  powerSum: 0,
  powerCount: 0,
  spmSum: 0,
  spmCount: 0,
};

// DOM References
const el = {
  headerSummary: document.getElementById('header-device-summary'),
  btnStartStop: document.getElementById('btn-start-stop'),
  labelStartStop: document.getElementById('label-start-stop'),
  btnReset: document.getElementById('btn-reset'),
  btnScanBle: document.getElementById('btn-scan-ble'),
  labelScanBle: document.getElementById('label-scan-ble'),
  countdownOverlay: document.getElementById('countdown-overlay'),
  countdownNumber: document.getElementById('countdown-number'),
  btnCancelCountdown: document.getElementById('btn-cancel-countdown'),
  btnPairHr: document.getElementById('btn-pair-hr'),
  btnPairRower: document.getElementById('btn-pair-rower'),
  bleNotice: document.getElementById('ble-notice'),
  bleNoticeText: document.getElementById('ble-notice-text'),
  bleStandaloneLink: document.getElementById('ble-standalone-link'),
  devicesList: document.getElementById('devices-list'),
  inputMaxHr: document.getElementById('input-max-hr'),

  valPace: document.getElementById('val-pace'),
  valAvgPace: document.getElementById('val-avg-pace'),
  valSpeedMps: document.getElementById('val-speed-mps'),
  valDrag: document.getElementById('val-drag'),

  valHr: document.getElementById('val-hr'),
  valHrZoneLabel: document.getElementById('val-hr-zone-label'),
  valHrPct: document.getElementById('val-hr-pct'),
  zoneStrip: document.getElementById('hr-zone-strip'),

  valWatts: document.getElementById('val-watts'),
  valAvgWatts: document.getElementById('val-avg-watts'),
  valPeakWatts: document.getElementById('val-peak-watts'),
  valEfficiency: document.getElementById('val-efficiency'),

  valSpm: document.getElementById('val-spm'),
  valStrokes: document.getElementById('val-strokes'),
  valAvgSpm: document.getElementById('val-avg-spm'),
  valHrv: document.getElementById('val-hrv'),

  valDistance: document.getElementById('val-distance'),
  valElapsed: document.getElementById('val-elapsed'),
  valCalories: document.getElementById('val-calories'),
  valSessionStatus: document.getElementById('val-session-status'),
};

// Format helpers
function formatPace(secPer500m) {
  if (secPer500m === null || !Number.isFinite(secPer500m) || secPer500m <= 0) {
    return '--:--.-';
  }
  const mins = Math.floor(secPer500m / 60);
  const secs = Math.floor(secPer500m % 60);
  const tenths = Math.floor((secPer500m % 1) * 10);
  return `${mins}:${String(secs).padStart(2, '0')}.${tenths}`;
}

function formatDuration(totalSeconds) {
  const s = Math.max(0, Math.floor(totalSeconds));
  const hrs = Math.floor(s / 3600);
  const mins = Math.floor((s % 3600) / 60);
  const secs = s % 60;
  const mm = String(mins).padStart(2, '0');
  const ss = String(secs).padStart(2, '0');
  return hrs > 0 ? `${hrs}:${mm}:${ss}` : `${mm}:${ss}`;
}

function paceToWatts(paceSec) {
  if (!paceSec || paceSec <= 0) return 0;
  return Math.round(2.8 / Math.pow(paceSec / 500, 3));
}

function wattsToPace(watts) {
  if (!watts || watts <= 0) return null;
  return 500 * Math.cbrt(2.8 / watts);
}

function calculateRmssd(rrList) {
  if (rrList.length < 3) return null;
  let sumSq = 0;
  let count = 0;
  for (let i = 1; i < rrList.length; i++) {
    const prev = rrList[i - 1];
    const curr = rrList[i];
    if (Math.abs(curr - prev) < 350 && curr > 250 && curr < 2000) {
      const diff = curr - prev;
      sumSq += diff * diff;
      count++;
    }
  }
  return count > 0 ? Math.round(Math.sqrt(sumSq / count)) : null;
}

// BLE Binary Decoders
function parseHeartRate(value) {
  const flags = value.getUint8(0);
  const is16Bit = (flags & 0x01) !== 0;
  const energyPresent = (flags & 0x08) !== 0;
  const rrPresent = (flags & 0x10) !== 0;

  let offset = 1;
  let bpm;
  if (is16Bit) {
    bpm = value.getUint16(offset, true);
    offset += 2;
  } else {
    bpm = value.getUint8(offset);
    offset += 1;
  }

  if (energyPresent && offset + 2 <= value.byteLength) {
    offset += 2;
  }

  const rrIntervals = [];
  if (rrPresent) {
    while (offset + 2 <= value.byteLength) {
      const rrRaw = value.getUint16(offset, true);
      rrIntervals.push((rrRaw / 1024) * 1000);
      offset += 2;
    }
  }

  return { bpm, rrIntervals };
}

function parseFtmsRowerData(value) {
  const flags = value.getUint16(0, true);
  let offset = 2;

  const out = {
    spm: null,
    strokeCount: null,
    distance: null,
    paceSec: null,
    watts: null,
    calories: null,
    hrBpm: null,
  };

  if ((flags & 0x0001) === 0 && offset + 3 <= value.byteLength) {
    out.spm = value.getUint8(offset) * 0.5;
    offset += 1;
    out.strokeCount = value.getUint16(offset, true);
    offset += 2;
  }
  if ((flags & 0x0002) !== 0 && offset + 1 <= value.byteLength) offset += 1;
  if ((flags & 0x0004) !== 0 && offset + 3 <= value.byteLength) {
    out.distance =
      value.getUint8(offset) +
      (value.getUint8(offset + 1) << 8) +
      (value.getUint8(offset + 2) << 16);
    offset += 3;
  }
  if ((flags & 0x0008) !== 0 && offset + 2 <= value.byteLength) {
    const rawPace = value.getUint16(offset, true);
    out.paceSec = rawPace === 0xffff || rawPace === 0 ? null : rawPace;
    offset += 2;
  }
  if ((flags & 0x0010) !== 0 && offset + 2 <= value.byteLength) offset += 2;
  if ((flags & 0x0020) !== 0 && offset + 2 <= value.byteLength) {
    out.watts = Math.max(0, value.getInt16(offset, true));
    offset += 2;
  }
  if ((flags & 0x0040) !== 0 && offset + 2 <= value.byteLength) offset += 2;
  if ((flags & 0x0080) !== 0 && offset + 2 <= value.byteLength) offset += 2;
  if ((flags & 0x0100) !== 0 && offset + 5 <= value.byteLength) {
    const kcal = value.getUint16(offset, true);
    out.calories = kcal === 0xffff ? null : kcal;
    offset += 5;
  }
  if ((flags & 0x0200) !== 0 && offset + 1 <= value.byteLength) {
    out.hrBpm = value.getUint8(offset);
  }

  return out;
}

// UI Rendering
let bleNoticeTimeoutId = null;

function showBleNotice(message, showStandaloneLink = false) {
  if (!el.bleNotice || !el.bleNoticeText || !el.bleStandaloneLink) return;
  if (bleNoticeTimeoutId !== null) {
    window.clearTimeout(bleNoticeTimeoutId);
    bleNoticeTimeoutId = null;
  }
  if (!message) {
    el.bleNotice.classList.add('hidden');
    return;
  }
  el.bleNoticeText.textContent = message;
  el.bleNotice.classList.remove('hidden');
  if (showStandaloneLink) {
    el.bleStandaloneLink.setAttribute('href', window.location.href);
    el.bleStandaloneLink.classList.remove('hidden');
  } else {
    el.bleStandaloneLink.classList.add('hidden');
  }
  bleNoticeTimeoutId = window.setTimeout(() => {
    el.bleNotice?.classList.add('hidden');
  }, 6000);
}

function renderDevices() {
  if (!el.devicesList) return;

  if (state.devices.length === 0) {
    el.devicesList.innerHTML = `
      <div class="empty-devices">
        No paired Bluetooth devices detected yet. Click <strong>Scan Bluetooth</strong> to pair your heart rate monitor or rowing machine.
      </div>
    `;
  } else {
    el.devicesList.innerHTML = '';
    for (const dev of state.devices) {
      const card = document.createElement('div');
      card.className = `device-card${dev.status === 'connected' ? ' connected' : ''}`;

      const info = document.createElement('div');
      info.className = 'device-info';

      const nameEl = document.createElement('div');
      nameEl.className = 'device-name';
      nameEl.textContent = dev.name;

      const metaEl = document.createElement('div');
      metaEl.className = 'device-meta';
      const battText = dev.battery !== null ? ` · ${dev.battery}%` : '';
      metaEl.textContent = `${dev.protocol}${battText}`;

      const statusEl = document.createElement('div');
      statusEl.className = 'device-status';
      if (dev.status === 'connected') {
        statusEl.classList.add('status-connected');
        statusEl.textContent = '● Connected';
      } else if (dev.status === 'connecting') {
        statusEl.classList.add('status-connecting');
        statusEl.textContent = '◌ Connecting...';
      } else if (dev.status === 'error') {
        statusEl.classList.add('status-error');
        statusEl.textContent = `✖ ${dev.errorMessage || 'Connection failed'}`;
      } else {
        statusEl.classList.add('status-ready');
        statusEl.textContent = '○ Available';
      }

      info.append(nameEl, metaEl, statusEl);

      const actionBtn = document.createElement('button');
      actionBtn.type = 'button';
      if (dev.status === 'connected') {
        actionBtn.className = 'device-action-btn disconnect';
        actionBtn.textContent = 'Disconnect';
        actionBtn.addEventListener('click', () => disconnectDevice(dev.id));
      } else {
        actionBtn.className = 'device-action-btn';
        actionBtn.textContent = dev.status === 'connecting' ? 'Pairing...' : 'Connect';
        actionBtn.disabled = dev.status === 'connecting';
        actionBtn.addEventListener('click', () => connectDeviceById(dev.id));
      }

      card.append(info, actionBtn);
      el.devicesList.appendChild(card);
    }
  }

  const hrDev = state.devices.find((d) => d.kind === 'heart_rate' && d.status === 'connected');
  const rowerDev = state.devices.find((d) => d.kind === 'rower' && d.status === 'connected');
  if (el.headerSummary) {
    const hrLabel = hrDev ? hrDev.name : 'Not connected';
    const rowerLabel = rowerDev ? rowerDev.name : 'Not connected';
    el.headerSummary.textContent = `HR: ${hrLabel} · Rower: ${rowerLabel}`;
  }
}

function renderMetrics() {
  const avgWatts = state.powerCount > 0 ? Math.round(state.powerSum / state.powerCount) : null;
  const avgPace = avgWatts && avgWatts > 0 ? wattsToPace(avgWatts) : null;
  const avgSpm = state.spmCount > 0 ? (state.spmSum / state.spmCount).toFixed(1) : '--';

  if (el.valPace) el.valPace.textContent = formatPace(state.paceSec);
  if (el.valAvgPace) el.valAvgPace.textContent = `Avg ${formatPace(avgPace)}`;
  if (el.valSpeedMps) {
    el.valSpeedMps.textContent =
      state.paceSec && state.paceSec > 0 ? `${(500 / state.paceSec).toFixed(2)} m/s` : '-- m/s';
  }
  if (el.valDrag) {
    el.valDrag.textContent = state.dragFactor !== null ? `Drag ${state.dragFactor}` : 'Drag --';
  }

  if (el.valHr) el.valHr.textContent = state.hrBpm !== null ? String(state.hrBpm) : '--';
  let activeZone = null;
  if (state.hrBpm !== null && state.maxHrBpm > 0) {
    const pct = Math.round((state.hrBpm / state.maxHrBpm) * 100);
    if (pct < 60) activeZone = HR_ZONES[0];
    else if (pct < 70) activeZone = HR_ZONES[1];
    else if (pct < 80) activeZone = HR_ZONES[2];
    else if (pct < 90) activeZone = HR_ZONES[3];
    else activeZone = HR_ZONES[4];

    if (el.valHrPct) el.valHrPct.textContent = `${pct}% Max`;
    if (el.valHrZoneLabel) {
      el.valHrZoneLabel.textContent = `Zone ${activeZone.zone} · ${activeZone.name}`;
    }
  } else {
    if (el.valHrPct) el.valHrPct.textContent = '--% Max';
    if (el.valHrZoneLabel) el.valHrZoneLabel.textContent = 'Awaiting HR monitor';
  }

  if (el.zoneStrip) {
    const segs = el.zoneStrip.querySelectorAll('.zone-seg');
    segs.forEach((seg) => {
      const zNum = Number(seg.getAttribute('data-zone'));
      seg.classList.toggle('active', activeZone !== null && zNum === activeZone.zone);
    });
  }

  if (el.valWatts) el.valWatts.textContent = state.watts !== null ? `${state.watts} W` : '-- W';
  if (el.valAvgWatts) el.valAvgWatts.textContent = avgWatts !== null ? `Avg ${avgWatts} W` : 'Avg -- W';
  if (el.valPeakWatts) {
    el.valPeakWatts.textContent = state.peakWatts > 0 ? `Peak ${state.peakWatts} W` : 'Peak -- W';
  }
  if (el.valEfficiency) {
    const eff =
      state.watts !== null && state.hrBpm !== null && state.hrBpm > 0
        ? (state.watts / state.hrBpm).toFixed(2)
        : '--';
    el.valEfficiency.textContent = `Efficiency ${eff} W/bpm`;
  }

  const sessionStrokes = Math.max(0, state.rawStrokes - state.offsetStrokes);
  const sessionDistance = Math.max(0, Math.round(state.rawDistance - state.offsetDistance));
  const sessionCalories = Math.max(0, Math.round(state.rawCalories - state.offsetCalories));

  if (el.valSpm) el.valSpm.textContent = state.spm !== null ? `${state.spm} spm` : '-- spm';
  if (el.valStrokes) el.valStrokes.textContent = `${sessionStrokes} strokes`;
  if (el.valAvgSpm) el.valAvgSpm.textContent = `Avg ${avgSpm} spm`;
  if (el.valHrv) el.valHrv.textContent = state.hrvMs !== null ? `${state.hrvMs} ms` : '-- ms';

  if (el.valDistance) el.valDistance.textContent = sessionDistance.toLocaleString('en-US');
  if (el.valElapsed) el.valElapsed.textContent = formatDuration(state.elapsedSeconds);
  if (el.valCalories) el.valCalories.textContent = `${sessionCalories} kcal`;
  if (el.valSessionStatus) {
    el.valSessionStatus.textContent =
      state.countdownRemaining > 0
        ? `Starting in ${state.countdownRemaining}s`
        : state.isRunning
          ? 'Active'
          : 'Stopped';
  }

  if (el.btnStartStop && el.labelStartStop) {
    el.btnStartStop.classList.toggle('btn-running', state.isRunning);
    el.labelStartStop.textContent = state.isRunning ? 'Stop' : 'Start';
  }

  if (el.countdownOverlay && el.countdownNumber) {
    if (state.countdownRemaining > 0) {
      el.countdownNumber.textContent = String(state.countdownRemaining);
      el.countdownOverlay.classList.remove('hidden');
    } else {
      el.countdownOverlay.classList.add('hidden');
    }
  }
}

// Web Bluetooth Connection & GATT Service Auto-Discovery
async function connectBtDevice(deviceId, btDevice, preferredKind) {
  const devEntry = state.devices.find((d) => d.id === deviceId);
  if (devEntry) {
    devEntry.status = 'connecting';
    devEntry.errorMessage = '';
    renderDevices();
  }

  try {
    if (!btDevice.gatt) {
      throw new Error('GATT server unavailable on selected device.');
    }

    const server = await btDevice.gatt.connect();
    const subscribedChars = [];
    let battery = null;

    try {
      const battSvc = await server.getPrimaryService(BLE_UUIDS.BATTERY_SERVICE);
      const battChar = await battSvc.getCharacteristic(BLE_UUIDS.BATTERY_LEVEL);
      const battVal = await battChar.readValue();
      battery = battVal.getUint8(0);
    } catch {
      // Optional Battery Service absent
    }

    let hasRower = false;
    let hasHr = false;
    let protocol = '';

    const tryHr = async () => {
      try {
        const hrSvc = await server.getPrimaryService(BLE_UUIDS.HEART_RATE_SERVICE);
        const hrChar = await hrSvc.getCharacteristic(BLE_UUIDS.HEART_RATE_MEASUREMENT);
        await hrChar.startNotifications();
        hrChar.addEventListener('characteristicvaluechanged', (ev) => {
          const val = ev.target?.value;
          if (!val) return;
          const parsed = parseHeartRate(val);
          state.hrBpm = parsed.bpm;
          if (parsed.rrIntervals.length > 0) {
            state.rrBuffer = [...state.rrBuffer, ...parsed.rrIntervals].slice(-24);
            const rmssd = calculateRmssd(state.rrBuffer);
            if (rmssd !== null) state.hrvMs = rmssd;
          }
          renderMetrics();
        });
        subscribedChars.push(hrChar);
        hasHr = true;
        if (!protocol) protocol = 'BLE Heart Rate · 0x180D';
      } catch {
        // Not a Heart Rate sensor
      }
    };

    const tryRower = async () => {
      try {
        const ftmsSvc = await server.getPrimaryService(BLE_UUIDS.FITNESS_MACHINE_SERVICE);
        const rowerChar = await ftmsSvc.getCharacteristic(BLE_UUIDS.FTMS_ROWER_DATA);
        await rowerChar.startNotifications();
        rowerChar.addEventListener('characteristicvaluechanged', (ev) => {
          const val = ev.target?.value;
          if (!val) return;
          const parsed = parseFtmsRowerData(val);

          if (parsed.watts !== null) {
            state.watts = parsed.watts;
          } else if (parsed.paceSec !== null && parsed.paceSec > 0) {
            state.watts = paceToWatts(parsed.paceSec);
          }

          if (parsed.paceSec !== null) {
            state.paceSec = parsed.paceSec;
          } else if (state.watts && state.watts > 0) {
            state.paceSec = wattsToPace(state.watts);
          }

          if (state.watts !== null && state.watts > state.peakWatts) {
            state.peakWatts = state.watts;
          }
          if (parsed.spm !== null) state.spm = parsed.spm;
          if (parsed.strokeCount !== null) state.rawStrokes = parsed.strokeCount;
          if (parsed.distance !== null) state.rawDistance = parsed.distance;
          if (parsed.calories !== null) state.rawCalories = parsed.calories;
          if (parsed.hrBpm !== null && state.hrBpm === null) state.hrBpm = parsed.hrBpm;

          renderMetrics();
        });
        subscribedChars.push(rowerChar);
        hasRower = true;
        protocol = 'BLE FTMS · 0x1826';
        return;
      } catch {
        // Try Concept2 PM5 next
      }

      try {
        const pm5Svc = await server.getPrimaryService(BLE_UUIDS.CONCEPT2_PM5_ROWING_SERVICE);
        const genChar = await pm5Svc.getCharacteristic(BLE_UUIDS.CONCEPT2_PM5_GENERAL_STATUS);
        const add1Char = await pm5Svc.getCharacteristic(BLE_UUIDS.CONCEPT2_PM5_ADDITIONAL_STATUS_1);
        const add2Char = await pm5Svc.getCharacteristic(BLE_UUIDS.CONCEPT2_PM5_ADDITIONAL_STATUS_2);

        await genChar.startNotifications();
        genChar.addEventListener('characteristicvaluechanged', (ev) => {
          const v = ev.target?.value;
          if (!v) return;
          const distRaw = v.getUint8(3) + (v.getUint8(4) << 8) + (v.getUint8(5) << 16);
          state.rawDistance = distRaw * 0.1;
          if (v.byteLength >= 18) state.dragFactor = v.getUint8(17);
          renderMetrics();
        });

        await add1Char.startNotifications();
        add1Char.addEventListener('characteristicvaluechanged', (ev) => {
          const v = ev.target?.value;
          if (!v) return;
          state.spm = v.getUint8(5);
          const hrRaw = v.getUint8(6);
          if (hrRaw > 0 && hrRaw !== 255 && state.hrBpm === null) state.hrBpm = hrRaw;
          const paceRaw = v.getUint16(7, true);
          if (paceRaw > 0 && paceRaw !== 0xffff) {
            state.paceSec = paceRaw * 0.01;
            state.watts = paceToWatts(state.paceSec);
            if (state.watts > state.peakWatts) state.peakWatts = state.watts;
          }
          renderMetrics();
        });

        await add2Char.startNotifications();
        add2Char.addEventListener('characteristicvaluechanged', (ev) => {
          const v = ev.target?.value;
          if (!v) return;
          state.rawCalories = v.getUint16(6, true);
          renderMetrics();
        });

        subscribedChars.push(genChar, add1Char, add2Char);
        hasRower = true;
        protocol = 'BLE Concept2 PM5';
      } catch {
        // Not a PM5 device
      }
    };

    if (preferredKind === 'heart_rate') {
      await tryHr();
      if (!hasHr) await tryRower();
    } else {
      await tryRower();
      await tryHr();
    }

    if (!hasRower && !hasHr) {
      let exposed = '';
      try {
        if (server.getPrimaryServices) {
          const svcs = await server.getPrimaryServices();
          exposed = svcs.map((s) => s.uuid).join(', ');
        }
      } catch {
        // ignore
      }
      throw new Error(
        exposed
          ? `No Rowing (0x1826 / PM5) or Heart Rate (0x180D) service found. Exposed: ${exposed}`
          : 'No supported Rowing or Heart Rate GATT service found.'
      );
    }

    const resolvedKind = hasRower ? 'rower' : 'heart_rate';

    btDevice.addEventListener('gattserverdisconnected', () => {
      state.btHandles.delete(deviceId);
      const d = state.devices.find((item) => item.id === deviceId);
      if (d) d.status = 'disconnected';
      renderDevices();
    });

    state.btHandles.set(deviceId, { btDevice, characteristics: subscribedChars });

    for (const d of state.devices) {
      if (d.id === deviceId) {
        d.kind = resolvedKind;
        d.protocol = protocol;
        d.status = 'connected';
        if (battery !== null) d.battery = battery;
      } else if (d.kind === resolvedKind && d.status === 'connected') {
        disconnectDevice(d.id);
      }
    }

    state.isRunning = true;
    renderDevices();
    renderMetrics();
  } catch (err) {
    const msg = err instanceof Error ? err.message : 'Failed to connect GATT service';
    if (devEntry) {
      devEntry.status = 'error';
      devEntry.errorMessage = msg;
    }
    renderDevices();
  }
}

function disconnectDevice(deviceId) {
  const handle = state.btHandles.get(deviceId);
  if (handle) {
    handle.characteristics.forEach((c) => c.stopNotifications().catch(() => {}));
    if (handle.btDevice.gatt?.connected) {
      handle.btDevice.gatt.disconnect();
    }
    state.btHandles.delete(deviceId);
  }

  const dev = state.devices.find((d) => d.id === deviceId);
  if (dev) {
    dev.status = 'disconnected';
    dev.errorMessage = '';
  }
  renderDevices();
}

async function connectDeviceById(deviceId) {
  const cached = state.knownBtDevices.get(deviceId);
  if (cached) {
    await connectBtDevice(deviceId, cached);
    return;
  }

  const bt = navigator.bluetooth;
  if (bt && bt.getDevices) {
    const paired = await bt.getDevices();
    const found = paired.find((p) => p.id === deviceId);
    if (found) {
      state.knownBtDevices.set(deviceId, found);
      await connectBtDevice(deviceId, found);
      return;
    }
  }

  const dev = state.devices.find((d) => d.id === deviceId);
  if (dev) {
    dev.status = 'error';
    dev.errorMessage = 'Click Scan Bluetooth to re-authorize this device.';
    renderDevices();
  }
}

async function scanBluetooth(kindFilter) {
  const bt = navigator.bluetooth;
  if (!bt) {
    showBleNotice(
      'Web Bluetooth is not supported in this browser. Open in Chrome or Edge over HTTPS.'
    );
    return;
  }

  if (state.blePolicyBlocked) {
    showBleNotice(
      'Bluetooth scanning is blocked inside this embedded preview frame. Open this page in a standalone browser tab to connect physical devices.',
      true
    );
    return;
  }

  state.isScanning = true;
  if (el.btnScanBle) el.btnScanBle.disabled = true;
  if (el.labelScanBle) el.labelScanBle.textContent = 'Scanning...';

  try {
    const filters =
      kindFilter === 'heart_rate'
        ? [{ services: [BLE_UUIDS.HEART_RATE_SERVICE] }]
        : kindFilter === 'rower'
          ? [
              { services: [BLE_UUIDS.FITNESS_MACHINE_SERVICE] },
              { services: [BLE_UUIDS.CONCEPT2_PM5_ROWING_SERVICE] },
            ]
          : [
              { services: [BLE_UUIDS.HEART_RATE_SERVICE] },
              { services: [BLE_UUIDS.FITNESS_MACHINE_SERVICE] },
              { services: [BLE_UUIDS.CONCEPT2_PM5_ROWING_SERVICE] },
            ];

    const btDevice = await bt.requestDevice({
      filters,
      optionalServices: [
        BLE_UUIDS.HEART_RATE_SERVICE,
        BLE_UUIDS.FITNESS_MACHINE_SERVICE,
        BLE_UUIDS.CONCEPT2_PM5_ROWING_SERVICE,
        BLE_UUIDS.CONCEPT2_PM5_DISCOVERY,
        BLE_UUIDS.BATTERY_SERVICE,
      ],
    });

    state.knownBtDevices.set(btDevice.id, btDevice);

    const existing = state.devices.find((d) => d.id === btDevice.id);
    if (!existing) {
      state.devices.unshift({
        id: btDevice.id,
        name: btDevice.name || 'Bluetooth LE Device',
        kind: kindFilter || 'rower',
        protocol: 'Detecting GATT...',
        status: 'disconnected',
        battery: null,
        errorMessage: '',
      });
    }

    renderDevices();
    await connectBtDevice(btDevice.id, btDevice, kindFilter);
  } catch (err) {
    const msg = err instanceof Error ? err.message : 'Scan cancelled';
    if (/permissions policy|disallowed/i.test(msg)) {
      state.blePolicyBlocked = true;
      showBleNotice(
        'Bluetooth scanning is blocked inside this embedded preview frame. Open this page in a standalone browser tab to connect physical devices.',
        true
      );
    } else if (!/cancel/i.test(msg)) {
      showBleNotice(msg, false);
    }
  } finally {
    state.isScanning = false;
    if (el.btnScanBle) el.btnScanBle.disabled = false;
    if (el.labelScanBle) el.labelScanBle.textContent = 'Scan Bluetooth';
  }
}

function clearMonitorData() {
  state.elapsedSeconds = 0;
  state.powerSum = 0;
  state.powerCount = 0;
  state.spmSum = 0;
  state.spmCount = 0;
  state.peakWatts = 0;
  state.paceSec = null;
  state.watts = null;
  state.spm = null;
  state.dragFactor = null;
  state.hrBpm = null;
  state.hrvMs = null;
  state.rrBuffer = [];
  state.offsetDistance = state.rawDistance;
  state.offsetStrokes = state.rawStrokes;
  state.offsetCalories = state.rawCalories;
}

function cancelCountdown() {
  if (state.countdownTimerId !== null) {
    window.clearInterval(state.countdownTimerId);
    state.countdownTimerId = null;
  }
  state.countdownRemaining = 0;
  renderMetrics();
}

// Start / Stop & Reset handlers
function toggleStartStop() {
  if (state.countdownRemaining > 0) {
    cancelCountdown();
  }
  state.isRunning = !state.isRunning;
  renderMetrics();
}

function resetMonitor() {
  // 1. Stop current session & cancel any existing countdown
  if (state.countdownTimerId !== null) {
    window.clearInterval(state.countdownTimerId);
    state.countdownTimerId = null;
  }
  state.isRunning = false;

  // 2. Clear all monitor data
  clearMonitorData();

  // 3. Start 5-second countdown, then start session
  state.countdownRemaining = 5;
  renderMetrics();

  state.countdownTimerId = window.setInterval(() => {
    state.countdownRemaining -= 1;

    if (state.countdownRemaining <= 0) {
      if (state.countdownTimerId !== null) {
        window.clearInterval(state.countdownTimerId);
        state.countdownTimerId = null;
      }
      state.countdownRemaining = 0;
      // Re-anchor offsets right when the session starts
      state.offsetDistance = state.rawDistance;
      state.offsetStrokes = state.rawStrokes;
      state.offsetCalories = state.rawCalories;
      state.isRunning = true;
    }

    renderMetrics();
  }, 1000);
}

// 1Hz Session Clock & Average Accumulator
window.setInterval(() => {
  if (!state.isRunning) return;
  state.elapsedSeconds += 1;

  if (state.watts !== null && state.watts > 0) {
    state.powerSum += state.watts;
    state.powerCount += 1;
  }
  if (state.spm !== null && state.spm > 0) {
    state.spmSum += state.spm;
    state.spmCount += 1;
  }
  renderMetrics();
}, 1000);

// Initialization
async function init() {
  el.btnStartStop?.addEventListener('click', toggleStartStop);
  el.btnReset?.addEventListener('click', resetMonitor);
  el.btnCancelCountdown?.addEventListener('click', cancelCountdown);
  el.btnScanBle?.addEventListener('click', () => scanBluetooth());
  el.btnPairHr?.addEventListener('click', () => scanBluetooth('heart_rate'));
  el.btnPairRower?.addEventListener('click', () => scanBluetooth('rower'));

  el.inputMaxHr?.addEventListener('input', (ev) => {
    const val = Number(ev.target.value);
    if (Number.isFinite(val) && val >= 120 && val <= 230) {
      state.maxHrBpm = val;
      renderMetrics();
    }
  });

  el.bleNotice?.addEventListener('click', (ev) => {
    if (ev.target !== el.bleStandaloneLink) {
      el.bleNotice?.classList.add('hidden');
    }
  });

  const bt = navigator.bluetooth;
  if (!bt) {
    renderDevices();
    renderMetrics();
    return;
  }

  const policy = document.permissionsPolicy || document.featurePolicy;
  if (policy && typeof policy.allowsFeature === 'function' && !policy.allowsFeature('bluetooth')) {
    state.blePolicyBlocked = true;
  }

  if (bt.getDevices) {
    try {
      const paired = await bt.getDevices();
      for (const dev of paired) {
        state.knownBtDevices.set(dev.id, dev);
        state.devices.push({
          id: dev.id,
          name: dev.name || 'Paired BLE Device',
          kind: /pm5|row|erg|ftms|concept2|waterrower/i.test(dev.name || '') ? 'rower' : 'heart_rate',
          protocol: 'Paired Bluetooth LE',
          status: 'disconnected',
          battery: null,
          errorMessage: '',
        });
      }
    } catch {
      // ignore getDevices errors
    }
  }

  renderDevices();
  renderMetrics();
}

init();
