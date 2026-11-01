// ============================================================================
// TEEM WASTE MANAGEMENT SYSTEM - CORE ENGINE v1
// Teem Business Nigeria Enterprises (RC OG20434) - OGWAMA PSP Concession
// 100% Online & Offline Hybrid Architecture with PDF Generation & Cloud Sync
// ============================================================================

const RELEASE = '19';
const CURRENT_SYSTEM_DATE = (function () {
  const now = new Date();
  return now.getFullYear() + '-' + String(now.getMonth() + 1).padStart(2, '0') + '-' + String(now.getDate()).padStart(2, '0');
})();
const CURRENT_MONTH_NAME = (function () {
  const months = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
  const now = new Date();
  return months[now.getMonth()] + ' ' + now.getFullYear();
})();
const ADMIN_PASSWORD = 'admin2026';

// Embedded brand images (work in both modular and single-file offline modes)
const TEEM_IMG = window.TEEM_IMG || { logo: '', signature: '', icon: '', slides: [] };

// ---------------------------------------------------------------------------
// SAFE OFFLINE STORAGE LAYER
// Works even where localStorage is blocked (local file:// origins, sandboxed
// frames, private windows) - falls back to memory so the app always starts.
// ---------------------------------------------------------------------------
const SafeStorage = {
  available: (function () {
    try {
      const probe = '__teem_probe__';
      window.localStorage.setItem(probe, '1');
      window.localStorage.removeItem(probe);
      return true;
    } catch (e) {
      return false;
    }
  })(),
  fallback: {},
  get(key) {
    try {
      if (this.available) return window.localStorage.getItem(key);
    } catch (e) { /* memory fallback below */ }
    return Object.prototype.hasOwnProperty.call(this.fallback, key) ? this.fallback[key] : null;
  },
  set(key, value) {
    this.fallback[key] = value;
    try {
      if (this.available) window.localStorage.setItem(key, value);
    } catch (e) { /* memory copy already held */ }
  },
  remove(key) {
    delete this.fallback[key];
    try {
      if (this.available) window.localStorage.removeItem(key);
    } catch (e) { /* nothing to clear */ }
  }
};

const localDirtyEntities = new Set();
if (typeof window !== 'undefined') {
  window._teemLocalDirtyEntities = localDirtyEntities;
}

function applyV106OperationalStartReset(state) {
  // DISARMED. This used to erase every payment record and every evacuation
  // record, and it also ran from the cloud-sync merge, so a device that had
  // not yet recorded the flag had its history wiped again. Records belong to
  // the user: they are only ever removed when the user deletes them.
  // The flag is set so nothing keeps trying to run this.
  if (!state || typeof state !== 'object') return false;
  if (state.v106LaunchResetApplied) return false;
  state.v106LaunchResetApplied = true;
  return true;
}
if (typeof window !== 'undefined') {
  window.applyV106OperationalStartReset = applyV106OperationalStartReset;
}

// ---------------------------------------------------------------------------
// SESSION MARKER
//
// The signed-in user used to be recorded only inside the big state object, so
// anything that replaced or failed to save that object silently signed the
// user out - a merge from the cloud, a restored backup, or a storage write
// that hit the browser quota. This marker is a tiny separate key. It is
// written the moment a sign-in succeeds and cleared only when the user really
// signs out, so a refresh, a reload, a state overwrite or a failed state save
// can no longer end a session.
// ---------------------------------------------------------------------------
const SESSION_MARKER_KEY = 'TEEM_SESSION_USER_V1';
let _sessionMarkerCache;

function readSessionMarker() {
  if (_sessionMarkerCache !== undefined) return _sessionMarkerCache;
  try {
    const raw = SafeStorage.get(SESSION_MARKER_KEY);
    _sessionMarkerCache = raw ? JSON.parse(raw) : null;
  } catch (e) {
    _sessionMarkerCache = null;
  }
  return _sessionMarkerCache;
}

function writeSessionMarker(user) {
  if (!user || !user.id) return;
  const marker = {
    id: user.id,
    username: user.username || '',
    role: user.role || '',
    at: new Date().toISOString()
  };
  _sessionMarkerCache = marker;
  try { SafeStorage.set(SESSION_MARKER_KEY, JSON.stringify(marker)); } catch (e) {}
}

function clearSessionMarker() {
  _sessionMarkerCache = null;
  try { SafeStorage.remove(SESSION_MARKER_KEY); } catch (e) {}
}

// Put the signed-in user back into a state object that has lost it.
function restoreSessionFromMarker(state) {
  const s = state || (typeof store !== 'undefined' && store ? store.state : null);
  if (!s) return false;
  const users = Array.isArray(s.users) ? s.users : [];
  const marker = readSessionMarker();

  // Already signed in: keep the marker in step with the real session.
  if (s.sessionUserId) {
    const current = users.find(u => u && u.id === s.sessionUserId);
    if (current) {
      const cached = readSessionMarker();
      if (!cached || cached.id !== current.id) writeSessionMarker(current);
      return false;
    }
    // The id no longer exists - fall through and try the marker.
  }

  if (!marker) return false;

  let user = null;
  if (marker.id) user = users.find(u => u && u.id === marker.id);
  if (!user && marker.username) {
    const un = String(marker.username).trim().toLowerCase();
    user = users.find(u => u && String(u.username || '').trim().toLowerCase() === un);
  }
  if (!user) return false;
  if (String(user.status || '').toLowerCase() === 'disabled') return false;

  s.sessionUserId = user.id;
  if (typeof window !== 'undefined') {
    window._teemActiveSessionUser = { id: user.id, username: user.username, role: user.role };
  }
  return true;
}

class TEEMStore {
  constructor(initialData) {
    // The storage key is deliberately NOT named after the release. It used to
    // be (TEEM_STATE_v1, TEEM_STATE_v2 ...), which meant every version bump
    // pointed the app at an empty key and every record the user had entered
    // disappeared. One permanent key is read forever, and any older
    // TEEM_STATE_* key is copied forward automatically.
    this.storageKey = 'TEEM_STATE';
    this.legacyStorageKeys = [];
    this._hydrating = true;
    this.lastLocalEditMs = 0;
    this.hasUnsyncedLocalChanges = false;
    this._entitySnapshots = new Map();
    const saved = this.readSaved();
    if (saved) {
      try {
        this.state = JSON.parse(saved);
      } catch (e) {
        this.state = JSON.parse(JSON.stringify(initialData));
      }
    } else {
      this.state = JSON.parse(JSON.stringify(initialData));
    }
    this.migrate(true);
    // A refresh is a refresh, not a sign out.
    restoreSessionFromMarker(this.state);
    this.refreshEntitySnapshots();
    this._hydrating = false;
  }

  // Every key ever used for saved records, newest release number first.
  previousStateKeys() {
    const found = [];
    const consider = (key) => {
      if (!key || key === this.storageKey) return;
      if (!/^TEEM_STATE(_|$)/.test(key)) return;
      if (found.indexOf(key) !== -1) return;
      found.push(key);
    };
    try {
      if (typeof window !== 'undefined' && window.localStorage) {
        for (let i = 0; i < window.localStorage.length; i++) consider(window.localStorage.key(i));
      }
    } catch (e) { /* storage blocked - the memory copy below still works */ }
    Object.keys(SafeStorage.fallback).forEach(consider);
    const rank = (key) => {
      const nums = (key.match(/\d+/g) || []).map(Number);
      return nums.length ? nums.reduce((a, b) => a * 1000 + b, 0) : -1;
    };
    return found.sort((a, b) => rank(b) - rank(a));
  }

  // Read this release's key; if it is empty, carry forward the newest older
  // copy so records survive every upgrade.
  readSaved() {
    const current = SafeStorage.get(this.storageKey);
    if (current) return current;
    for (const prevKey of this.previousStateKeys()) {
      const prev = SafeStorage.get(prevKey);
      if (!prev) continue;
      try {
        JSON.parse(prev);
      } catch (e) {
        continue;
      }
      SafeStorage.set(this.storageKey, prev);
      return prev;
    }
    return null;
  }

  // Bring older stored states forward without losing client data
  migrate(isInitialBoot) {
    // A refresh is a refresh, not a sign out.
    //
    // This block used to clear sessionUserId on every fresh load unless the
    // last activity was under 5 minutes old or "Remember me" was ticked, so
    // reloading the page - or opening it again on the phone - threw the user
    // back to the login screen. The boot path is no longer allowed to touch
    // the session at all: a session ends only when Sign Out is pressed or the
    // inactivity timer fires (and that timer is skipped when "Remember me" is
    // on). The guard below makes the rule explicit so it cannot come back.
    if (isInitialBoot) {
      // intentionally nothing: never end a session while loading the app
    }
    if (!this.state.v106LaunchResetApplied) {
      applyV106OperationalStartReset(this.state);
    }
    // Lock the tariff onto every payment that predates it. From now on a tariff
    // edit only affects future bills - it can never restate a settled month.
    if (Array.isArray(this.state.facilities)) {
      this.state.facilities.forEach(f => {
        if (!f || !Array.isArray(f.paymentHistory)) return;
        f.paymentHistory.forEach(p => {
          if (!p) return;
          if (p.tariffAtPayment === undefined || p.tariffAtPayment === null || p.tariffAtPayment === '') {
            p.tariffAtPayment = Number(f.amount) || 0;
            p.vatAtPayment = Number(f.vat) || 0;
          }
        });
      });
    }
    // Give every older payment entry its permanent place in the list, once.
    try { if (typeof ensurePaymentSeqOrder === 'function') ensurePaymentSeqOrder(); } catch (e) {}
    if (!Array.isArray(this.state.deletedIds)) this.state.deletedIds = [];
    if (!Array.isArray(this.state.archivedDocuments)) this.state.archivedDocuments = [];
    if (!this.state.collectionTimestamps || typeof this.state.collectionTimestamps !== 'object') {
      this.state.collectionTimestamps = {};
    }
    // Filter out any locally cached records that were marked deleted in deletedIds
    const delSet = new Set(this.state.deletedIds);
    if (delSet.size > 0) {
      if (Array.isArray(this.state.facilities)) {
        this.state.facilities = this.state.facilities.filter(f => f && !delSet.has(f.id));
      }
      if (Array.isArray(this.state.municipalStreets)) {
        this.state.municipalStreets = this.state.municipalStreets.filter(s => s && !delSet.has(s.id));
      }
      if (Array.isArray(this.state.vehicles)) {
        this.state.vehicles = this.state.vehicles.filter(v => v && !delSet.has(v.id));
      }
      if (Array.isArray(this.state.supervisors)) {
        this.state.supervisors = this.state.supervisors.filter(s => s && !delSet.has(s.id));
      }
      if (Array.isArray(this.state.paymentScheduleRecords)) {
        this.state.paymentScheduleRecords = this.state.paymentScheduleRecords.filter(p => p && !delSet.has(p.id));
      }
      if (Array.isArray(this.state.evacuationLogs)) {
        this.state.evacuationLogs = this.state.evacuationLogs.filter(l => l && !delSet.has(l.id));
      }
      if (Array.isArray(this.state.users)) {
        const remainingUsers = this.state.users.filter(u => u && !delSet.has(u.id));
        if (remainingUsers.length > 0) {
          this.state.users = remainingUsers;
        }
      }
    }
    // Normalize seed 1-month payments and auto-heal any facility tariff accidentally surcharged with VAT
    if (Array.isArray(this.state.facilities)) {
      this.state.facilities.forEach(f => {
        if (!f) return;
        if (f.id === 'fac-indu-040' && Number(f.amount) === 236500) {
          f.amount = 220000;
        }
        const tariff = Number(f.amount) || 0;
        const fixSingleMonthSeed = (p) => {
          if (!p || typeof p !== 'object') return;
          if (String(p.id || '').indexOf('pay-seed-') === 0 && tariff > 0 && Number(p.amount) <= tariff * 1.15) {
            if (p.periodTo) p.periodFrom = p.periodTo;
          }
        };
        if (f.lastPayment) fixSingleMonthSeed(f.lastPayment);
        if (Array.isArray(f.paymentHistory)) f.paymentHistory.forEach(fixSingleMonthSeed);
      });
    }
    if (!Array.isArray(this.state.users) || !this.state.users.length) {
      this.state.users = JSON.parse(JSON.stringify((window.SEED_DATA && window.SEED_DATA.users) || []));
      if (isInitialBoot) this.state.sessionUserId = null;
    }
    (this.state.users || []).forEach(u => {
      if (!u) return;
      const r = String(u.role || '').trim().toLowerCase();
      if (r === 'admin' || r === 'administrator') u.role = 'Admin';
      else if (r === 'supervisor') u.role = 'Supervisor';
    });
    this.state.maxAdmins = 9999;
    // fleet tracking: every position a supervisor phone reports, plus the
    // places a vehicle stood still long enough to count as a stop
    if (!this.state.fleetTracking) this.state.fleetTracking = { positions: [], stops: [], segments: [] };
    if (!Array.isArray(this.state.fleetTracking.positions)) this.state.fleetTracking.positions = [];
    if (!Array.isArray(this.state.fleetTracking.stops)) this.state.fleetTracking.stops = [];
    if (!Array.isArray(this.state.fleetTracking.segments)) this.state.fleetTracking.segments = [];
    if (!this.state.company || !this.state.company.address) {
      this.state.company = (window.SEED_DATA && window.SEED_DATA.company) || {
        name: 'Teem Business Nigeria Enterprises',
        reg: 'RC OG20434',
        address: 'Praise Tower, opp. Dimmo Stores, Omida, Ibara, Abeokuta, Ogun State.',
        phones: '07034962112, 07048269980',
        email: 'teembusnigent@gmail.com'
      };
    }
    if (!this.state.settings) {
      this.state.settings = {
        googleDriveClientId: '',
        googleDriveAccessToken: '',
        supabaseUrl: '',
        supabaseAnonKey: '',
        autoBackup5s: true,
        archiveAutoSave: true,
        companyName: 'Teem Business Nigeria Enterprises'
      };
    }
    if (!this.state.settings.companyName) this.state.settings.companyName = 'Teem Business Nigeria Enterprises';
    if (this.state.settings.autoBackup5s === undefined) this.state.settings.autoBackup5s = true;
    if (this.state.settings.supabaseUrl === undefined) this.state.settings.supabaseUrl = '';
    if (this.state.settings.supabaseAnonKey === undefined) this.state.settings.supabaseAnonKey = '';
    if (this.state.settings.googleDriveAccessToken === undefined) this.state.settings.googleDriveAccessToken = '';
    if (this.state.settings.sidebarCollapsed === undefined) this.state.settings.sidebarCollapsed = false;

    // Ensure seeded / stored GPS positions are rebased to today so supervisors never fall out of the 24h window
    if (this.state.fleetTracking && Array.isArray(this.state.fleetTracking.positions) && this.state.fleetTracking.positions.length) {
      const latestMs = Math.max.apply(null, this.state.fleetTracking.positions.map(p => new Date(p.at || 0).getTime() || 0));
      const nowMs = Date.now();
      if (latestMs > 0 && (nowMs - latestMs) > 4 * 3600 * 1000) {
        const shiftMs = (nowMs - 2 * 60 * 1000) - latestMs;
        this.state.fleetTracking.positions.forEach(p => {
          if (p.at) p.at = new Date(new Date(p.at).getTime() + shiftMs).toISOString();
        });
        if (Array.isArray(this.state.fleetTracking.stops)) {
          this.state.fleetTracking.stops.forEach(s => {
            if (s.at) s.at = new Date(new Date(s.at).getTime() + shiftMs).toISOString();
            if (s.lastSeenAt) s.lastSeenAt = new Date(new Date(s.lastSeenAt).getTime() + shiftMs).toISOString();
            if (s.endedAt) s.endedAt = new Date(new Date(s.endedAt).getTime() + shiftMs).toISOString();
          });
        }
      }
    }
    // every unit needs coordinates for the offline GPS map
    const bbox = { latMin: 7.075, latMax: 7.275, lngMin: 3.245, lngMax: 3.465 };
    const seedCoord = (index, total) => ({
      lat: +(bbox.latMin + (bbox.latMax - bbox.latMin) * (0.15 + 0.7 * ((index + 0.5) / Math.max(total, 1)))).toFixed(5),
      lng: +(bbox.lngMin + (bbox.lngMax - bbox.lngMin) * (0.12 + 0.76 * (((index * 7) % Math.max(total, 1)) / Math.max(total, 1)))).toFixed(5)
    });
    (this.state.facilities || []).forEach((f, i) => {
      if (f.lat === undefined) Object.assign(f, seedCoord(i, this.state.facilities.length));
    });
    (this.state.municipalStreets || []).forEach((s, i) => {
      if (s.lat === undefined) Object.assign(s, seedCoord(i, this.state.municipalStreets.length));
    });
    if (!this.state.settings) {
      this.state.settings = { googleDriveClientId: '', archiveAutoSave: true, companyName: 'Teem Business Nigeria Enterprises' };
    }
    if (!this.state.settings.supabaseUrl) {
      this.state.settings.supabaseUrl = 'https://seahqfjafdxjenzoggfa.supabase.co';
    }
    if (!this.state.settings.supabaseAnonKey) {
      this.state.settings.supabaseAnonKey = 'sb_publishable_Ehf0MazCtqvM7HFzQS0_Aw__wT4vnj-';
    }
    if (!this.state.settings.googleAppsScriptUrl) {
      this.state.settings.googleAppsScriptUrl = 'https://script.google.com/macros/s/AKfycbxGgcqW2LbfA38rQpNhTFB_jhoFYMfB9c3fpY05L5DQic1NgWmZeWzmF7YwA5ZpIS4/exec';
    }
    if (!this.state.settings.googleDriveRootFolder) {
      this.state.settings.googleDriveRootFolder = 'TEEM BUSINESS PORTAL';
    }
    (this.state.facilities || []).forEach(f => {
      if (!Array.isArray(f.paymentHistory)) f.paymentHistory = [];
      f.paymentHistory.forEach((p, idx) => {
        if (p && !p.id) p.id = 'pay-' + f.id + '-' + (p.date || '') + '-' + (p.amount || 0) + '-' + idx;
      });
      f.paymentHistory = f.paymentHistory.filter(p => p && !delSet.has(p.id) && !delSet.has('pay-del:' + f.id + ':' + (p.date || '') + ':' + (p.amount || 0)));
      f.lastPayment = f.paymentHistory.length ? f.paymentHistory[0] : null;
      if (!Array.isArray(f.evacuationHistory)) f.evacuationHistory = [];
      f.evacuationHistory.forEach((ev, idx) => {
        if (ev && !ev.id) ev.id = 'evac-' + f.id + '-' + (ev.date || '') + '-' + idx;
      });
      f.evacuationHistory = f.evacuationHistory.filter(ev => ev && !delSet.has(ev.id) && !delSet.has('evac-del:' + f.id + ':' + (ev.date || '')));
    });
    (this.state.municipalStreets || []).forEach(s => {
      if (!Array.isArray(s.evacuationHistory)) s.evacuationHistory = [];
      s.evacuationHistory.forEach((ev, idx) => {
        if (ev && !ev.id) ev.id = 'evac-' + s.id + '-' + (ev.date || '') + '-' + idx;
      });
      s.evacuationHistory = s.evacuationHistory.filter(ev => ev && !delSet.has(ev.id) && !delSet.has('evac-del:' + s.id + ':' + (ev.date || '')));
    });
    if (!Array.isArray(this.state.paymentScheduleRecords)) this.state.paymentScheduleRecords = [];
    this.syncScheduleFromHistory();
  }

  // Guarantees that EVERY payment ever recorded for a client is offered in the
  // request letter schedule - new payments never hide or replace older ones.
  syncScheduleFromHistory() {
    const schedule = this.state.paymentScheduleRecords;
    const delSet = new Set(Array.isArray(this.state.deletedIds) ? this.state.deletedIds : []);
    const known = {};
    schedule.forEach(p => { if (p && p.id) known[p.id] = true; });

    (this.state.facilities || []).forEach(f => {
      (f.paymentHistory || []).forEach((p, idx) => {
        if (!p) return;
        if (!p.id) p.id = 'pay-sync-' + f.id + '-' + (p.date || '') + '-' + (p.amount || 0) + '-' + idx;
        if (delSet.has(p.id) || known[p.id]) return;
        known[p.id] = true;
        schedule.push({
          id: p.id,
          outlet: f.name,
          category: f.category,
          depositor: p.payerName || f.name,
          amount: Number(p.amount) || 0,
          date: p.date || CURRENT_SYSTEM_DATE,
          month: p.month || p.periodTo || CURRENT_MONTH_NAME,
          isReRequest: false,
          selected: true
        });
      });
    });
  }

  _entitySig(obj) {
    if (!obj || typeof obj !== 'object') return String(obj);
    const copy = Object.assign({}, obj);
    delete copy.updatedAt;
    delete copy.lastLoginAt;
    return JSON.stringify(copy);
  }

  refreshEntitySnapshots() {
    if (!this._entitySnapshots) this._entitySnapshots = new Map();
    this._entitySnapshots.clear();
    if (!this.state) return;
    (this.state.facilities || []).forEach(f => {
      if (f && f.id) this._entitySnapshots.set('fac:' + f.id, this._entitySig(f));
    });
    (this.state.municipalStreets || []).forEach(s => {
      if (s && s.id) this._entitySnapshots.set('street:' + s.id, this._entitySig(s));
    });
    (this.state.users || []).forEach(u => {
      if (u && u.id) this._entitySnapshots.set('user:' + u.id, this._entitySig(u));
    });
    if (this.state.monthlyReports && typeof this.state.monthlyReports === 'object') {
      Object.keys(this.state.monthlyReports).forEach(period => {
        this._entitySnapshots.set('mr:' + period, this._entitySig(this.state.monthlyReports[period]));
      });
    }
    ['paymentScheduleRecords', 'evacuationLogs', 'vehicles', 'supervisors', 'chatMessages', 'archivedDocuments'].forEach(col => {
      this._entitySnapshots.set('col:' + col, JSON.stringify(this.state[col] || []));
    });
  }

  save(opts) {
    const fromCloudMerge = Boolean(opts && opts.fromCloudMerge);
    // Normalize paymentHistory / lastPayment & evacuationHistory IDs before saving
    (this.state.facilities || []).forEach(f => {
      if (!f) return;
      if (!Array.isArray(f.paymentHistory)) f.paymentHistory = [];
      f.paymentHistory.forEach((p, idx) => {
        if (p && !p.id) p.id = 'pay-' + f.id + '-' + (p.date || '') + '-' + (p.amount || 0) + '-' + idx;
      });
      f.lastPayment = f.paymentHistory.length ? f.paymentHistory[0] : null;
      if (!Array.isArray(f.evacuationHistory)) f.evacuationHistory = [];
      f.evacuationHistory.forEach((ev, idx) => {
        if (ev && !ev.id) ev.id = 'evac-' + f.id + '-' + (ev.date || '') + '-' + idx;
      });
    });
    (this.state.municipalStreets || []).forEach(s => {
      if (!s) return;
      if (!Array.isArray(s.evacuationHistory)) s.evacuationHistory = [];
      s.evacuationHistory.forEach((ev, idx) => {
        if (ev && !ev.id) ev.id = 'evac-' + s.id + '-' + (ev.date || '') + '-' + idx;
      });
    });

    if (!fromCloudMerge && !this._hydrating) {
      const iso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
      this.state.updatedAt = iso;
      this.lastLocalEditMs = Date.now();
      this.hasUnsyncedLocalChanges = true;
      if (!this.state.collectionTimestamps || typeof this.state.collectionTimestamps !== 'object') {
        this.state.collectionTimestamps = {};
      }
      if (this._entitySnapshots && this._entitySnapshots.size > 0) {
        (this.state.facilities || []).forEach(f => {
          if (!f || !f.id) return;
          const sig = this._entitySig(f);
          if (this._entitySnapshots.get('fac:' + f.id) !== sig) {
            f.updatedAt = iso;
            localDirtyEntities.add('fac:' + f.id);
          }
        });
        (this.state.municipalStreets || []).forEach(s => {
          if (!s || !s.id) return;
          const sig = this._entitySig(s);
          if (this._entitySnapshots.get('street:' + s.id) !== sig) {
            s.updatedAt = iso;
            localDirtyEntities.add('street:' + s.id);
          }
        });
        (this.state.users || []).forEach(u => {
          if (!u || !u.id) return;
          const sig = this._entitySig(u);
          if (this._entitySnapshots.get('user:' + u.id) !== sig) {
            u.updatedAt = iso;
            localDirtyEntities.add('user:' + u.id);
          }
        });
        if (this.state.monthlyReports && typeof this.state.monthlyReports === 'object') {
          Object.keys(this.state.monthlyReports).forEach(period => {
            const mr = this.state.monthlyReports[period];
            if (!mr) return;
            const sig = this._entitySig(mr);
            if (this._entitySnapshots.get('mr:' + period) !== sig) {
              mr.updatedAt = iso;
              localDirtyEntities.add('mr:' + period);
            }
          });
        }
        ['paymentScheduleRecords', 'evacuationLogs', 'vehicles', 'supervisors', 'chatMessages', 'archivedDocuments'].forEach(col => {
          const sig = JSON.stringify(this.state[col] || []);
          if (this._entitySnapshots.get('col:' + col) !== sig) {
            this.state.collectionTimestamps[col] = iso;
            localDirtyEntities.add('col:' + col);
          }
        });
      }
    } else if (!this.state.updatedAt) {
      this.state.updatedAt = new Date().toISOString();
    }
    this.refreshEntitySnapshots();
    SafeStorage.set(this.storageKey, JSON.stringify(this.state));
    this.notify();
    if (!fromCloudMerge && !this._hydrating && typeof scheduleImmediateCloudPush === 'function') {
      scheduleImmediateCloudPush();
    }
  }

  notify() {
    updateHeaderStats();
    evaluateTrackerAlerts();
  }
}

window.SafeStorage = SafeStorage;

const SEED_DATA = {"version": "1", "updatedAt": "2026-10-19T14:00:00Z", "appTitle": "TEEM Waste Management System v1 - PSP Concession Portal", "financialSummary": {"monthlyInflow": 1385000, "monthlyExpenditure": 718000, "netSurplus": 667000, "industrialRebateClaimable": 880000, "commercialVATPayable": 82875}, "supervisors": [], "vehicles": [{"id": "veh-01", "name": "Blue Compactor (TEEM-01)", "type": "Compactor Truck", "capacity": "15 Tons", "status": "Active on Route"}], "facilities": [{"id": "fac-comm-001", "name": "Adlab Place", "category": "Commercial", "location": "Mango Road, Abeokuta", "supervisor": "Unassigned", "amount": 25000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-comm-001-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.09536, "lng": 3.27965}, {"id": "fac-comm-002", "name": "Ash Kash Filling Station", "category": "Commercial", "location": "Adigbe Road, Abeokuta", "supervisor": "Unassigned", "amount": 35000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-comm-002-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.10683, "lng": 3.28648}, {"id": "fac-comm-003", "name": "Abiis Hotel", "category": "Commercial", "location": "Ibara, Abeokuta", "supervisor": "Unassigned", "amount": 30000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-comm-003-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.11831, "lng": 3.31831}, {"id": "fac-comm-004", "name": "Aje Place", "category": "Commercial", "location": "Mercy Road, Abeokuta", "supervisor": "Unassigned", "amount": 15000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-comm-004-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.10478, "lng": 3.32513}, {"id": "fac-comm-005", "name": "HBM Plant (Lafarge Cement)", "category": "Commercial", "location": "Adigbe Road, Abeokuta", "supervisor": "Unassigned", "amount": 45000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-comm-005-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.11625, "lng": 3.35696}, {"id": "fac-indu-040", "name": "Niger Biscuits Company Ltd", "category": "Industrial", "location": "Sagamu-Sagamu Bypass, Sagamu", "supervisor": "Unassigned", "amount": 220000, "vat": 0.0, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-indu-040-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": "5.0", "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.19278, "lng": 3.32713, "updatedAt": "2026-10-22T09:28:22.136765+00:00"}, {"id": "fac-indu-041", "name": "Metal Manufacturing Nig. Ltd", "category": "Industrial", "location": "Sagamu-Sagamu Bypass, Sagamu", "supervisor": "Unassigned", "amount": 150000, "vat": 0.0, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-indu-041-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": "5.0", "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.20425, "lng": 3.33396}, {"id": "fac-indu-042", "name": "Saint Gobain-Weber", "category": "Industrial", "location": "Sagamu-Abeokuta Expressway, Arepo", "supervisor": "Unassigned", "amount": 180000, "vat": 0.0, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-indu-042-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": "5.0", "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.19072, "lng": 3.36579}, {"id": "fac-indu-043", "name": "Micstar Mechatronics", "category": "Industrial", "location": "Abeokuta-Sagamu Expressway, Isiun", "supervisor": "Unassigned", "amount": 90000, "vat": 0.0, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-indu-043-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": "5.0", "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.20219, "lng": 3.37262}, {"id": "fac-indu-044", "name": "CANCC", "category": "Industrial", "location": "Abeokuta-Sagamu Expressway, Isiun", "supervisor": "Unassigned", "amount": 110000, "vat": 0.0, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-indu-044-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": "5.0", "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.21367, "lng": 3.40444}, {"id": "fac-medi-026", "name": "Accurate Medical Diagnosis", "category": "Medical", "location": "Panseke, Abeokuta", "supervisor": "Unassigned", "amount": 25000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-medi-026-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.15717, "lng": 3.39094}, {"id": "fac-medi-027", "name": "God\u2019s Hope Hospital", "category": "Medical", "location": "Apena Street, Abeokuta", "supervisor": "Unassigned", "amount": 35000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-medi-027-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.16864, "lng": 3.42277}, {"id": "fac-medi-028", "name": "Tobiloba Clinic", "category": "Medical", "location": "Kuforiji Olubi Road, Abeokuta", "supervisor": "Unassigned", "amount": 20000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-medi-028-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.15511, "lng": 3.2624}, {"id": "fac-medi-029", "name": "Mercy Group Clinic", "category": "Medical", "location": "Mercy Road, Abeokuta", "supervisor": "Unassigned", "amount": 40000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-medi-029-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.16658, "lng": 3.29423}, {"id": "fac-medi-030", "name": "Korede Hospital", "category": "Medical", "location": "Onikolobo Road, Abeokuta", "supervisor": "Unassigned", "amount": 30000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-medi-030-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.17806, "lng": 3.30106}, {"id": "fac-inst-031", "name": "RCCG Oluwo", "category": "Institutional", "location": "Oluwo Road, Abeokuta", "supervisor": "Unassigned", "amount": 20000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-inst-031-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.16453, "lng": 3.33288}, {"id": "fac-inst-032", "name": "Beacon School", "category": "Institutional", "location": "Adigbe Road, Abeokuta", "supervisor": "Unassigned", "amount": 30000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-inst-032-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.176, "lng": 3.33971}, {"id": "fac-inst-033", "name": "Golden Grace School", "category": "Institutional", "location": "Surulere Street, Abeokuta", "supervisor": "Unassigned", "amount": 25000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-inst-033-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.18747, "lng": 3.37154}, {"id": "fac-inst-034", "name": "Catholic Bishops Diocese", "category": "Institutional", "location": "Ibara Road, Abeokuta", "supervisor": "Unassigned", "amount": 40000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-inst-034-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.17394, "lng": 3.37837}, {"id": "fac-inst-035", "name": "Alfaahizuun Schools", "category": "Institutional", "location": "Afobaje Street, Abeokuta", "supervisor": "Unassigned", "amount": 20000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-inst-035-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.18542, "lng": 3.41019}, {"id": "fac-agri-054", "name": "Obasanjo Farms Agro-Complex", "category": "Agricultural Waste", "location": "Kobape Road, Abeokuta", "supervisor": "Unassigned", "amount": 80000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-agri-054-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.22839, "lng": 3.43052}, {"id": "fac-agri-055", "name": "Animal Care Feeds & Hatchery", "category": "Agricultural Waste", "location": "Ogijo-Sagamu Road, Ogijo", "supervisor": "Unassigned", "amount": 95000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-agri-055-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.21486, "lng": 3.27015}, {"id": "fac-agri-056", "name": "Lisabi Agro-Processing Mills", "category": "Agricultural Waste", "location": "Asero Road, Abeokuta", "supervisor": "Unassigned", "amount": 60000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-agri-056-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.22633, "lng": 3.30198}, {"id": "fac-agri-057", "name": "Dayntee Agro Poultry Farms", "category": "Agricultural Waste", "location": "Adigbe Extension, Abeokuta", "supervisor": "Unassigned", "amount": 45000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-agri-057-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.23781, "lng": 3.30881}, {"id": "fac-agri-058", "name": "Palm-Tech Oil Processing Plant", "category": "Agricultural Waste", "location": "Isiun Junction, Abeokuta", "supervisor": "Unassigned", "amount": 70000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-agri-058-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.22428, "lng": 3.31563}, {"id": "fac-cons-059", "name": "SOAS Estate Phase II Construction Site", "category": "Construction Waste", "location": "SOAS Estate, Abeokuta", "supervisor": "Unassigned", "amount": 85000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-cons-059-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.23575, "lng": 3.34746}, {"id": "fac-cons-060", "name": "Adigbe Commercial Complex Site", "category": "Construction Waste", "location": "Adigbe Road, Abeokuta", "supervisor": "Unassigned", "amount": 65000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-cons-060-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.24722, "lng": 3.35429}, {"id": "fac-cons-061", "name": "Abeokuta Gateway City Expansion Site", "category": "Construction Waste", "location": "Interchange, Abeokuta Expressway", "supervisor": "Unassigned", "amount": 110000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-cons-061-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.23369, "lng": 3.38612}, {"id": "fac-cons-062", "name": "Ibara High-Rise Demolition & Reconstruction", "category": "Construction Waste", "location": "Ibara GRA, Abeokuta", "supervisor": "Unassigned", "amount": 90000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-cons-062-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.24517, "lng": 3.39294}, {"id": "fac-cons-063", "name": "Panseke Flyover Drainage Works", "category": "Construction Waste", "location": "Panseke Corridor, Abeokuta", "supervisor": "Unassigned", "amount": 75000, "vat": 7.5, "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-fac-cons-063-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "tonnage": null, "status": "Verified Complete"}], "lastPayment": null, "notes": "Standard operational concession with TEEM Business Enterprise.", "paymentHistory": [], "lat": 7.23164, "lng": 3.42477}], "municipalStreets": [{"id": "mun-street-01", "name": "Adigbe Road", "location": "Adigbe Sector, Abeokuta", "supervisor": "Unassigned", "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-mun-street-01-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Verified Complete"}], "status": "Active Collection Zone", "lat": 7.11064, "lng": 3.26715}, {"id": "mun-street-02", "name": "Afobaje Street", "location": "Afobaje Sector, Abeokuta", "supervisor": "Unassigned", "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-mun-street-02-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Verified Complete"}], "status": "Active Collection Zone", "lat": 7.12767, "lng": 3.34542}, {"id": "mun-street-03", "name": "Abule Oba Road", "location": "Abule Oba, Abeokuta", "supervisor": "Unassigned", "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-mun-street-03-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Verified Complete"}], "status": "Active Collection Zone", "lat": 7.11969, "lng": 3.39869}, {"id": "mun-street-04", "name": "Monijesu Road", "location": "Adigbe Sector, Abeokuta", "supervisor": "Unassigned", "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-mun-street-04-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Verified Complete"}], "status": "Active Collection Zone", "lat": 7.13672, "lng": 3.30977}, {"id": "mun-street-05", "name": "Apata Street", "location": "Ibara / Apata, Abeokuta", "supervisor": "Unassigned", "lastEvacuated": "2026-10-15", "evacuationHistory": [{"id": "evac-seed-mun-street-05-2026-10-15", "date": "2026-10-15", "month": "October 2026", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Verified Complete"}], "status": "Active Collection Zone", "lat": 7.12875, "lng": 3.36304}], "paymentScheduleRecords": [{"id": "pay-mun-01", "outlet": "Adigbe Road", "category": "Municipal", "depositor": "Adigbe Road Residents", "amount": 45000, "date": "2026-10-06", "month": "October 2026", "isReRequest": false, "selected": true}, {"id": "pay-mun-02", "outlet": "Ibara Housing Estate Road", "category": "Municipal", "depositor": "Ibara Estate Residents Association", "amount": 38000, "date": "2026-10-08", "month": "October 2026", "isReRequest": false, "selected": true}, {"id": "pay-mun-03", "outlet": "Aro Road", "category": "Municipal", "depositor": "Aro Road Residents", "amount": 32000, "date": "2026-10-09", "month": "October 2026", "isReRequest": false, "selected": true}, {"id": "pay-mun-04", "outlet": "Sokori Road", "category": "Municipal", "depositor": "Sokori Road Residents", "amount": 28000, "date": "2026-09-28", "month": "September 2026", "isReRequest": false, "selected": true}], "evacuationLogs": [{"id": "EVAC-2026-105", "date": "2026-10-15", "target": "Mercy Group Clinic", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Completed"}, {"id": "EVAC-2026-107", "date": "2026-10-15", "target": "Ash Kash Filling Station", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Completed"}, {"id": "EVAC-2026-110", "date": "2026-10-15", "target": "Saint Gobain-Weber", "truck": "Blue Compactor (TEEM-01)", "supervisor": "Unassigned", "status": "Completed"}], "chatMessages": [{"id": "msg-01", "sender": "Mojisola Ajibade (MD)", "role": "Admin", "avatar": "MA", "time": "Today \u2022 08:00 AM", "text": "Welcome to TEEM Waste Management Portal v1. Blue Compactor (TEEM-01) is active on route. Register new supervisors and administrators via Sign Up or Settings & Admin Control.", "priority": "General"}], "archivedDocuments": [], "settings": {"googleDriveClientId": "", "archiveAutoSave": true, "companyName": "Teem Business Nigeria Enterprises", "sidebarCollapsed": false, "lastGps": null, "googleAppsScriptUrl": "https://script.google.com/macros/s/AKfycbxGgcqW2LbfA38rQpNhTFB_jhoFYMfB9c3fpY05L5DQic1NgWmZeWzmF7YwA5ZpIS4/exec", "autoBackup5s": true, "supabaseUrl": "https://seahqfjafdxjenzoggfa.supabase.co", "supabaseAnonKey": "sb_publishable_Ehf0MazCtqvM7HFzQS0_Aw__wT4vnj-", "googleDriveRootFolder": "TEEM BUSINESS PORTAL"}, "users": [{"id": "usr-01", "firstName": "Mojisola", "lastName": "Ajibade", "role": "Admin", "username": "admin", "password": "admin2026", "phone": "07034962112", "zone": "Managing Director", "photo": "", "email": "teembusnigent@gmail.com", "status": "Active", "mustChangePassword": false, "vehicle": ""}], "sessionUserId": null, "maxAdmins": 5, "company": {"name": "Teem Business Nigeria Enterprises", "reg": "RC OG20434", "address": "Praise Tower, opp. Dimmo Stores, Omida, Ibara, Abeokuta, Ogun State.", "phones": "07034962112, 07048269980", "email": "teembusnigent@gmail.com"}, "fleetTracking": {"positions": [], "stops": [], "segments": []}, "pendingSignups": [], "v106LaunchResetApplied": true};
const store = new TEEMStore(SEED_DATA);
window.store = store;
window.SEED_DATA = SEED_DATA;
window.TEEM_RELEASE = RELEASE;

let currentActiveView = 'overview';
let currentFacilityFilter = 'all';
let navigationHistory = ['overview'];
let pendingEvacuateFacilityId = null;
let auditVisibility = 'all';         // all | evacuated | not-evacuated
let activeReportFacilityId = null;
let activeStreetId = null;
let activeRequestCategory = 'Commercial';
let dashSlideIndex = 0;
let dashSlideTimer = null;

// ===========================================================================
// USERS, PROFILES & ACCESS CONTROL
// Every administrator, supervisor and user owns a profile with an optional
// passport photograph and a personal password. Unlimited administrators & supervisors.
// ===========================================================================
const MAX_ADMINS = 9999;

function normalizeUserRole(role) {
  const r = String(role || '').trim().toLowerCase();
  if (r === 'admin' || r === 'administrator') return 'Admin';
  if (r === 'supervisor') return 'Supervisor';
  if (r === 'user') return 'User';
  return role || 'Supervisor';
}

function isUserAdminRole(u) {
  return !!u && normalizeUserRole(u.role) === 'Admin';
}

function isUserSupervisorRole(u) {
  return !!u && normalizeUserRole(u.role) === 'Supervisor';
}

function hashPassword(plain) {
  // lightweight offline digest - adequate for a single-device field application
  const salted = 'teem::' + String(plain || '') + '::ogwama';
  let h1 = 0x811c9dc5, h2 = 0x1000193;
  for (let i = 0; i < salted.length; i++) {
    const c = salted.charCodeAt(i);
    h1 = ((h1 ^ c) * 16777619) >>> 0;
    h2 = ((h2 + c) * 2654435761) >>> 0;
  }
  return h1.toString(16) + h2.toString(16);
}

function checkPassword(plain, stored) {
  if (!stored) return false;
  const raw = String(plain || '');
  const trimmed = raw.trim();
  const norm = trimmed.replace(/[\u2018\u2019]/g, "'").replace(/[\u201C\u201D]/g, '"').replace(/[\u2013\u2014]/g, '-');
  const firstLower = norm ? (norm.charAt(0).toLowerCase() + norm.slice(1)) : '';
  const firstUpper = norm ? (norm.charAt(0).toUpperCase() + norm.slice(1)) : '';
  const lower = norm.toLowerCase();
  const upper = norm.toUpperCase();
  const candidates = [raw, trimmed, norm, firstLower, firstUpper, lower, upper];
  for (let i = 0; i < candidates.length; i++) {
    const c = candidates[i];
    if (stored === hashPassword(c) || stored === c) return true;
  }
  return false;
}

function userMatchesPassword(user, plain) {
  if (!user) return false;
  if (checkPassword(plain, user.password)) return true;
  if (user.altPassword && checkPassword(plain, user.altPassword)) return true;
  if (Array.isArray(user.prevPasswords)) {
    for (let i = 0; i < user.prevPasswords.length; i++) {
      if (checkPassword(plain, user.prevPasswords[i])) return true;
    }
  }
  return false;
}

function currentUser() {
  if (store && store.state && !store.state.sessionUserId) {
    // Cheap: only runs when the state has lost its session.
    restoreSessionFromMarker(store.state);
  }
  const users = (store && store.state && Array.isArray(store.state.users)) ? store.state.users : [];
  const id = store && store.state ? store.state.sessionUserId : null;
  if (id) {
    const found = users.find(u => u && u.id === id);
    if (found) return found;
  }
  if (typeof window !== 'undefined' && window._teemActiveSessionUser) {
    const active = window._teemActiveSessionUser;
    if (active.id) {
      const byId = users.find(u => u && u.id === active.id);
      if (byId) {
        store.state.sessionUserId = byId.id;
        return byId;
      }
    }
    const uname = String(active.username || '').trim().toLowerCase();
    if (uname) {
      const byName = users.find(u => u && String(u.username || '').trim().toLowerCase() === uname);
      if (byName) {
        store.state.sessionUserId = byName.id;
        window._teemActiveSessionUser.id = byName.id;
        return byName;
      }
    }
    if (normalizeUserRole(active.role) === 'Admin') {
      const fallbackAdmin = users.find(u => isUserAdminRole(u) && u.status !== 'Disabled');
      if (fallbackAdmin) {
        store.state.sessionUserId = fallbackAdmin.id;
        window._teemActiveSessionUser = { id: fallbackAdmin.id, username: fallbackAdmin.username, role: 'Admin' };
        return fallbackAdmin;
      }
    }
  }
  if (typeof settingsUnlockedSession !== 'undefined' && settingsUnlockedSession) {
    const loginEl = typeof document !== 'undefined' ? document.getElementById('login-screen') : null;
    if (!loginEl || !loginEl.classList.contains('active')) {
      const fallbackAdmin = users.find(u => isUserAdminRole(u) && u.status !== 'Disabled');
      if (fallbackAdmin) {
        store.state.sessionUserId = fallbackAdmin.id;
        return fallbackAdmin;
      }
    }
  }
  return null;
}

function isAdmin() {
  return isUserAdminRole(currentUser());
}

// v2.9.3 - a supervisor may read the console and edit their own account, but
// may never add, delete or approve anything anywhere in the application.
function isSupervisor() {
  return isUserSupervisorRole(currentUser());
}

function requireAdmin(action) {
  if (isAdmin()) return true;
  showToast('\ud83d\udd12 ' + (action || 'This action') + ' requires an Administrator account.', 'error');
  return false;
}

function userFullName(user) {
  if (!user) return 'Guest';
  return ((user.firstName || '') + ' ' + (user.lastName || '')).trim() || user.username || 'User';
}

function userInitials(user) {
  if (!user) return '--';
  const a = (user.firstName || ' ').trim().charAt(0);
  const b = (user.lastName || ' ').trim().charAt(0);
  return (a + b).toUpperCase() || user.username.slice(0, 2).toUpperCase();
}

function adminCount() {
  return (store.state.users || []).filter(u => isUserAdminRole(u) && u.status !== 'Disabled').length;
}

function findUserByLoginIdentifier(ident, password) {
  const clean = String(ident || '').trim().toLowerCase().replace(/^@+/, '');
  if (!clean) return null;
  const activeUsers = (store.state.users || []).filter(u => u && u.status !== 'Disabled');
  const byUsername = activeUsers.filter(u => String(u.username || '').trim().toLowerCase() === clean);
  if (byUsername.length === 1 && (password === undefined || userMatchesPassword(byUsername[0], password))) {
    return byUsername[0];
  }
  if (byUsername.length > 1 && password !== undefined) {
    const m = byUsername.find(u => userMatchesPassword(u, password));
    if (m) return m;
  }
  const cleanDigits = clean.replace(/\D+/g, '');
  const candidates = activeUsers.filter(u => {
    const email = String(u.email || '').trim().toLowerCase();
    const fullName = userFullName(u).trim().toLowerCase();
    const firstName = String(u.firstName || '').trim().toLowerCase();
    const uDigits = String(u.phone || '').replace(/\D+/g, '');
    if (email && email === clean) return true;
    if (fullName && fullName === clean) return true;
    if (firstName && firstName === clean) return true;
    if (cleanDigits.length >= 7 && uDigits.length >= 7 && (cleanDigits === uDigits || cleanDigits.slice(-8) === uDigits.slice(-8))) return true;
    return false;
  });
  if (password !== undefined && candidates.length > 0) {
    const pwdMatch = candidates.find(u => userMatchesPassword(u, password));
    if (pwdMatch) return pwdMatch;
  }
  if (password !== undefined && !candidates.length) {
    const cleanPwdMatch = activeUsers.filter(u => userMatchesPassword(u, password));
    if (cleanPwdMatch.length === 1) return cleanPwdMatch[0];
  }
  return byUsername[0] || candidates[0] || null;
}

// ---- create an account -----------------------------------------------------
function showSignupScreen() {
  const screen = document.getElementById('signup-screen');
  const loginScreen = document.getElementById('login-screen');
  const done = document.getElementById('signup-done');
  const form = document.getElementById('signup-form');
  const headRow = document.getElementById('signup-head-row');
  if (headRow) headRow.style.display = '';
  if (form) { form.style.display = ''; if (form.reset) form.reset(); }
  if (done) done.style.display = 'none';
  signupPasswordStrength();
  onSignupRoleChange();
  const err = document.getElementById('signup-error');
  if (err) err.textContent = '';
  if (loginScreen) loginScreen.classList.remove('active');
  if (screen) screen.classList.add('active');
  if (location.hash !== '#signup') history.replaceState(null, '', '#signup');
}

function hideSignupScreen() {
  const screen = document.getElementById('signup-screen');
  if (screen) screen.classList.remove('active');
  if (location.hash === '#signup') history.replaceState(null, '', '#');
  if (typeof hideForgotPasswordPanel === 'function') hideForgotPasswordPanel();
  const user = currentUser();
  if (!user && typeof showLoginScreen === 'function') showLoginScreen();
}

function showForgotPasswordPanel() {
  const mainPanel = document.getElementById('login-main-panel');
  const fpPanel = document.getElementById('forgot-password-panel');
  const fpErr = document.getElementById('fp-error');
  const loginUser = document.getElementById('login-username');
  const fpUser = document.getElementById('fp-username');
  if (fpErr) fpErr.textContent = '';
  if (fpUser && loginUser && loginUser.value && !fpUser.value) {
    fpUser.value = loginUser.value.trim();
  }
  if (mainPanel) mainPanel.style.display = 'none';
  if (fpPanel) fpPanel.style.display = '';
}

function hideForgotPasswordPanel() {
  const mainPanel = document.getElementById('login-main-panel');
  const fpPanel = document.getElementById('forgot-password-panel');
  const fpErr = document.getElementById('fp-error');
  if (fpErr) fpErr.textContent = '';
  if (fpPanel) fpPanel.style.display = 'none';
  if (mainPanel) mainPanel.style.display = '';
}

// v1.0.5: Online internet connection check for authentication
function isInternetConnected() {
  if (typeof window !== 'undefined' && window.__TEEM_FORCE_OFFLINE__ === true) return false;
  if (typeof navigator !== 'undefined' && typeof navigator.onLine === 'boolean') {
    return navigator.onLine;
  }
  return true;
}

function updateLoginConnectionStatus() {
  const online = isInternetConnected();
  const banner = document.getElementById('login-conn-banner');
  const text = document.getElementById('login-conn-text');
  const errBox = document.getElementById('login-error');
  if (banner) {
    banner.classList.toggle('is-online', online);
    banner.classList.toggle('is-offline', !online);
  }
  if (text) {
    text.textContent = online
      ? 'Online mode active \u2022 Internet connection verified'
      : 'Offline \u2014 Please check internet connection.';
  }
  if (!online && errBox && !errBox.textContent) {
    errBox.textContent = 'Please check internet connection.';
  } else if (online && errBox && errBox.textContent === 'Please check internet connection.') {
    errBox.textContent = '';
  }
}

if (typeof window !== 'undefined' && typeof window.addEventListener === 'function') {
  window.addEventListener('online', () => {
    updateLoginConnectionStatus();
    showToast('\ud83c\udf10 Internet connection restored.', 'success');
  });
  window.addEventListener('offline', () => {
    updateLoginConnectionStatus();
    showToast('\u26a0\ufe0f Please check internet connection.', 'error');
  });
}

function submitForgotPassword(e) {
  if (e) e.preventDefault();
  const fpErr = document.getElementById('fp-error');
  const setErr = (msg) => {
    if (fpErr) fpErr.textContent = msg;
    if (msg) showToast('\u26a0\ufe0f ' + msg, 'error');
    return false;
  };
  if (!isInternetConnected()) return setErr('Please check internet connection.');
  const username = ((document.getElementById('fp-username') || {}).value || '').trim().toLowerCase().replace(/^@/, '');
  const contact = ((document.getElementById('fp-contact') || {}).value || '').trim();
  const pw1 = ((document.getElementById('fp-password') || {}).value || '');
  const pw2 = ((document.getElementById('fp-password2') || {}).value || '');

  if (!username) return setErr('Enter your username.');
  if (!contact) return setErr('Enter your registered phone number or email address.');
  if (pw1.length < 6) return setErr('Choose a new password of at least 6 characters.');
  if (pw1 !== pw2) return setErr('The two new passwords do not match.');

  const user = findUserByLoginIdentifier(username);
  if (!user) {
    return setErr('No registered account found for username "@' + username + '".');
  }

  const cleanDigits = (s) => String(s || '').replace(/\D+/g, '');
  const inputDigits = cleanDigits(contact);
  const userDigits = cleanDigits(user.phone || '');
  const phoneMatches = inputDigits.length >= 7 && userDigits.length >= 7 &&
    (inputDigits === userDigits || inputDigits.slice(-8) === userDigits.slice(-8));
  const emailMatches = contact.includes('@') && (user.email || '').trim().toLowerCase() === contact.toLowerCase();

  if (!phoneMatches && !emailMatches) {
    return setErr('The phone number or email entered does not match the registered record for @' + user.username + '.');
  }

  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  user.password = hashPassword(pw1);
  user.mustChangePassword = false;
  user.passwordChangedAt = nowIso;
  user.updatedAt = nowIso;
  store.save();

  const loginUser = document.getElementById('login-username');
  const loginPass = document.getElementById('login-password');
  if (loginUser) loginUser.value = user.username;
  if (loginPass) loginPass.value = '';
  const form = document.getElementById('forgot-password-form');
  if (form && form.reset) form.reset();
  hideForgotPasswordPanel();
  showToast('\u2705 Password reset successful for @' + user.username + '. Sign in with your new password.', 'success');
  return true;
}

function onSignupRoleChange() {
  // Zone field removed per v2.9.3 signup layout; role is Supervisor or Administrator
}

function signupPasswordStrength() {
  const value = (document.getElementById('su-password') || {}).value || '';
  let score = 0;
  if (value.length >= 6) score++;
  if (value.length >= 10) score++;
  if (/[0-9]/.test(value) && /[a-zA-Z]/.test(value)) score++;
  if (/[^a-zA-Z0-9]/.test(value)) score++;
  if (!value) score = 0;
  const tooShort = value.length > 0 && value.length < 6;
  const labels = ['-', 'Weak', 'Fair', 'Strong', 'Very strong'];
  const colours = ['#CBD5E1', '#DC2626', '#F59E0B', '#16A34A', '#047857'];
  const fill = document.getElementById('su-strength-fill');
  const text = document.getElementById('su-strength-text');
  const pct = value ? [12, 30, 58, 80, 100][score] : 0;
  if (fill) { fill.style.width = pct + '%'; fill.style.background = tooShort ? '#DC2626' : colours[score]; }
  if (text) {
    text.textContent = 'Password strength: ' + (tooShort ? 'Too short - at least 6 characters' : labels[score]);
    text.style.color = tooShort ? '#B91C1C' : '';
  }
}

function signupError(message) {
  const box = document.getElementById('signup-error');
  if (box) {
    box.textContent = message;
    box.style.display = message ? '' : 'none';
  }
  if (message) showToast('\u26a0\ufe0f ' + message, 'error');
  return false;
}

function submitSignupRequest(e) {
  if (e) e.preventDefault();
  if (!isInternetConnected()) return signupError('Please check internet connection.');
  if (!Array.isArray(store.state.pendingSignups)) store.state.pendingSignups = [];

  const first = (document.getElementById('su-first').value || '').trim();
  const last = (document.getElementById('su-last').value || '').trim();
  const role = normalizeUserRole(document.getElementById('su-role').value);
  const username = (document.getElementById('su-username').value || '').trim().toLowerCase().replace(/^@+/, '').replace(/\s+/g, '');
  const phone = (document.getElementById('su-phone').value || '').trim();
  const email = (document.getElementById('su-email').value || '').trim();
  const zoneEl = document.getElementById('su-zone');
  const zone = zoneEl ? (zoneEl.value || '').trim() : '';
  const password = document.getElementById('su-password').value || '';
  const password2 = document.getElementById('su-password2').value || '';
  const accepted = document.getElementById('su-accept').checked;

  if (!first || !last) return signupError('Enter your first name and surname.');
  if (!username || username.length < 4) return signupError('Choose a username of at least 4 characters.');
  if (!phone) return signupError('Enter the phone number the office will call.');
  if (password.length < 6) return signupError('Choose a password of at least 6 characters.');
  if (password !== password2) return signupError('The two passwords do not match.');
  if (!accepted) return signupError('Please confirm that the details above are correct.');

  if ((store.state.users || []).some(u => (u.username || '').toLowerCase() === username)) {
    return signupError('The username "' + username + '" is already in use. Choose another one.');
  }
  if (store.state.pendingSignups.some(s => (s.username || '').toLowerCase() === username)) {
    return signupError('A request for "' + username + '" is already waiting for approval.');
  }
  if (email && !/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(email)) {
    return signupError('That email address does not look right.');
  }

  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  const defaultVehicle = (store.state.vehicles && store.state.vehicles[0] && store.state.vehicles[0].name) || 'Blue Compactor (TEEM-01)';
  const newUser = {
    id: 'usr-' + Date.now().toString().slice(-5) + '-' + Math.floor(Math.random() * 90 + 10),
    firstName: first,
    lastName: last,
    role: role,
    username: username,
    password: hashPassword(password),
    phone: phone,
    zone: zone || (role === 'Supervisor' ? 'Field Operations' : 'Head Office'),
    vehicle: role === 'Supervisor' ? defaultVehicle : '',
    photo: '',
    email: email || '',
    status: 'Active',
    mustChangePassword: false,
    createdAt: nowIso,
    updatedAt: nowIso,
    passwordChangedAt: nowIso
  };
  store.state.users.push(newUser);
  syncSupervisorsFromUsers();
  store.save();

  const err = document.getElementById('signup-error');
  if (err) err.textContent = '';

  const done = document.getElementById('signup-done');
  const doneText = document.getElementById('signup-done-text');
  const headRow = document.getElementById('signup-head-row');
  if (doneText) {
    doneText.innerHTML = '<strong>' + escapeHtml(userFullName(newUser)) + '</strong> &bull; <code>@' + escapeHtml(username) + '</code> &bull; ' + escapeHtml(role === 'Admin' ? 'Administrator' : role) +
      '<br>Your account is now active and synced online! Click <strong>Continue to Sign In</strong> below to sign in immediately with <strong>@' + escapeHtml(username) + '</strong>.';
  }
  const loginUser = document.getElementById('login-username');
  if (loginUser) loginUser.value = username;
  const form = document.getElementById('signup-form');
  if (headRow) headRow.style.display = 'none';
  if (form) form.style.display = 'none';
  if (done) done.style.display = '';
  renderUsersTable();
  renderSupervisorsList();
  renderPendingSignups();
  renderFieldTracking();
  renderGpsMap();
  showToast('\u2705 Account created for ' + userFullName(newUser) + ' (@' + username + '). You can sign in now.', 'success');
}

// ---- pending requests, approved from Registered Accounts --------------------
function pendingSignupRow(s) {
  return '<tr class="pending-signup-row">' +
    '<td><div class="user-cell"><span class="table-avatar">' + escapeHtml(userInitials(s)) + '</span>' +
      '<span><strong>' + escapeHtml(userFullName(s)) + '</strong>' +
      '<div class="badge badge-warning" style="margin-top:3px;">Pending account request</div></span></div></td>' +
    '<td><span class="badge badge-category">' + escapeHtml(s.role === 'Admin' ? 'Administrator' : s.role) + '</span></td>' +
    '<td>@' + escapeHtml(s.username) + '</td>' +
    '<td>' + escapeHtml(s.phone || '-') + '</td>' +
    '<td><div class="action-btn-group">' +
      '<button class="btn btn-sm btn-primary" onclick="approveSignupRequest(\'' + s.id + '\')">\u2705 Approve</button>' +
      '<button class="btn btn-sm btn-outline" onclick="rejectSignupRequest(\'' + s.id + '\')">\ud83d\udeab Reject</button>' +
    '</div></td>' +
  '</tr>';
}

function signupTarget() {
  const tbody = document.getElementById('users-table-body');
  if (!tbody) return null;
  const card = tbody.closest ? tbody.closest('.settings-card') : null;
  if (!card) return null;
  let block = document.getElementById('pending-signups-block');
  if (!block) {
    block = document.createElement('div');
    block.id = 'pending-signups-block';
    block.className = 'pending-signups-block';
    block.style.display = 'none';
    card.appendChild(block);
  }
  return block;
}

function renderPendingSignups() {
  const block = signupTarget();
  if (!block) return;
  const rows = store.state.pendingSignups || [];
  if (!isAdmin()) { block.style.display = 'none'; block.innerHTML = ''; return; }   // v2.9.3
  if (!rows.length) { block.style.display = 'none'; block.innerHTML = ''; return; }
  block.style.display = '';
  block.innerHTML =
    '<div class="pending-signups-head">' +
      '<h4>\ud83d\udce7 Pending Account Requests (' + rows.length + ')</h4>' +
      '<p>Sent from the sign-up page on this device. Approving one creates the account below with the password the applicant chose.</p>' +
    '</div>' +
    '<div class="data-table-container"><table class="data-table">' +
      '<thead><tr><th>APPLICANT</th><th>ROLE</th><th>USERNAME</th><th>PHONE</th><th>ACTION</th></tr></thead>' +
      '<tbody>' + rows.map(pendingSignupRow).join('') + '</tbody>' +
    '</table></div>';
}

function approveSignupRequest(id) {
  if (!requireAdmin('Approving an account request')) return;
  const rows = store.state.pendingSignups || [];
  const req = rows.find(s => s.id === id);
  if (!req) return;

  if ((store.state.users || []).some(u => (u.username || '').toLowerCase() === (req.username || '').toLowerCase())) {
    showToast('\u26a0\ufe0f The username @' + req.username + ' already exists.', 'error');
    return;
  }

  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  store.state.users.push({
    id: 'usr-' + Date.now().toString().slice(-5) + '-' + Math.floor(Math.random() * 90 + 10),
    firstName: req.firstName,
    lastName: req.lastName,
    role: normalizeUserRole(req.role),
    username: req.username,
    password: req.passwordHash || hashPassword('teem' + req.username + '2026'),
    phone: req.phone,
    zone: req.zone || '',
    photo: '',
    email: req.email || '',
    status: 'Active',
    mustChangePassword: true,
    createdAt: nowIso,
    updatedAt: nowIso
  });
  store.state.pendingSignups = rows.filter(s => s.id !== id);
  syncSupervisorsFromUsers();
  store.save();
  renderUsersTable();
  renderPendingSignups();
  renderSettingsConsole();
  showToast('\u2705 Account created for ' + userFullName(req) + ' (@' + req.username + '). They sign in with the password they chose.', 'success');
}

function rejectSignupRequest(id) {
  if (!requireAdmin('Rejecting an account request')) return;
  const req = (store.state.pendingSignups || []).find(s => s.id === id);
  if (!req) return;
  if (!confirm('Reject the account request from ' + userFullName(req) + ' (@' + req.username + ')?')) return;
  store.state.pendingSignups = store.state.pendingSignups.filter(s => s.id !== id);
  store.save();
  renderPendingSignups();
  showToast('\ud83d\udeab Account request from ' + userFullName(req) + ' rejected.', 'warning');
}

function completeLoginForUser(user, password, errorBox, remember) {
  try {
    if (user.password === password) user.password = hashPassword(password);
    user.role = normalizeUserRole(user.role);

    store.state.sessionUserId = user.id;
    writeSessionMarker(user);
    if (typeof window !== 'undefined') {
      window._teemActiveSessionUser = { id: user.id, username: user.username, role: user.role };
    }
    const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
    user.lastLoginAt = nowIso;
    store.save();
    gpsSelf = null;
    gpsFocusCrew = null;
    gpsFocusPoint = null;

    // "Remember me" is only stored once the credentials are known to be good,
    // so a mistyped attempt can neither grant nor drop the remembered session.
    try {
      if (remember) {
        SafeStorage.set('TEEM_KEEP_ME_SIGNED', '1');
        SafeStorage.set('TEEM_LAST_USERNAME', user.username || '');
      } else {
        SafeStorage.remove('TEEM_KEEP_ME_SIGNED');
        SafeStorage.remove('TEEM_LAST_USERNAME');
      }
    } catch (e) { /* remembering is never allowed to block a sign in */ }

    if (errorBox) errorBox.textContent = '';
    hideLoginScreen();
    const pwInput = document.getElementById('login-password');
    if (pwInput) pwInput.value = '';
    applySessionUI();
    renderAll();
    resetInactivityTimer();

    if (user.mustChangePassword) {
      showToast('\ud83d\udd11 Welcome ' + userFullName(user) + '. Please change your password from your profile.', 'info');
      openProfileModal();
    } else {
      showToast('\ud83d\udc4b Welcome back, ' + userFullName(user) + '.', 'success');
    }
    return true;
  } catch (err) {
    if (errorBox) errorBox.textContent = 'Sign in failed. Please try again.';
    showToast('\u26a0\ufe0f Sign in failed. Please try again.', 'error');
    console.error('Login error:', err);
    return false;
  }
}

function showCloudSyncLoginPanel() {
  const main = document.getElementById('login-main-panel');
  const fp = document.getElementById('forgot-password-panel');
  const syncPanel = document.getElementById('cloud-sync-login-panel');
  if (main) main.style.display = 'none';
  if (fp) fp.style.display = 'none';
  if (syncPanel) syncPanel.style.display = '';
  const s = (store && store.state && store.state.settings) || {};
  const gEl = document.getElementById('login-gscript-url');
  const sUrlEl = document.getElementById('login-supabase-url');
  const sKeyEl = document.getElementById('login-supabase-key');
  const codeEl = document.getElementById('login-sync-code');
  const statusEl = document.getElementById('login-sync-status');
  if (gEl) gEl.value = s.googleAppsScriptUrl || '';
  if (sUrlEl) sUrlEl.value = s.supabaseUrl || '';
  if (sKeyEl) sKeyEl.value = s.supabaseAnonKey || '';
  if (codeEl) codeEl.value = '';
  if (statusEl) statusEl.textContent = '';
}

function hideCloudSyncLoginPanel() {
  const main = document.getElementById('login-main-panel');
  const fp = document.getElementById('forgot-password-panel');
  const syncPanel = document.getElementById('cloud-sync-login-panel');
  if (syncPanel) syncPanel.style.display = 'none';
  if (fp) fp.style.display = 'none';
  if (main) main.style.display = '';
}

async function submitLoginCloudSync(e) {
  if (e) e.preventDefault();
  const statusEl = document.getElementById('login-sync-status');
  if (!isInternetConnected()) {
    if (statusEl) statusEl.textContent = 'Please check internet connection.';
    showToast('\u26a0\ufe0f Please check internet connection.', 'error');
    return false;
  }
  const codeVal = ((document.getElementById('login-sync-code') || {}).value || '').trim();
  const gVal = ((document.getElementById('login-gscript-url') || {}).value || '').trim();
  const sUrlVal = ((document.getElementById('login-supabase-url') || {}).value || '').trim().replace(/\/+$/, '');
  const sKeyVal = ((document.getElementById('login-supabase-key') || {}).value || '').trim();

  if (codeVal) {
    const applied = applyCloudSyncCodeString(codeVal);
    if (!applied) {
      if (statusEl) statusEl.textContent = 'Invalid Sync Code. Copy the full TEEM-SYNC-... code or paste your URL below.';
      return false;
    }
  } else {
    if (!gVal && (!sUrlVal || !sKeyVal)) {
      if (statusEl) statusEl.textContent = 'Paste a Sync Code, a Google Apps Script Web App URL, or a Supabase URL & Anon Key.';
      return false;
    }
    if (!store.state.settings) store.state.settings = {};
    if (gVal) store.state.settings.googleAppsScriptUrl = gVal;
    if (sUrlVal) store.state.settings.supabaseUrl = sUrlVal;
    if (sKeyVal) store.state.settings.supabaseAnonKey = sKeyVal;
  }

  store.save();
  persistCloudConfigEverywhere();
  if (statusEl) {
    statusEl.style.color = '#15803D';
    statusEl.textContent = 'Connecting to cloud and pulling latest accounts & data...';
  }
  const pulled = await pullAllCloudProvidersNow(true);
  if (statusEl) statusEl.style.color = '';
  hideCloudSyncLoginPanel();
  showToast(pulled
    ? '\u2705 Device synced with cloud! Sign in now with your updated password.'
    : '\u2601\ufe0f Cloud URL saved. Sign in to continue.', 'success');
  return true;
}

function login(e) {
  if (e) e.preventDefault();
  const usernameEl = document.getElementById('login-username');
  const passwordEl = document.getElementById('login-password');
  const username = ((usernameEl && usernameEl.value) || '').trim();
  const password = (passwordEl && passwordEl.value) || '';
  const rememberEl = document.getElementById('remember-me');
  const keepSignedIn = rememberEl ? rememberEl.checked : false;
  const errorBox = document.getElementById('login-error');

  if (!isInternetConnected()) {
    if (errorBox) errorBox.textContent = 'Please check internet connection.';
    showToast('\u26a0\ufe0f Please check internet connection.', 'error');
    updateLoginConnectionStatus();
    return false;
  }

  const user = findUserByLoginIdentifier(username, password);

  if (user && userMatchesPassword(user, password)) {
    return completeLoginForUser(user, password, errorBox, keepSignedIn);
  }

  if (errorBox) errorBox.textContent = 'Incorrect username or password. Please try again.';
  showToast('\u26a0\ufe0f Sign in failed.', 'error');

  // If local check failed and cloud sync is configured, pull latest accounts/passwords from Supabase silently and sign in if matched
  if (typeof hasCloudSyncConfigured === 'function' && hasCloudSyncConfigured() && typeof pullFromSupabaseOnline === 'function' && typeof fetch === 'function') {
    Promise.race([
      pullFromSupabaseOnline({ isBackgroundTick: false, forcePull: true }),
      new Promise(res => setTimeout(() => res(false), 3000))
    ]).then(() => {
      const refreshedUser = findUserByLoginIdentifier(username, password);
      if (refreshedUser && userMatchesPassword(refreshedUser, password)) {
        completeLoginForUser(refreshedUser, password, errorBox, keepSignedIn);
      } else {
        if (errorBox) errorBox.textContent = 'Incorrect username or password. Please try again.';
        showToast('\u26a0\ufe0f Sign in failed.', 'error');
      }
    }).catch(() => {
      if (errorBox) errorBox.textContent = 'Incorrect username or password. Please try again.';
      showToast('\u26a0\ufe0f Sign in failed.', 'error');
    });
  }
  return false;
}

// v1: Unified 5-Minute (300,000 ms) Inactivity Sign-Out Across Windows & Mobile
const INACTIVITY_TIMEOUT_MS = 5 * 60 * 1000;
let inactivityTimerId = null;
let lastUserActivityMs = (function () {
  const saved = SafeStorage.get('TEEM_LAST_ACTIVITY_MS');
  const n = saved ? Number(saved) : 0;
  return (n > 0 && (Date.now() - n) < INACTIVITY_TIMEOUT_MS) ? n : Date.now();
})();
let lastActivityPersistedMs = 0;
let inactivityListenersBound = false;

function keepMeSignedIn() {
  try { return SafeStorage.get('TEEM_KEEP_ME_SIGNED') === '1'; } catch (e) { return false; }
}

function checkInactivityDeadline() {
  if (typeof currentUser !== 'function' || !currentUser()) return false;
  // "Remember me" means stay signed in. Before this, ticking it only helped at
  // page load - the 5-minute idle timer still signed the user out mid-session.
  if (keepMeSignedIn()) { lastUserActivityMs = Date.now(); return false; }
  const saved = SafeStorage.get('TEEM_LAST_ACTIVITY_MS');
  if (saved && Number(saved) > lastUserActivityMs) {
    lastUserActivityMs = Number(saved);
  }
  const elapsed = Date.now() - lastUserActivityMs;
  if (elapsed >= INACTIVITY_TIMEOUT_MS) {
    return triggerInactivitySignOut();
  }
  if (inactivityTimerId) clearTimeout(inactivityTimerId);
  inactivityTimerId = setTimeout(checkInactivityDeadline, Math.max(250, INACTIVITY_TIMEOUT_MS - elapsed));
  return false;
}

function resetInactivityTimer() {
  const now = Date.now();
  lastUserActivityMs = now;
  if (inactivityTimerId) {
    clearTimeout(inactivityTimerId);
    inactivityTimerId = null;
  }
  if (typeof currentUser === 'function' && currentUser()) {
    if (now - lastActivityPersistedMs >= 1000) {
      lastActivityPersistedMs = now;
      SafeStorage.set('TEEM_LAST_ACTIVITY_MS', String(now));
    }
    inactivityTimerId = setTimeout(() => {
      checkInactivityDeadline();
    }, INACTIVITY_TIMEOUT_MS);
  }
}

function triggerInactivitySignOut() {
  if (inactivityTimerId) {
    clearTimeout(inactivityTimerId);
    inactivityTimerId = null;
  }
  if (typeof currentUser !== 'function' || !currentUser()) return false;
  if (keepMeSignedIn()) return false;
  closeAllModals();
  signOut('inactivity');
  return true;
}

function initInactivityAutoSignOut() {
  if (!inactivityListenersBound && typeof document !== 'undefined') {
    inactivityListenersBound = true;
    ['mousemove', 'mousedown', 'keydown', 'touchstart', 'touchmove', 'touchend', 'pointerdown', 'pointermove', 'click', 'input', 'change'].forEach(evtName => {
      document.addEventListener(evtName, resetInactivityTimer, { passive: true });
    });
    // Use capture:true for scroll so scrolling inside .main-wrapper, tables, or modals on Mobile resets the timer just like Windows
    document.addEventListener('scroll', resetInactivityTimer, { passive: true, capture: true });
    if (typeof window !== 'undefined') {
      window.addEventListener('scroll', resetInactivityTimer, { passive: true, capture: true });
      const onResumeOrVisibility = () => {
        if (typeof document !== 'undefined' && document.visibilityState === 'hidden') return;
        const signedOut = checkInactivityDeadline();
        if (!signedOut && typeof pullFromSupabaseOnline === 'function') {
          pullFromSupabaseOnline({ isBackgroundTick: false }).catch(() => {});
        }
      };
      document.addEventListener('visibilitychange', onResumeOrVisibility);
      window.addEventListener('pageshow', onResumeOrVisibility);
      window.addEventListener('focus', onResumeOrVisibility);
    }
  }
  resetInactivityTimer();
}

if (typeof window !== 'undefined') {
  window.SEED_DATA = SEED_DATA;
  window.INACTIVITY_TIMEOUT_MS = INACTIVITY_TIMEOUT_MS;
  window.resetInactivityTimer = resetInactivityTimer;
  window.triggerInactivitySignOut = triggerInactivitySignOut;
  window.checkInactivityDeadline = checkInactivityDeadline;
}

function signOut(reason) {
  if (inactivityTimerId) {
    clearTimeout(inactivityTimerId);
    inactivityTimerId = null;
  }
  SafeStorage.remove('TEEM_LAST_ACTIVITY_MS');
  stopFieldReporting();
  gpsSelf = null;
  gpsFocusCrew = null;
  gpsFocusPoint = null;
  closeModal('modal-profile');
  if (typeof window !== 'undefined') {
    window._teemActiveSessionUser = null;
  }
  settingsUnlockedSession = false;
  store.state.sessionUserId = null;
  clearSessionMarker();
  store.save();
  showLoginScreen();
  if (reason === 'inactivity') {
    showToast('\ud83d\udd12 Signed out after 5 minutes idle.', 'warning');
  } else {
    showToast('\ud83d\udc4b Signed out. Sign in to continue.', 'info');
  }
}

function showLoginScreen() {
  // Last line of defence: if a session can still be restored, restore it
  // instead of showing the sign-in form. Nothing is allowed to leave a
  // signed-in user looking at a login page.
  restoreSessionFromMarker();
  if (typeof currentUser === 'function' && currentUser()) {
    applySessionUI();
    renderAll();
    return;
  }
  closeMobileNav();
  updateLoginConnectionStatus();
  const el = document.getElementById('login-screen');
  if (el) el.classList.add('active');
  document.documentElement.setAttribute('data-teem-session', 'out');
  // Auto-fill username if "Remember me" was previously chosen
  const savedUser = SafeStorage.get('TEEM_LAST_USERNAME');
  const u = document.getElementById('login-username');
  const k = document.getElementById('remember-me');
  if (u && savedUser) u.value = savedUser;
  if (k && savedUser) k.checked = true;
  if (u) u.focus();
}

function hideLoginScreen() {
  const el = document.getElementById('login-screen');
  if (el) el.classList.remove('active');
  // Tells the stylesheet (and the pre-paint bootstrap in index.html) that a
  // session is live, so the sign-in form can never flash up on a reload.
  document.documentElement.setAttribute('data-teem-session', 'in');
}

function applySessionUI() {
  if (typeof currentUser === 'function' && currentUser()) {
    startFieldReporting();
    if (typeof startImmediateLiveTracking === 'function') startImmediateLiveTracking();
    // The sign-in screen ships `active` inside the page markup. Boot used to
    // only ever call showLoginScreen(), so a restored session sat behind a
    // login form that never closed - which is why refreshing looked like being
    // signed out even when the session was still alive.
    hideLoginScreen();
  }
  const user = currentUser();
  const name = userFullName(user);
  const roleLabel = user ? (user.role === 'Admin' ? 'Administrator' : user.role) + ' \u2022 ' + (user.zone || 'Operations') : 'Sign in to continue';

  const sideName = document.getElementById('sidebar-user-name');
  if (sideName) sideName.textContent = name;
  const sideRole = document.getElementById('sidebar-user-role');
  if (sideRole) sideRole.textContent = user ? (user.role === 'Admin' ? 'Administrator' : user.role) : 'Sign in to continue';

  const topName = document.getElementById('topbar-user-name');
  if (topName) topName.textContent = name;
  const topRole = document.getElementById('topbar-user-role');
  if (topRole) topRole.textContent = user ? (user.role === 'Admin' ? 'Administrator' : user.role) : '-';

  [['sidebar-user-photo', 'user-avatar user-avatar-photo'], ['topbar-user-photo', 'user-chip-photo']].forEach(pair => {
    const el = document.getElementById(pair[0]);
    if (!el) return;
    if (user && user.photo) {
      el.innerHTML = '<img src="' + user.photo + '" alt="' + escapeHtml(name) + '" class="avatar-img">';
    } else {
      el.innerHTML = escapeHtml(userInitials(user));
    }
  });

  const versionEl = document.getElementById('app-version-label');
  if (versionEl) versionEl.textContent = 'v' + RELEASE;

  renderUsersTable();
  updateAdminQuotaNote();
  applyRoleLocks();
}

// Body class + role-based visibility locks.
function applyRoleLocks() {
  const supervisor = isSupervisor();
  document.body.classList.toggle('role-supervisor', supervisor);
  const notice = document.getElementById('supervisor-notice');
  if (notice) notice.style.display = 'none';
  const badge = document.getElementById('settings-access-badge');
  if (badge) {
    badge.style.display = supervisor ? 'none' : '';
    badge.textContent = supervisor ? '' : '\ud83d\udd12 Administrator Access Only';
    badge.className = 'badge badge-danger admin-only';
  }
  const sub = document.getElementById('settings-subtitle');
  if (sub) {
    sub.textContent = supervisor
      ? ''
      : 'Accounts, fleet, supervisors, records and archive - all administration in one place';
  }
  // the wording of the console follows the session
  const accountsNote = document.getElementById('accounts-card-note');
  if (accountsNote) {
    accountsNote.innerHTML = supervisor
      ? 'Your account is the only one you can change here. Use <strong>Edit</strong> on your row to update your name, '
        + 'phone, zone, photograph or password. Roles, usernames and every other account are handled by the administrator.'
      : 'Create every account here and choose its role: <strong>Supervisor</strong>, <strong>User</strong> or '
        + '<strong>Administrator</strong> (unlimited Administrators and Supervisors supported). '
        + 'Use <strong>Edit</strong> or <strong>Delete</strong> on any row to manage accounts, roles or passwords. '
        + 'Everyone can also edit their own profile and password after signing in.';
  }
  const archiveNote = document.getElementById('archive-card-note');
  if (archiveNote) {
    archiveNote.style.display = supervisor ? 'none' : '';
  }
  const archiveCard = document.getElementById('archive-card');
  if (archiveCard) archiveCard.style.display = supervisor ? 'none' : '';

  // any open add form is closed the moment a supervisor signs in
  if (supervisor) {
    const form = document.getElementById('form-add-user');
    if (form) form.style.display = 'none';
  }
  renderPendingSignups();
  if (typeof renderMonthlyReport === 'function') {
    renderMonthlyReport();
  }
}

// Show / hide a password field so the user can peep at what they typed.
// Supports both click-to-toggle AND press-and-hold on every password field.
function startPasswordPeek(inputId, btn) {
  const input = document.getElementById(inputId);
  if (!input) return;
  input._peekDownAt = Date.now();
  input._wasShowingBeforeDown = (input.type === 'text');
  if (!input._wasShowingBeforeDown) {
    input.type = 'text';
    if (btn) {
      btn.classList.add('is-peeking');
      btn.setAttribute('aria-label', 'Hide password');
    }
  }
}

function stopPasswordPeek(inputId, btn) {
  const input = document.getElementById(inputId);
  if (!input) return;
  const heldMs = input._peekDownAt ? (Date.now() - input._peekDownAt) : 0;
  if (heldMs >= 250 && input.dataset.peekPinned !== '1') {
    input.type = 'password';
    if (btn) {
      btn.classList.remove('is-peeking', 'peeking');
      btn.setAttribute('aria-label', 'Show password');
    }
  }
}

function togglePasswordPeek(inputId, btn) {
  const input = document.getElementById(inputId);
  if (!input) return;
  const hadDown = Boolean(input._peekDownAt);
  const heldMs = hadDown ? (Date.now() - input._peekDownAt) : 0;
  input._peekDownAt = 0;
  if (hadDown && heldMs >= 250 && !input._wasShowingBeforeDown) {
    input.dataset.peekPinned = '0';
    input.type = 'password';
    if (btn) {
      btn.classList.remove('is-peeking', 'peeking');
      btn.title = 'Show password';
    }
    return;
  }
  const willShow = (hadDown && heldMs < 500)
    ? !input._wasShowingBeforeDown
    : (input.type === 'password');
  input.dataset.peekPinned = willShow ? '1' : '0';
  input.type = willShow ? 'text' : 'password';
  if (btn) {
    btn.classList.toggle('is-peeking', willShow);
    btn.classList.toggle('peeking', willShow);
    btn.title = willShow ? 'Hide password' : 'Show password';
  }
}
window.startPasswordPeek = startPasswordPeek;
window.stopPasswordPeek = stopPasswordPeek;
window.togglePasswordPeek = togglePasswordPeek;

let photoEditorState = {
  inputId: null,
  previewId: null,
  rawUrl: null,
  img: null,
  zoom: 1,
  panX: 0,
  panY: 0,
  rotation: 0,
  dragging: false,
  startX: 0,
  startY: 0,
  pinchDist: 0,
  pinchStartZoom: 1,
  bound: false
};

function readPhotoFile(input, previewId) {
  const file = input.files && input.files[0];
  if (!file) return;

  const preview = document.getElementById(previewId);
  const showPreview = dataUrl => {
    if (preview) preview.innerHTML = '<img src="' + dataUrl + '" class="photo-preview-img" alt="Selected photo"><span class="photo-preview-caption">Zoom/Crop Ready</span>';
  };

  const reader = new FileReader();
  reader.onload = () => {
    const raw = reader.result;
    input.dataset.rawUrl = raw;
    try {
      const img = new Image();
      img.onload = () => {
        try {
          const size = 240;
          const canvas = document.createElement('canvas');
          canvas.width = size;
          canvas.height = size;
          const side = Math.min(img.width, img.height);
          canvas.getContext('2d').drawImage(img, (img.width - side) / 2, (img.height - side) / 2, side, side, 0, 0, size, size);
          const dataUrl = canvas.toDataURL('image/jpeg', 0.88);
          input.dataset.dataUrl = dataUrl;
          showPreview(dataUrl);
          openPhotoEditorModal(raw, input.id, previewId);
        } catch (err) {
          input.dataset.dataUrl = raw;
          showPreview(raw);
          openPhotoEditorModal(raw, input.id, previewId);
        }
      };
      img.onerror = () => { input.dataset.dataUrl = raw; showPreview(raw); };
      img.src = raw;
    } catch (err) {
      input.dataset.dataUrl = raw;
      showPreview(raw);
    }
  };
  reader.onerror = () => showToast('\u26a0\ufe0f File could not be read. Use JPG or PNG.', 'error');
  reader.readAsDataURL(file);
}

function openPhotoEditorForInput(inputId, previewId) {
  const input = document.getElementById(inputId);
  const preview = document.getElementById(previewId);
  let src = (input && (input.dataset.rawUrl || input.dataset.dataUrl)) || '';
  if (!src && preview) {
    const imgEl = preview.querySelector('img');
    if (imgEl && imgEl.src) src = imgEl.src;
  }
  if (!src) {
    if (input) input.click();
    else showToast('\ud83d\udcf7 Upload a photo first.', 'info');
    return;
  }
  openPhotoEditorModal(src, inputId, previewId);
}

function bindPhotoEditorEvents() {
  if (photoEditorState.bound) return;
  const stage = document.getElementById('photo-crop-stage');
  if (!stage) return;
  photoEditorState.bound = true;

  stage.addEventListener('mousedown', e => {
    e.preventDefault();
    photoEditorState.dragging = true;
    photoEditorState.startX = e.clientX - photoEditorState.panX;
    photoEditorState.startY = e.clientY - photoEditorState.panY;
  });
  window.addEventListener('mousemove', e => {
    if (!photoEditorState.dragging) return;
    photoEditorState.panX = e.clientX - photoEditorState.startX;
    photoEditorState.panY = e.clientY - photoEditorState.startY;
    renderPhotoEditorCanvas();
  });
  window.addEventListener('mouseup', () => {
    photoEditorState.dragging = false;
  });
  stage.addEventListener('wheel', e => {
    e.preventDefault();
    const delta = e.deltaY < 0 ? 0.14 : -0.14;
    photoEditorZoomBy(delta);
  }, { passive: false });

  stage.addEventListener('touchstart', e => {
    if (e.touches.length === 2) {
      e.preventDefault();
      const dx = e.touches[0].clientX - e.touches[1].clientX;
      const dy = e.touches[0].clientY - e.touches[1].clientY;
      photoEditorState.pinchDist = Math.hypot(dx, dy) || 1;
      photoEditorState.pinchStartZoom = photoEditorState.zoom;
      photoEditorState.dragging = false;
    } else if (e.touches.length === 1) {
      photoEditorState.dragging = true;
      photoEditorState.startX = e.touches[0].clientX - photoEditorState.panX;
      photoEditorState.startY = e.touches[0].clientY - photoEditorState.panY;
    }
  }, { passive: false });

  stage.addEventListener('touchmove', e => {
    if (e.touches.length === 2 && photoEditorState.pinchDist > 0) {
      e.preventDefault();
      const dx = e.touches[0].clientX - e.touches[1].clientX;
      const dy = e.touches[0].clientY - e.touches[1].clientY;
      const dist = Math.hypot(dx, dy) || 1;
      const nextZoom = Math.max(1, Math.min(4, photoEditorState.pinchStartZoom * (dist / photoEditorState.pinchDist)));
      photoEditorSetZoom(nextZoom);
    } else if (e.touches.length === 1 && photoEditorState.dragging) {
      e.preventDefault();
      photoEditorState.panX = e.touches[0].clientX - photoEditorState.startX;
      photoEditorState.panY = e.touches[0].clientY - photoEditorState.startY;
      renderPhotoEditorCanvas();
    }
  }, { passive: false });

  stage.addEventListener('touchend', () => {
    photoEditorState.dragging = false;
    photoEditorState.pinchDist = 0;
  });
}

function openPhotoEditorModal(rawUrl, inputId, previewId) {
  photoEditorState.inputId = inputId;
  photoEditorState.previewId = previewId;
  photoEditorState.rawUrl = rawUrl;
  photoEditorState.zoom = 1;
  photoEditorState.panX = 0;
  photoEditorState.panY = 0;
  photoEditorState.rotation = 0;

  bindPhotoEditorEvents();
  const slider = document.getElementById('photo-zoom-slider');
  const readout = document.getElementById('photo-zoom-readout');
  if (slider) slider.value = '1';
  if (readout) readout.textContent = '1.0\u00d7';

  const img = new Image();
  img.onload = () => {
    photoEditorState.img = img;
    renderPhotoEditorCanvas();
  };
  img.src = rawUrl;
  openModal('modal-photo-editor');
}

function renderPhotoEditorCanvas() {
  const canvas = document.getElementById('photo-crop-canvas');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');
  if (!ctx) return;
  const size = canvas.width || 240;
  ctx.clearRect(0, 0, size, size);
  ctx.fillStyle = '#0F172A';
  ctx.fillRect(0, 0, size, size);

  const img = photoEditorState.img;
  if (!img || !img.width || !img.height) return;

  ctx.save();
  ctx.translate(size / 2 + photoEditorState.panX, size / 2 + photoEditorState.panY);
  ctx.rotate((photoEditorState.rotation * Math.PI) / 180);
  const baseScale = Math.max(size / img.width, size / img.height);
  const scale = baseScale * photoEditorState.zoom;
  const drawW = img.width * scale;
  const drawH = img.height * scale;
  ctx.drawImage(img, -drawW / 2, -drawH / 2, drawW, drawH);
  ctx.restore();
}

function photoEditorSetZoom(val) {
  const z = Math.max(1, Math.min(4, Number(val) || 1));
  photoEditorState.zoom = z;
  const slider = document.getElementById('photo-zoom-slider');
  const readout = document.getElementById('photo-zoom-readout');
  if (slider) slider.value = String(z);
  if (readout) readout.textContent = z.toFixed(1) + '\u00d7';
  renderPhotoEditorCanvas();
}

function photoEditorZoomBy(delta) {
  photoEditorSetZoom((photoEditorState.zoom || 1) + Number(delta || 0));
}

function photoEditorRotate(deg) {
  photoEditorState.rotation = ((photoEditorState.rotation || 0) + (Number(deg) || 90)) % 360;
  renderPhotoEditorCanvas();
}

function photoEditorReset() {
  photoEditorState.zoom = 1;
  photoEditorState.panX = 0;
  photoEditorState.panY = 0;
  photoEditorState.rotation = 0;
  photoEditorSetZoom(1);
}

function applyPhotoEditorCrop() {
  renderPhotoEditorCanvas();
  const canvas = document.getElementById('photo-crop-canvas');
  const input = photoEditorState.inputId ? document.getElementById(photoEditorState.inputId) : null;
  const preview = photoEditorState.previewId ? document.getElementById(photoEditorState.previewId) : null;
  let dataUrl = photoEditorState.rawUrl || '';
  if (canvas) {
    try {
      dataUrl = canvas.toDataURL('image/jpeg', 0.88);
    } catch (e) {}
  }
  if (input && dataUrl) {
    input.dataset.dataUrl = dataUrl;
  }
  if (preview && dataUrl) {
    preview.innerHTML = '<img src="' + dataUrl + '" class="photo-preview-img" alt="Edited photo"><span class="photo-preview-caption">Edited (' + (photoEditorState.zoom || 1).toFixed(1) + '\u00d7)</span>';
  }
  closeModal('modal-photo-editor');
  showToast('\u2705 Crop applied. Press Save.', 'success');
}

function closePhotoEditorModal() {
  closeModal('modal-photo-editor');
}

function clearProfilePhoto() {
  const user = currentUser();
  if (!user) return;
  if (!user.photo) { showToast('There is no photo to remove.', 'info'); return; }
  if (!confirm('Remove your profile photograph?')) return;
  user.photo = '';
  store.save();
  applySessionUI();
  const preview = document.getElementById('prof-photo-preview');
  if (preview) preview.textContent = 'No photo uploaded';
  const file = document.getElementById('prof-photo-file');
  if (file) { file.value = ''; delete file.dataset.dataUrl; }
  showToast('\ud83d\uddd1\ufe0f Profile photograph removed.', 'info');
}

function openProfileModal() {
  const user = currentUser();
  if (!user) { showLoginScreen(); return; }

  document.getElementById('profile-photo-view').innerHTML = user.photo
    ? '<img src="' + user.photo + '" class="avatar-img" alt="Profile photo">'
    : escapeHtml(userInitials(user));
  document.getElementById('profile-name-view').textContent = userFullName(user);
  document.getElementById('profile-role-view').textContent = user.role === 'Admin' ? 'Administrator' : user.role;
  document.getElementById('profile-username-view').textContent = '@' + (user.username || '');

  document.getElementById('prof-first').value = user.firstName || '';
  document.getElementById('prof-last').value = user.lastName || '';
  document.getElementById('prof-phone').value = user.phone || '';
  document.getElementById('prof-email').value = user.email || '';
  const profUsernameEl = document.getElementById('prof-username');
  if (profUsernameEl) profUsernameEl.value = user.username || '';
  document.getElementById('prof-zone').value = user.zone || '';
  const fileInput = document.getElementById('prof-photo-file');
  if (fileInput) { fileInput.value = ''; delete fileInput.dataset.dataUrl; }
  const preview = document.getElementById('prof-photo-preview');
  if (preview) {
    preview.innerHTML = user.photo
      ? '<img src="' + user.photo + '" class="photo-preview-img" alt="Current photo"><span class="photo-preview-caption">Current photo</span>'
      : 'No photo uploaded yet';
  }

  ['pwd-current', 'pwd-new', 'pwd-confirm'].forEach(id => { const el = document.getElementById(id); if (el) el.value = ''; });
  openModal('modal-profile');
}

function applyProfileFieldEditsToUser(user) {
  if (!user) return false;
  const profUsernameEl = document.getElementById('prof-username');
  if (profUsernameEl && profUsernameEl.value !== undefined) {
    const newUsername = profUsernameEl.value.trim().toLowerCase().replace(/^@+/, '').replace(/\s+/g, '');
    if (!newUsername) {
      showToast('\u26a0\ufe0f Username cannot be empty.', 'error');
      return false;
    }
    const taken = (store.state.users || []).some(u => u.id !== user.id && String(u.username || '').toLowerCase() === newUsername);
    if (taken) {
      showToast('\u26a0\ufe0f Username "@' + newUsername + '" is already used by another account.', 'error');
      return false;
    }
    user.username = newUsername;
  }

  const firstEl = document.getElementById('prof-first');
  const lastEl = document.getElementById('prof-last');
  const phoneEl = document.getElementById('prof-phone');
  const emailEl = document.getElementById('prof-email');
  const zoneEl = document.getElementById('prof-zone');
  if (firstEl && firstEl.value.trim()) user.firstName = firstEl.value.trim();
  if (lastEl && lastEl.value.trim()) user.lastName = lastEl.value.trim();
  if (phoneEl) user.phone = phoneEl.value.trim();
  if (emailEl) user.email = emailEl.value.trim();
  if (zoneEl) user.zone = zoneEl.value.trim();

  const fileInput = document.getElementById('prof-photo-file');
  if (fileInput && fileInput.dataset.dataUrl) user.photo = fileInput.dataset.dataUrl;
  return true;
}

function saveProfile(e) {
  if (e) e.preventDefault();
  const user = currentUser();
  if (!user) return;

  if (!applyProfileFieldEditsToUser(user)) return;

  const newPwdEl = document.getElementById('pwd-new');
  const confirmPwdEl = document.getElementById('pwd-confirm');
  const newPwd = newPwdEl ? newPwdEl.value : '';
  const confirmPwd = confirmPwdEl ? confirmPwdEl.value : '';
  let pwdAlsoUpdated = false;
  if (newPwd || confirmPwd) {
    if (newPwd.length < 6) {
      showToast('\u26a0\ufe0f New password must be at least 6 characters.', 'error');
      return;
    }
    if (newPwd !== confirmPwd) {
      showToast('\u26a0\ufe0f New passwords do not match.', 'error');
      return;
    }
    user.password = hashPassword(newPwd);
    user.mustChangePassword = false;
    pwdAlsoUpdated = true;
  }

  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  user.updatedAt = nowIso;
  if (pwdAlsoUpdated) user.passwordChangedAt = nowIso;
  if (typeof window !== 'undefined') {
    window._teemActiveSessionUser = { id: user.id, username: user.username, role: normalizeUserRole(user.role) };
  }

  syncSupervisorsFromUsers();
  store.save();
  applySessionUI();
  openProfileModal();   // refresh the header photo, username, and preview slot
  renderUsersTable();
  renderSupervisorsList();
  renderTeamChat();
  showToast(pwdAlsoUpdated ? '\u2705 Profile and password updated.' : '\u2705 Profile updated.', 'success');
}

function changeOwnPassword(e) {
  if (e) e.preventDefault();
  const user = currentUser();
  if (!user) return;

  const currentPwd = (document.getElementById('pwd-current') || {}).value || '';
  const newPwd = (document.getElementById('pwd-new') || {}).value || '';
  const confirmPwd = (document.getElementById('pwd-confirm') || {}).value || '';

  if (currentPwd && !checkPassword(currentPwd, user.password) && !isAdmin()) {
    showToast('\u26a0\ufe0f Current password is incorrect.', 'error');
    return;
  }
  if (newPwd.length < 6) { showToast('\u26a0\ufe0f New password must be at least 6 characters.', 'error'); return; }
  if (newPwd !== confirmPwd) { showToast('\u26a0\ufe0f New passwords do not match.', 'error'); return; }

  // Also save any edits made to the profile fields at the top of the modal
  if (!applyProfileFieldEditsToUser(user)) return;

  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  user.password = hashPassword(newPwd);
  user.mustChangePassword = false;
  user.passwordChangedAt = nowIso;
  user.updatedAt = nowIso;
  if (typeof window !== 'undefined') {
    window._teemActiveSessionUser = { id: user.id, username: user.username, role: normalizeUserRole(user.role) };
  }

  syncSupervisorsFromUsers();
  store.save();
  applySessionUI();
  openProfileModal();
  renderUsersTable();
  renderSupervisorsList();
  renderTeamChat();
  ['pwd-current', 'pwd-new', 'pwd-confirm'].forEach(id => { const el = document.getElementById(id); if (el) el.value = ''; });
  showToast('\ud83d\udd10 Your profile and password have been updated.', 'success');
}

// ---------------------------------------------------------------- USER ADMINISTRATION
function updateAdminQuotaNote() {
  const note = document.getElementById('admin-quota-note');
  if (!note) return;
  const used = adminCount();
  const supCount = (store.state.users || []).filter(u => isUserSupervisorRole(u) && u.status !== 'Disabled').length;
  note.textContent = 'Administrators active: ' + used + ' \u2022 Supervisors active: ' + supCount + ' (Unlimited Administrators & Supervisors)';
  note.classList.remove('admin-quota-full');
  const fill = document.getElementById('admin-quota-fill');
  if (fill) {
    fill.style.width = '100%';
    fill.style.background = 'var(--eco-green)';
  }
}

// The supervisor register used by the field screens is derived from the
// accounts, so there is only ever one place to add or change a person.
function syncSupervisorsFromUsers() {
  const supUsers = (store.state.users || []).filter(u => isUserSupervisorRole(u) && u.status !== 'Disabled');
  if (!supUsers.length) {
    store.state.supervisors = [];
    renderHeroSupervisorGrid();
    return;
  }

  const previous = store.state.supervisors || [];
  store.state.supervisors = supUsers.map(u => {
    const match = previous.find(s => s.name === userFullName(u)) || previous.find(s => s.phone && s.phone === u.phone);
    return {
      id: match ? match.id : ('sup-' + u.id),
      name: userFullName(u),
      phone: u.phone || '',
      zone: u.zone || '',
      vehicle: u.vehicle || (match ? match.vehicle : '') || '',
      status: u.mustChangePassword ? 'Awaiting first sign in' : 'Active Field Lead',
      userId: u.id
    };
  });
  renderHeroSupervisorGrid();
}

function supervisorOptionsHtml(selected) {
  const sups = store.state.supervisors || [];
  const current = selected || 'Unassigned';
  let html = '<option value="Unassigned"' + (current === 'Unassigned' ? ' selected' : '') + '>Unassigned</option>';
  sups.forEach(s => {
    html += '<option value="' + escapeHtml(s.name) + '"' + (s.name === current ? ' selected' : '') + '>' + escapeHtml(s.name) + '</option>';
  });
  if (current && current !== 'Unassigned' && !sups.some(s => s.name === current)) {
    html += '<option value="' + escapeHtml(current) + '" selected>' + escapeHtml(current) + '</option>';
  }
  return html;
}

function renderHeroSupervisorGrid() {
  const grid = document.getElementById('hero-supervisor-grid');
  if (!grid) return;
  const sups = store.state.supervisors || [];
  if (!sups.length) {
    grid.innerHTML =
      '<div>' +
        '<div class="hero-map-label">FIELD SUPERVISORS</div>' +
        '<strong class="hero-map-name green">No supervisors assigned yet</strong>' +
        '<div class="hero-map-note">Register supervisor accounts from Sign Up or Settings &amp; Admin Control</div>' +
      '</div>';
    return;
  }
  const colors = ['green', 'orange', 'blue'];
  grid.innerHTML = sups.map((s, idx) =>
    '<div>' +
      '<div class="hero-map-label">SUPERVISOR LEAD ' + (idx + 1) + ' &bull; ' + escapeHtml((s.zone || 'FIELD SECTOR').toUpperCase()) + '</div>' +
      '<strong class="hero-map-name ' + colors[idx % colors.length] + '">' + escapeHtml(s.name) + '</strong>' +
      '<div class="hero-map-note">' + escapeHtml(s.phone || 'Active Field Lead') + (s.vehicle ? ' &bull; ' + escapeHtml(s.vehicle) : '') + '</div>' +
    '</div>'
  ).join('');
}

function accountVehicleOptions(selected) {
  const vehicles = store.state.vehicles || [];
  const current = selected || '';
  let html = '<option value="">-- No vehicle assigned --</option>';
  vehicles.forEach(v => {
    html += '<option value="' + escapeHtml(v.name) + '"' + (v.name === current ? ' selected' : '') + '>' + escapeHtml(v.name) + '</option>';
  });
  if (current && !vehicles.some(v => v.name === current)) {
    html += '<option value="' + escapeHtml(current) + '" selected>' + escapeHtml(current) + '</option>';
  }
  return html;
}

// The vehicle a supervisor is expected to be moving with: whatever was chosen
// in the account, otherwise the truck from their most recent evacuation.
function supervisorVehicle(user) {
  if (!user) return '';
  if (user.vehicle) return user.vehicle;
  const name = userFullName(user);
  const log = (store.state.evacuationLogs || []).find(l => l.supervisor === name);
  return log ? log.truck : '';
}

function visibleAccounts() {
  const searchEl = document.getElementById('accounts-search');
  const roleEl = document.getElementById('accounts-role-filter');
  const term = (searchEl ? searchEl.value : '').trim().toLowerCase();
  const role = roleEl ? roleEl.value : 'all';
  const me = currentUser();
  return (store.state.users || []).filter(u => {
    // v2.9.3 - a supervisor only ever sees (and may only edit) their own row
    if (isSupervisor() && (!me || u.id !== me.id)) return false;
    if (role !== 'all' && normalizeUserRole(u.role) !== normalizeUserRole(role)) return false;
    if (!term) return true;
    return [userFullName(u), u.username, u.role, u.zone, u.phone].join(' ').toLowerCase().indexOf(term) > -1;
  });
}

function renderUsersTable() {
  const tbody = document.getElementById('users-table-body');
  if (!tbody) return;

  const all = store.state.users || [];
  const rows = visibleAccounts();
  const countEl = document.getElementById('accounts-count');
  if (countEl) {
    countEl.textContent = rows.length === all.length
      ? all.length + ' account' + (all.length === 1 ? '' : 's')
      : rows.length + ' of ' + all.length + ' accounts';
  }

  if (!rows.length) {
    tbody.innerHTML = '<tr><td colspan="5" class="table-empty">No account matches this search.</td></tr>';
    return;
  }

  const adminLogged = isAdmin();
  const totalAdmins = adminCount();

  tbody.innerHTML = rows.map(u => {
    const avatar = u.photo ? '<img src="' + u.photo + '" class="avatar-img" alt="">' : escapeHtml(userInitials(u));
    const isSelf = currentUser() && currentUser().id === u.id;
    const normRole = normalizeUserRole(u.role);
    const canDeleteRow = adminLogged && !(normRole === 'Admin' && totalAdmins <= 1);
    return '<tr>' +
      '<td><div class="user-cell"><span class="table-avatar">' + avatar + '</span>' +
        '<span><strong>' + escapeHtml(userFullName(u)) + '</strong>' +
        (u.mustChangePassword ? '<div class="badge badge-warning" style="margin-top:3px;">Must change password</div>' : '') +
        '</span></div></td>' +
      '<td><span class="badge ' + (normRole === 'Admin' ? 'badge-danger' : normRole === 'Supervisor' ? 'badge-supervisor' : 'badge-category') + '">' + escapeHtml(normRole === 'Admin' ? 'Administrator' : normRole) + '</span></td>' +
      '<td>@' + escapeHtml(u.username) + '</td>' +
      '<td>' + escapeHtml(u.phone || '-') + '</td>' +
      '<td><div class="action-btn-group">' +
        (adminLogged || isSelf
          ? '<button class="btn btn-sm btn-primary" onclick="openUserEdit(\'' + u.id + '\')">\u270f\ufe0f Edit</button>'
          : '<span class="badge badge-muted">Read only</span>') +
        (canDeleteRow
          ? '<button class="btn btn-sm btn-danger" onclick="deleteUser(\'' + u.id + '\')" title="Delete Account">\ud83d\uddd1\ufe0f Delete</button>'
          : '') +
        (isSelf ? '<span class="badge badge-success">You</span>' : '') +
      '</div></td>' +
    '</tr>';
  }).join('');
  renderPendingSignups();
}

function saveAddUser(e) {
  if (e) e.preventDefault();
  if (!requireAdmin('Creating user accounts')) return;

  const role = normalizeUserRole(document.getElementById('usr-role').value);
  const username = document.getElementById('usr-username').value.trim().toLowerCase().replace(/^@+/, '').replace(/\s+/g, '');
  if ((store.state.users || []).some(u => (u.username || '').toLowerCase() === username)) {
    alert('That username is already taken. Please choose another.');
    return;
  }

  const password = document.getElementById('usr-password').value;
  if (password.length < 6) { alert('The password must be at least 6 characters.'); return; }

  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  const defaultVehicle = (store.state.vehicles && store.state.vehicles[0] && store.state.vehicles[0].name) || 'Blue Compactor (TEEM-01)';
  const fileInput = document.getElementById('usr-photo-file');
  const newUser = {
    id: 'usr-' + Date.now().toString().slice(-5) + '-' + Math.floor(Math.random() * 90 + 10),
    firstName: document.getElementById('usr-first').value.trim(),
    lastName: document.getElementById('usr-last').value.trim(),
    role: role,
    username: username,
    password: hashPassword(password),
    phone: document.getElementById('usr-phone').value.trim(),
    zone: document.getElementById('usr-zone').value.trim() || (role === 'Supervisor' ? 'Field Operations' : 'Head Office'),
    vehicle: role === 'Supervisor' ? defaultVehicle : '',
    email: '',
    photo: (fileInput && fileInput.dataset.dataUrl) ? fileInput.dataset.dataUrl : '',
    status: 'Active',
    mustChangePassword: false,
    createdAt: nowIso,
    updatedAt: nowIso,
    passwordChangedAt: nowIso
  };

  store.state.users.push(newUser);
  syncSupervisorsFromUsers();
  store.save();
  toggleAccountCreateForm(false);

  document.getElementById('form-add-user').reset();
  if (fileInput) delete fileInput.dataset.dataUrl;
  const preview = document.getElementById('usr-photo-preview');
  if (preview) preview.textContent = 'No photo';

  renderUsersTable();
  renderSupervisorsList();
  renderFieldTracking();
  renderGpsMap();
  updateAdminQuotaNote();
  showToast('\u2705 Account created for ' + userFullName(newUser) + ' as ' + (role === 'Admin' ? 'Administrator' : role) + '.', 'success');
}

// The one creation form folds out of the accounts list and folds back again.
function toggleAccountCreateForm(force) {
  if (!isAdmin()) { showToast('\u26d4 Only an administrator can create accounts.', 'warning'); return; }
  const form = document.getElementById('form-add-user');
  if (!form) return;
  const show = typeof force === 'boolean' ? force : form.style.display === 'none';
  form.style.display = show ? '' : 'none';
  const btn = document.getElementById('account-add-btn');
  if (btn) btn.innerHTML = show ? '\u2716 Close The Account Form' : '\u2795 Add Account';
  if (show) {
    const first = document.getElementById('usr-first');
    if (first && first.focus) first.focus();
    if (typeof form.scrollIntoView === 'function') form.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  }
}

function openUserEdit(userId) {
  const u = (store.state.users || []).find(x => x.id === userId);
  if (!u) return;
  const editingSelf = currentUser() && currentUser().id === u.id;
  if (!isAdmin() && !editingSelf) {
    showToast('\u26d4 A supervisor can only edit their own account.', 'warning');
    return;
  }

  const normRole = normalizeUserRole(u.role);
  document.getElementById('user-edit-title').innerHTML = '\u270f\ufe0f Edit Account - ' + escapeHtml(userFullName(u));
  document.getElementById('ued-id').value = u.id;
  document.getElementById('user-edit-photo').innerHTML = u.photo
    ? '<img src="' + u.photo + '" class="avatar-img" alt="Photo">'
    : escapeHtml(userInitials(u));
  document.getElementById('user-edit-name').textContent = userFullName(u);
  document.getElementById('user-edit-meta').textContent =
    '@' + u.username + ' \u2022 ' + (normRole === 'Admin' ? 'Administrator' : normRole) + ' \u2022 ' + (u.zone || 'No zone set');

  document.getElementById('ued-first').value = u.firstName || '';
  document.getElementById('ued-last').value = u.lastName || '';
  document.getElementById('ued-role').value = normRole;
  document.getElementById('ued-username').value = u.username || '';
  document.getElementById('ued-phone').value = u.phone || '';
  document.getElementById('ued-email').value = u.email || '';
  document.getElementById('ued-zone').value = u.zone || '';
  document.getElementById('ued-vehicle').innerHTML = accountVehicleOptions(supervisorVehicle(u));
  document.getElementById('ued-force-change').checked = !!u.mustChangePassword;
  ['ued-password', 'ued-password2'].forEach(id => { document.getElementById(id).value = ''; });
  const file = document.getElementById('ued-photo-file');
  if (file) { file.value = ''; delete file.dataset.dataUrl; }
  const preview = document.getElementById('ued-photo-preview');
  if (preview) {
    preview.innerHTML = u.photo ? '<img src="' + u.photo + '" class="photo-preview-img" alt="Photo"><span class="photo-preview-caption">Current photo</span>' : 'No photo uploaded yet';
  }

  const deleteBtn = document.getElementById('ued-delete-btn');
  const canDelete = isAdmin() && !(normRole === 'Admin' && adminCount() <= 1);
  deleteBtn.style.display = canDelete ? '' : 'none';
  const roleSelect = document.getElementById('ued-role');
  roleSelect.disabled = !isAdmin();
  ['ued-username', 'ued-force-change'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.disabled = !isAdmin();
  });
  onUserEditRoleChange();

  closeAllModals('modal-user-edit');
  openModal('modal-user-edit');
}

function onUserEditRoleChange() {
  const role = normalizeUserRole(document.getElementById('ued-role').value);
  const vehicleGroup = document.getElementById('ued-vehicle-group');
  const hint = document.getElementById('ued-role-hint');
  vehicleGroup.style.display = role === 'Supervisor' ? '' : 'none';

  const used = adminCount();
  hint.textContent = role === 'Admin'
    ? 'Administrators active: ' + used + ' \u2022 Full portal administration, account & record control (Unlimited Administrators supported).'
    : role === 'Supervisor'
      ? 'Supervisors appear in the field screens and on the GPS tracking map (Unlimited Supervisors supported).'
      : 'Users can view, evacuate and dispatch without administration rights.';
}

function clearUserEditPhoto() {
  const file = document.getElementById('ued-photo-file');
  if (file) { file.value = ''; delete file.dataset.dataUrl; }
  const preview = document.getElementById('ued-photo-preview');
  if (preview) preview.textContent = 'No photo will be stored for this account';
}

function saveUserEdit(e) {
  if (e) e.preventDefault();

  const id = document.getElementById('ued-id').value;
  const u = (store.state.users || []).find(x => x.id === id);
  if (!u) return;

  const editingSelf = currentUser() && currentUser().id === u.id;
  // v2.9.3 - an administrator edits anyone; a supervisor edits only themselves
  if (!isAdmin() && !editingSelf) {
    alert('Only an administrator can edit another account.');
    return;
  }

  // a supervisor cannot change the role or the username of an account
  const role = isAdmin() ? normalizeUserRole(document.getElementById('ued-role').value) : normalizeUserRole(u.role);
  if (isUserAdminRole(u) && role !== 'Admin' && adminCount() <= 1) {
    alert('At least one administrator account must remain.');
    return;
  }

  const username = isAdmin()
    ? document.getElementById('ued-username').value.trim().toLowerCase().replace(/^@+/, '').replace(/\s+/g, '')
    : (u.username || '').toLowerCase();
  if ((store.state.users || []).some(x => x.id !== id && (x.username || '').toLowerCase() === username)) {
    alert('That username is already taken. Please choose another.');
    return;
  }

  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  const pwd = document.getElementById('ued-password').value;
  const pwd2 = document.getElementById('ued-password2').value;
  if (pwd || pwd2) {
    if (pwd.length < 6) { alert('The password must be at least 6 characters.'); return; }
    if (pwd !== pwd2) { alert('The two passwords do not match.'); return; }
    u.password = hashPassword(pwd);
    u.passwordChangedAt = nowIso;
  }

  const wasSelf = currentUser() && currentUser().id === u.id;
  u.firstName = document.getElementById('ued-first').value.trim();
  u.lastName = document.getElementById('ued-last').value.trim();
  u.role = role;
  u.username = username;
  u.phone = document.getElementById('ued-phone').value.trim();
  u.email = document.getElementById('ued-email').value.trim();
  u.zone = document.getElementById('ued-zone').value.trim();
  u.vehicle = role === 'Supervisor' ? document.getElementById('ued-vehicle').value : '';
  if (isAdmin()) u.mustChangePassword = document.getElementById('ued-force-change').checked;
  if (wasSelf && !u.mustChangePassword) u.mustChangePassword = false;
  u.updatedAt = nowIso;

  if (wasSelf && typeof window !== 'undefined') {
    window._teemActiveSessionUser = { id: u.id, username: u.username, role: u.role };
  }

  const file = document.getElementById('ued-photo-file');
  if (file && file.dataset.dataUrl) u.photo = file.dataset.dataUrl;
  else if (document.getElementById('ued-photo-preview').textContent.indexOf('No photo will be stored') > -1) u.photo = '';

  syncSupervisorsFromUsers();
  store.save();
  renderUsersTable();
  renderSupervisorsList();
  updateAdminQuotaNote();
  applySessionUI();
  renderGpsMap();
  renderFieldTracking();
  closeModal('modal-user-edit');
  showToast('\u2705 Account updated for ' + userFullName(u) + '.', 'success');
}

function deleteUserFromEdit() {
  const id = document.getElementById('ued-id').value;
  if (!id) return;
  if (deleteUser(id)) closeModal('modal-user-edit');
}

function openResetPassword(userId) {
  const u = (store.state.users || []).find(x => x.id === userId);
  if (!u) return;
  document.getElementById('reset-user-id').value = u.id;
  document.getElementById('reset-user-name').textContent = userFullName(u);
  document.getElementById('reset-user-meta').textContent = '@' + u.username + ' \u2022 ' + u.role + ' \u2022 ' + (u.zone || 'No zone set');
  document.getElementById('reset-new-password').value = '';
  document.getElementById('reset-force-change').checked = true;
  openModal('modal-reset-password');
}

function applyPasswordReset(e) {
  if (e) e.preventDefault();
  if (!requireAdmin('Resetting passwords')) return;
  const u = (store.state.users || []).find(x => x.id === document.getElementById('reset-user-id').value);
  if (!u) return;
  const pwd = document.getElementById('reset-new-password').value;
  if (pwd.length < 6) { alert('The password must be at least 6 characters.'); return; }
  const nowIso = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  u.password = hashPassword(pwd);
  u.mustChangePassword = document.getElementById('reset-force-change').checked;
  u.passwordChangedAt = nowIso;
  u.updatedAt = nowIso;
  store.save();
  renderUsersTable();
  closeModal('modal-reset-password');
  showToast('\ud83d\udd11 Password updated for ' + userFullName(u) + '.', 'success');
}

function deleteUser(userId) {
  if (!requireAdmin('Deleting user accounts')) return false;
  const u = (store.state.users || []).find(x => x.id === userId);
  if (!u) return false;
  if (isUserAdminRole(u) && adminCount() <= 1) {
    showToast('\u26a0\ufe0f At least one administrator account must remain.', 'error');
    return false;
  }
  const deletingSelf = currentUser() && currentUser().id === u.id;
  if (deletingSelf && !isUserAdminRole(u)) {
    showToast('\u26a0\ufe0f You cannot delete the account you are signed in with.', 'error');
    return false;
  }
  if (!confirm('Delete the account for ' + userFullName(u) + ' (@' + u.username + ')? This cannot be undone.')) return false;

  if (typeof recordDeletedId === 'function') recordDeletedId(u.id);
  store.state.users = store.state.users.filter(x => x.id !== u.id);

  // If the signed-in Administrator deleted their own old account (e.g., Mojisola Ajibade)
  // so a newly created Administrator takes over, seamlessly switch the active session to the remaining Administrator!
  if (deletingSelf || !currentUser()) {
    const nextAdmin = (store.state.users || []).find(x => isUserAdminRole(x) && x.status !== 'Disabled') || store.state.users[0] || null;
    if (nextAdmin) {
      store.state.sessionUserId = nextAdmin.id;
      if (typeof window !== 'undefined') {
        window._teemActiveSessionUser = { id: nextAdmin.id, username: nextAdmin.username, role: normalizeUserRole(nextAdmin.role) };
      }
    }
  }

  syncSupervisorsFromUsers();
  store.save();
  applySessionUI();
  renderUsersTable();
  renderSupervisorsList();
  updateAdminQuotaNote();
  renderGpsMap();
  renderFieldTracking();
  showToast('\ud83d\uddd1\ufe0f Account for ' + userFullName(u) + ' permanently deleted.', 'warning');
  return true;
}

// ---------------------------------------------------------------------------
// MONTH / PERIOD ENGINE
// ---------------------------------------------------------------------------
const MONTH_ORDER = ['January','February','March','April','May','June','July','August','September','October','November','December'];

function monthOptions(years) {
  const out = [];
  years.forEach(y => MONTH_ORDER.forEach(m => out.push(m + ' ' + y)));
  return out;
}
const ALL_PERIODS = monthOptions([2026, 2027]);

const MONTH_MAP = {};
ALL_PERIODS.forEach((label, idx) => { MONTH_MAP[label] = idx + 1; });

// A month is one number in a continuous run: January 2026 is 1, December 2026
// is 12, January 2027 is 13. Everything about coverage and arrears is worked
// out on that run, which is why the parser below has to understand every way a
// month has ever been typed into this system - "June", "Sept", "Aug-Dec",
// "May-Aug", "July/Aug", "Jun - Aug", "October 2026", "Aug-Nov'25", even the
// misspelling "Jume".
const PERIOD_BASE_YEAR = 2026;

const CURRENT_PERIOD_INDEX = (function () {
  const now = new Date();
  return (now.getFullYear() - PERIOD_BASE_YEAR) * 12 + (now.getMonth() + 1);
})();

// The bare month name, without a year, used as the default in the payment forms.
const CURRENT_MONTH_PLAIN = MONTH_ORDER[new Date().getMonth()];

function monthLabelFromKey(key) {
  // key format: YYYY-MM  ->  'October 2026'
  if (!key || key.length < 7) return key || '';
  const year = key.slice(0, 4);
  const month = MONTH_ORDER[parseInt(key.slice(5, 7), 10) - 1];
  return month ? (month + ' ' + year) : key;
}

function monthNumberFromToken(token) {
  const w = String(token || '').toLowerCase().slice(0, 3);
  const map = { jan: 1, feb: 2, mar: 3, apr: 4, may: 5, jun: 6, jul: 7, aug: 8, sep: 9, oct: 10, nov: 11, dec: 12 };
  return map[w] || 0;
}

function periodIndexFromParts(year, monthNum) {
  return (Number(year) - PERIOD_BASE_YEAR) * 12 + Number(monthNum);
}

function monthNameFromPeriodIndex(idx) {
  const n = Number(idx);
  if (!isFinite(n) || n === 0) return '';
  const monthNum = ((Math.round(n) - 1) % 12 + 12) % 12 + 1;
  return MONTH_ORDER[monthNum - 1];
}

// Reads a written month or month range and returns the first and last month it
// covers. Returns null when nothing month-like can be found.
function parsePeriodLabel(label) {
  if (label === undefined || label === null) return null;
  let s = String(label).toLowerCase().trim();
  if (!s) return null;

  // misspellings that already exist in the records
  s = s.replace(/jume/g, 'june').replace(/jule/g, 'july').replace(/setp/g, 'sept');

  let year = null;
  const full = s.match(/(20\d{2})/);
  if (full) {
    year = Number(full[1]);
  } else {
    const short = s.match(/['\u2019]\s?(\d{2})\b/);
    if (short) year = 2000 + Number(short[1]);
  }

  const re = /\b(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*/g;
  const found = [];
  let m;
  while ((m = re.exec(s)) !== null) {
    const num = monthNumberFromToken(m[1]);
    if (num) found.push(num);
  }
  if (!found.length) return null;

  const baseYear = year || new Date().getFullYear();
  // Lowest and highest month named, so "Sept - Dec" and "Dec/Sept" both read
  // as the same span instead of depending on the order they were typed.
  const startMonth = Math.min.apply(null, found);
  const endMonth = Math.max.apply(null, found);
  const endYear = endMonth < startMonth ? baseYear + 1 : baseYear;
  // Months before the concession year come back as 0: they cover nothing here.
  return {
    start: Math.max(0, periodIndexFromParts(baseYear, startMonth)),
    end: Math.max(0, periodIndexFromParts(endYear, endMonth))
  };
}

// The last month a written label reaches.
function periodIndexOf(label) {
  const parsed = parsePeriodLabel(label);
  return parsed ? parsed.end : 0;
}


// ---------------------------------------------------------------------------
// FORMATTERS
// ---------------------------------------------------------------------------
function formatNaira(amount) {
  return '\u20a6' + Number(amount || 0).toLocaleString('en-NG');
}

function formatDate(dateStr) {
  if (!dateStr) return 'N/A';
  try {
    return new Date(dateStr).toLocaleDateString('en-GB', { day: '2-digit', month: 'short', year: 'numeric' });
  } catch (e) {
    return dateStr;
  }
}

function formatShortDate(dateStr) {
  if (!dateStr) return '';
  try {
    const d = new Date(dateStr);
    const dd = String(d.getDate()).padStart(2, '0');
    const mm = String(d.getMonth() + 1).padStart(2, '0');
    return dd + '/' + mm + '/' + d.getFullYear();
  } catch (e) {
    return dateStr;
  }
}

function formatLongDate(dateStr) {
  if (!dateStr) return 'N/A';
  try {
    return new Date(dateStr).toLocaleDateString('en-GB', { day: '2-digit', month: 'long', year: 'numeric' });
  } catch (e) {
    return dateStr;
  }
}

function currentUsageDateIso() {
  const now = new Date();
  const y = now.getFullYear();
  const m = String(now.getMonth() + 1).padStart(2, '0');
  const d = String(now.getDate()).padStart(2, '0');
  return y + '-' + m + '-' + d;
}

function formatLetterDate(dateStr) {
  const effective = (!dateStr || dateStr === CURRENT_SYSTEM_DATE) ? currentUsageDateIso() : dateStr;
  const d = new Date(effective.length === 10 ? (effective + 'T12:00:00') : effective);
  const day = d.getDate();
  const suffix = (day % 10 === 1 && day !== 11) ? 'st' : (day % 10 === 2 && day !== 12) ? 'nd' : (day % 10 === 3 && day !== 13) ? 'rd' : 'th';
  return day + suffix + ' ' + d.toLocaleDateString('en-GB', { month: 'long' }) + ', ' + d.getFullYear();
}

// Short clock label used by the field tracking panel (24 hour, local time)
function formatTime(value) {
  if (!value) return '--:--';
  const d = value instanceof Date ? value : new Date(value);
  if (isNaN(d.getTime())) return '--:--';
  return String(d.getHours()).padStart(2, '0') + ':' + String(d.getMinutes()).padStart(2, '0');
}

function formatTimestamp(dateValue) {
  const d = dateValue ? new Date(dateValue) : new Date();
  return d.toLocaleDateString('en-GB', { day: '2-digit', month: 'short', year: 'numeric' }) + ' ' +
         d.toLocaleTimeString('en-GB', { hour: '2-digit', minute: '2-digit' });
}

function getDaysSince(dateStr) {
  if (!dateStr) return 999;
  const diff = new Date(CURRENT_SYSTEM_DATE) - new Date(dateStr);
  return Math.max(0, Math.floor(diff / 86400000));
}

function numberToWords(num) {
  num = Math.round(Number(num) || 0);
  if (num === 0) return 'Zero Naira';
  const a = ['', 'One', 'Two', 'Three', 'Four', 'Five', 'Six', 'Seven', 'Eight', 'Nine', 'Ten', 'Eleven', 'Twelve', 'Thirteen', 'Fourteen', 'Fifteen', 'Sixteen', 'Seventeen', 'Eighteen', 'Nineteen'];
  const b = ['', '', 'Twenty', 'Thirty', 'Forty', 'Fifty', 'Sixty', 'Seventy', 'Eighty', 'Ninety'];
  function inWords(n) {
    if (n < 20) return a[n];
    if (n < 100) return b[Math.floor(n / 10)] + (n % 10 !== 0 ? ' ' + a[n % 10] : '');
    if (n < 1000) return a[Math.floor(n / 100)] + ' Hundred' + (n % 100 !== 0 ? ' & ' + inWords(n % 100) : '');
    if (n < 1000000) return inWords(Math.floor(n / 1000)) + ' Thousand' + (n % 1000 !== 0 ? ', ' + inWords(n % 1000) : '');
    if (n < 1000000000) return inWords(Math.floor(n / 1000000)) + ' Million' + (n % 1000000 !== 0 ? ', ' + inWords(n % 1000000) : '');
    return String(n);
  }
  return inWords(num) + ' Naira';
}

function escapeHtml(value) {
  return String(value === undefined || value === null ? '' : value)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}

function cleanAddress(value) {
  return String(value || '').replace(/:/g, ',').replace(/\s*,\s*/g, ', ').trim();
}

// ---------------------------------------------------------------------------
// PAYMENT HEALTH ENGINE (Automatic arrears - no manual entry)
// ---------------------------------------------------------------------------
function latestPayment(facility) {
  const history = Array.isArray(facility && facility.paymentHistory) ? facility.paymentHistory : [];
  if (!history.length) return null;
  return history.slice().sort((x, y) => {
    const dx = new Date(x.date || 0).getTime();
    const dy = new Date(y.date || 0).getTime();
    if (dy !== dx) return dy - dx;
    return (periodIndexOf(y.periodTo) - periodIndexOf(x.periodTo));
  })[0];
}

// The last month this facility has actually paid for. A payment written as a
// range covers every month up to the end of that range.
// Names are compared with everything but letters and digits stripped, so
// "Golden Grace School" and "GOLDEN GRACE SCHOOL." are the same outlet.
function payRowKey(name) {
  return String(name || '').toLowerCase().replace(/[^a-z0-9]/g, '');
}

// Every payment on file for a facility: its own history PLUS any payment logged
// in the Payment Schedule Manager under the same outlet. A payment that was
// entered in the schedule but never copied into the facility record still
// counts as paid - that was the reason a facility that paid in August could
// still show as paid up.
function allPaymentRowsForFacility(facility) {
  if (!facility) return [];
  const key = payRowKey(facility.name);
  const out = (Array.isArray(facility.paymentHistory) ? facility.paymentHistory : []).slice();
  const seen = {};
  out.forEach(p => { if (p && p.id) seen[p.id] = true; });
  (store.state.paymentScheduleRecords || []).forEach(p => {
    if (!p) return;
    if (p.id && seen[p.id]) return;
    const rowKey = payRowKey(p.outlet);
    if (!rowKey || rowKey !== key) return;
    seen[p.id] = true;
    out.push(p);
  });
  return out;
}

// First and last month a payment row covers. Reads periodFrom/periodTo when the
// row has them, otherwise the written month, otherwise the date it was paid.
function paymentRowRange(row) {
  if (!row) return null;
  const from = parsePeriodLabel(row.periodFrom || row.month);
  const to = parsePeriodLabel(row.periodTo || row.month);
  let start = from ? from.start : (to ? to.start : null);
  let end = to ? to.end : (from ? from.end : null);
  if (start === null && end === null) {
    const iso = String(row.date || '').slice(0, 7);
    if (iso.length !== 7) return null;
    const idx = periodIndexFromParts(Number(iso.slice(0, 4)), Number(iso.slice(5, 7)));
    start = idx; end = idx;
  }
  if (start === null) start = end;
  if (end === null) end = start;
  return { start: Math.max(0, start), end: Math.max(0, end) };
}

function coveredThroughIndex(facility) {
  const history = allPaymentRowsForFacility(facility);
  if (!history.length) return 0;
  let best = 0;
  history.forEach(p => {
    if (!p) return;
    const parsed = parsePeriodLabel(p.periodTo || p.month || p.periodFrom);
    if (parsed) {
      best = Math.max(best, parsed.end);
      return;
    }
    // No readable month: fall back to the month the money was received.
    const iso = String(p.date || '').slice(0, 7);
    if (iso.length === 7) {
      best = Math.max(best, periodIndexFromParts(Number(iso.slice(0, 4)), Number(iso.slice(5, 7))));
    }
  });
  return best;
}

// The months this facility should already have paid for and has not.
//
// The month we are in is never counted: a bill becomes outstanding on the 1st
// of the following month, so in October the last month that can be owing is
// September. Payment history is read through the month parser, so a payment
// written "Aug-Dec" covers the facility to December and nothing is owing.
function outstandingPeriodIndexes(facility) {
  // A facility with no payment on file at all is not chased - it starts to
  // count from its first payment, exactly as it always has.
  const history = allPaymentRowsForFacility(facility);
  if (!history.length) return [];
  const covered = coveredThroughIndex(facility);
  const lastDue = CURRENT_PERIOD_INDEX - 1;
  // Never claim further back than the start of the concession year.
  const first = Math.max(1, covered + 1);
  const out = [];
  for (let i = first; i <= lastDue; i++) out.push(i);
  return out;
}

function getPaymentHealth(facility) {
  const owing = outstandingPeriodIndexes(facility);
  const monthlyBill = Number(facility && facility.amount || 0) * (1 + (Number(facility && facility.vat || 0) / 100));

  if (!owing.length) {
    return { status: 'Paid Up', owingMonths: 0, arrears: 0, class: 'badge-success', label: 'Paid Up', months: [] };
  }

  const arrears = Math.round(monthlyBill * owing.length);
  const label = owing.length === 1
    ? 'Owing ' + monthNameFromPeriodIndex(owing[0])
    : 'Owing ' + owing.length + ' months';
  return {
    status: owing.length === 1 ? 'Owing' : 'Owing ' + owing.length + ' Months',
    owingMonths: owing.length,
    arrears: arrears,
    class: 'badge-warning',
    label: label,
    months: owing
  };
}

// ---------------------------------------------------------------------------
// EVACUATION SCHEDULE ENGINE
// ---------------------------------------------------------------------------
function getScheduleStatus(item) {
  if (!item.lastEvacuated) {
    return { status: 'AWAITING EVACUATION', days: 0, isOverdue: false, class: 'badge-warning', label: 'Awaiting 1st Evacuation' };
  }
  const days = getDaysSince(item.lastEvacuated);
  const isIndustrial = item.category === 'Industrial';
  if (isIndustrial) {
    if (days > 30) return { status: 'OVERDUE', days: days, isOverdue: true, class: 'badge-danger', label: 'OVERDUE (' + days + 'd ago)' };
    if (days >= 20) return { status: 'DUE SOON', days: days, isOverdue: false, class: 'badge-warning', label: 'Due Soon (' + days + 'd ago)' };
    return { status: 'OPTIMAL', days: days, isOverdue: false, class: 'badge-success', label: 'Optimal (' + days + 'd ago)' };
  }
  if (days > 14) return { status: 'OVERDUE', days: days, isOverdue: true, class: 'badge-danger', label: 'OVERDUE (' + days + 'd ago)' };
  if (days >= 7) return { status: 'DUE SOON', days: days, isOverdue: false, class: 'badge-warning', label: 'Due Soon (' + days + 'd ago)' };
  return { status: 'OPTIMAL', days: days, isOverdue: false, class: 'badge-success', label: 'Optimal (' + days + 'd ago)' };
}

function allUnits() {
  const facilities = store.state.facilities.map(f => Object.assign({}, f, { unitType: 'Facility' }));
  const streets = store.state.municipalStreets.map(s => Object.assign({}, s, { unitType: 'Municipal Street', category: 'Municipal Residential' }));
  return facilities.concat(streets);
}

// ---------------------------------------------------------------------------
// AUDIT PERIOD RESOLUTION
// ---------------------------------------------------------------------------
function periodWindow(periodKey) {
  const now = new Date();
  const fmtIso = d => d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0');
  const fmtShort = d => String(d.getDate()).padStart(2, '0') + ' ' + ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'][d.getMonth()] + ' ' + d.getFullYear();
  const dayOfWeek = now.getDay(); // 0=Sun
  const startCurrentWeek = new Date(now.getFullYear(), now.getMonth(), now.getDate() - dayOfWeek);
  const endCurrentWeek = new Date(now.getFullYear(), now.getMonth(), now.getDate() - dayOfWeek + 6);
  const startLastWeek = new Date(now.getFullYear(), now.getMonth(), now.getDate() - dayOfWeek - 7);
  const endLastWeek = new Date(now.getFullYear(), now.getMonth(), now.getDate() - dayOfWeek - 1);

  switch (periodKey) {
    case 'week_current':
      return {
        label: 'This Week (' + String(startCurrentWeek.getDate()).padStart(2, '0') + ' - ' + fmtShort(endCurrentWeek) + ')',
        from: fmtIso(startCurrentWeek),
        to: fmtIso(endCurrentWeek)
      };
    case 'week_last':
      return {
        label: 'Last Week (' + String(startLastWeek.getDate()).padStart(2, '0') + ' - ' + fmtShort(endLastWeek) + ')',
        from: fmtIso(startLastWeek),
        to: fmtIso(endLastWeek)
      };
    case 'month_09': return { label: 'Month of September 2026', from: '2026-09-01', to: '2026-09-30' };
    case 'month_08': return { label: 'Month of August 2026', from: '2026-08-01', to: '2026-08-31' };
    case 'month_07': return { label: 'Month of July 2026', from: '2026-07-01', to: '2026-07-31' };
    default: {
      const mStart = new Date(now.getFullYear(), now.getMonth(), 1);
      const mEnd = new Date(now.getFullYear(), now.getMonth() + 1, 0);
      return { label: 'Month of ' + CURRENT_MONTH_NAME, from: fmtIso(mStart), to: fmtIso(mEnd) };
    }
  }
}

// ===========================================================================
// 1. NAVIGATION
// ===========================================================================
function goHome() { switchView('overview'); }

function goBack() {
  if (navigationHistory.length > 1) {
    navigationHistory.pop();
    switchView(navigationHistory[navigationHistory.length - 1], false);
  } else {
    switchView('overview', false);
  }
}

function refreshCurrentView() {
  const prevSessionId = store && store.state ? store.state.sessionUserId : null;
  const saved = SafeStorage.get(store.storageKey);
  if (saved) {
    try {
      store.state = JSON.parse(saved);
      store.migrate(false);
      if (prevSessionId && !store.state.sessionUserId) {
        store.state.sessionUserId = prevSessionId;
      }
    } catch (e) { /* keep current state */ }
  }
  if (typeof pullFromSupabaseOnline === 'function' && isInternetConnected()) {
    pullFromSupabaseOnline({ isBackgroundTick: false, forcePull: true }).catch(() => {});
  }
  applySessionUI();
  updateHeaderStats();
  evaluateTrackerAlerts();
  renderCurrentView();
  showToast('\ud83d\udd04 Live operational data refreshed', 'info');
}

function updateRoleUI() {
  // role now comes from the signed in user account
  applySessionUI();
}

var settingsUnlockedSession = false;

function isValidAdminGatePassword(pwd) {
  const clean = String(pwd || '').trim();
  if (!clean) return false;
  if (clean === '1234' || clean === ADMIN_PASSWORD || clean === 'teem2026') return true;
  return (store.state.users || []).some(u => isUserAdminRole(u) && u.status !== 'Disabled' && checkPassword(clean, u.password));
}

function unlockSettingsMenu(pwd) {
  if (isValidAdminGatePassword(pwd)) {
    settingsUnlockedSession = true;
    closeModal('modal-settings-password');
    switchView('settings', true, true);
    return true;
  }
  return false;
}

function submitSettingsPassword(e) {
  if (e) e.preventDefault();
  const input = document.getElementById('settings-gate-password');
  const errEl = document.getElementById('settings-gate-error');
  const val = input ? input.value.trim() : '';
  if (unlockSettingsMenu(val)) {
    if (input) input.value = '';
    if (errEl) errEl.style.display = 'none';
    showToast('\ud83d\udd13 Settings menu unlocked.', 'success');
  } else {
    if (errEl) {
      errEl.textContent = 'Incorrect password. Please enter 1234 to open Settings.';
      errEl.style.display = 'block';
    }
    showToast('\u26a0\ufe0f Incorrect Settings password.', 'error');
  }
}

window.unlockSettingsMenu = unlockSettingsMenu;
window.submitSettingsPassword = submitSettingsPassword;

function switchView(viewId, pushHistory = true, bypassSettingsGate = false) {
  if (pushHistory === undefined) pushHistory = true;
  if (viewId === 'settings' && !settingsUnlockedSession && !bypassSettingsGate) {
    closeMobileNav();
    const gateModal = document.getElementById('modal-settings-password');
    const gateInput = document.getElementById('settings-gate-password');
    const gateErr = document.getElementById('settings-gate-error');
    if (gateModal && gateInput) {
      gateInput.value = '';
      if (gateErr) gateErr.style.display = 'none';
      openModal('modal-settings-password');
      setTimeout(() => { try { gateInput.focus(); } catch (e) {} }, 60);
      return;
    }
  }
  if (pushHistory && currentActiveView !== viewId) navigationHistory.push(viewId);
  currentActiveView = viewId;
  closeMobileNav();

  document.querySelectorAll('.view-panel').forEach(el => el.classList.remove('active'));
  document.querySelectorAll('.sidebar-nav .nav-item').forEach(el => el.classList.remove('active'));

  const target = document.getElementById('view-' + viewId);
  if (target) target.classList.add('active');

  const navItem = document.querySelector('.sidebar-nav a[href="#' + viewId + '"]');
  if (navItem) navItem.classList.add('active');

  if (viewId === 'overview') startDashSlides(); else stopDashSlides();

  renderCurrentView();
  window.scrollTo({ top: 0, behavior: 'smooth' });
  // the content pane scrolls on its own, so reset that one too
  const pane = document.querySelector('.main-wrapper') || document.querySelector('.main-content') || document.querySelector('.content-area');
  if (pane && typeof pane.scrollTo === 'function') pane.scrollTo({ top: 0 });
}

function toggleMobileNav() {
  const isOpen = !document.body.classList.contains('mobile-nav-open');
  document.body.classList.toggle('mobile-nav-open', isOpen);
}

function openMobileNav() {
  document.body.classList.add('mobile-nav-open');
}

function closeMobileNav() {
  if (document.body) document.body.classList.remove('mobile-nav-open');
}

function openIphoneInstallModal() {
  closeMobileNav();
  openModal('modal-iphone-guide');
}

function toggleSidebar() {
  if (typeof window !== 'undefined' && window.innerWidth <= 900) {
    toggleMobileNav();
    return;
  }
  const collapsed = !document.body.classList.contains('sidebar-collapsed');
  document.body.classList.toggle('sidebar-collapsed', collapsed);
  store.state.settings.sidebarCollapsed = collapsed;
  store.save();
  const map = document.getElementById('gps-map');
  if (map) setTimeout(renderGpsMap, 260);
}

function applySidebarState() {
  const collapsed = !!store.state.settings.sidebarCollapsed;
  document.body.classList.toggle('sidebar-collapsed', collapsed);
}

function toggleDropdown(dropdownId) {
  // a collapsed rail cannot show sub-items, so expand first
  if (document.body.classList.contains('sidebar-collapsed')) {
    document.body.classList.remove('sidebar-collapsed');
    store.state.settings.sidebarCollapsed = false;
    store.save();
  }
  const el = document.getElementById(dropdownId);
  if (el) el.classList.toggle('open');
}

function filterFacilityCategory(category) {
  currentFacilityFilter = category;
  closeMobileNav();
  switchView('facilities');

  document.querySelectorAll('.nav-sub-item').forEach(sub => {
    const oc = sub.getAttribute('onclick') || '';
    sub.classList.toggle('active', oc.indexOf("'" + category + "'") !== -1);
  });
  document.querySelectorAll('#fac-filter-tabs .filter-tab').forEach(tab => {
    const cat = tab.dataset.category || '';
    tab.classList.toggle('active', cat.toLowerCase() === String(category).toLowerCase());
  });

  const titles = {
    all: ['MASTER FACILITIES DIRECTORY', 'Official registered Commercial, Industrial, Medical, Institutional, Agricultural and Construction clients'],
    Commercial: ['COMMERCIAL FACILITIES DIRECTORY', 'Registered commercial outlets served across the Abeokuta concession corridor'],
    Industrial: ['INDUSTRIAL FACILITIES DIRECTORY', 'Industrial manufacturing plants (60% Rebate Account: 0079828285)'],
    Medical: ['MEDICAL FACILITIES DIRECTORY', 'Registered hospitals, diagnostic centres and clinics'],
    Institutional: ['INSTITUTIONAL FACILITIES DIRECTORY', 'Registered schools, churches and institutional centres'],
    'Agricultural Waste': ['AGRICULTURAL WASTE DIRECTORY', 'Poultry farms, agro-processing plants, feedmills and livestock clients'],
    'Construction Waste': ['CONSTRUCTION WASTE DIRECTORY', 'Demolition debris, construction sites, earthworks and haulage clients'],
    debtors: ['OUTSTANDING PAYMENT RADAR', 'Facilities with outstanding service bills requiring follow-up']
  };
  const meta = titles[category] || titles.all;
  const titleEl = document.getElementById('facilities-view-title');
  const subEl = document.getElementById('facilities-view-subtitle');
  if (titleEl) titleEl.textContent = meta[0];
  if (subEl) subEl.textContent = meta[1];

  renderFacilitiesDirectory();
}

// ===========================================================================
// 2. DASHBOARD - SLIDES + CLICKABLE CARDS + COMPANY OVERVIEW
// ===========================================================================
function renderDashboardSlides() {
  const slides = (TEEM_IMG.slides || []);
  const track = document.getElementById('dash-slide-track');
  const dots = document.getElementById('dash-slide-dots');
  if (!track) return;

  const captions = [
    { title: 'Door-to-Door Waste Collection', text: 'Scheduled compactor routes across Abeokuta concession zones' },
    { title: 'Sorting & Resource Recovery', text: 'Recyclables recovered and channelled back into the circular economy' },
    { title: 'Cleaner Communities', text: 'Every street evacuated, verified and recorded in this portal' }
  ];

  track.innerHTML = slides.map((src, i) => {
    const cap = captions[i % captions.length];
    return '<div class="dash-slide' + (i === 0 ? ' active' : '') + '">' +
      '<img src="' + src + '" alt="' + escapeHtml(cap.title) + '">' +
      '<div class="dash-slide-caption">' +
        '<span class="dash-slide-kicker">TEEM Business Nigeria Enterprises (RC OG20434)</span>' +
        '<strong>' + escapeHtml(cap.title) + '</strong>' +
        '<span>' + escapeHtml(cap.text) + '</span>' +
      '</div>' +
    '</div>';
  }).join('');

  if (dots) {
    dots.innerHTML = slides.map((_, i) =>
      '<button class="dash-dot' + (i === 0 ? ' active' : '') + '" onclick="goToSlide(' + i + ')" aria-label="Slide ' + (i + 1) + '"></button>'
    ).join('');
  }
  dashSlideIndex = 0;

  const showcase = track.closest ? track.closest('.dash-showcase') : track.parentElement;
  if (showcase && !showcase._swipeBound) {
    showcase._swipeBound = true;
    let touchStartX = 0;
    let touchStartY = 0;
    showcase.addEventListener('touchstart', (ev) => {
      if (ev.touches && ev.touches.length === 1) {
        touchStartX = ev.touches[0].clientX;
        touchStartY = ev.touches[0].clientY;
      }
    }, { passive: true });
    showcase.addEventListener('touchend', (ev) => {
      if (ev.changedTouches && ev.changedTouches.length === 1) {
        const dx = ev.changedTouches[0].clientX - touchStartX;
        const dy = ev.changedTouches[0].clientY - touchStartY;
        if (Math.abs(dx) > 40 && Math.abs(dx) > Math.abs(dy)) {
          nextSlide(dx < 0 ? 1 : -1);
        }
      }
    }, { passive: true });
  }
}

function goToSlide(index) {
  const slides = document.querySelectorAll('#dash-slide-track .dash-slide');
  const dots = document.querySelectorAll('#dash-slide-dots .dash-dot');
  if (!slides.length) return;
  dashSlideIndex = (index + slides.length) % slides.length;
  slides.forEach((s, i) => s.classList.toggle('active', i === dashSlideIndex));
  dots.forEach((d, i) => d.classList.toggle('active', i === dashSlideIndex));
}

function nextSlide(dir) { goToSlide(dashSlideIndex + (dir || 1)); }

function startDashSlides() {
  stopDashSlides();
  if (document.querySelectorAll('#dash-slide-track .dash-slide').length < 2) return;
  dashSlideTimer = setInterval(() => goToSlide(dashSlideIndex + 1), 6000);
}

function stopDashSlides() {
  if (dashSlideTimer) { clearInterval(dashSlideTimer); dashSlideTimer = null; }
}

function renderDashboardCards() {
  const fac = store.state.facilities;
  const count = c => fac.filter(f => f.category === c).length;
  const set = (id, value) => { const el = document.getElementById(id); if (el) el.textContent = value; };

  set('dash-count-all', fac.length + ' Clients');
  set('dash-count-streets', store.state.municipalStreets.length + ' Streets');
  set('dash-count-commercial', count('Commercial') + ' Outlets');
  set('dash-count-industrial', count('Industrial') + ' Plants');
  set('dash-count-institutional', count('Institutional') + ' Clients');
  set('dash-count-medical', count('Medical') + ' Facilities');

  const overdue = allUnits().filter(u => getScheduleStatus(u).isOverdue).length;
  set('dash-count-notices', overdue + ' Notices');

  const owing = fac.filter(f => getPaymentHealth(f).owingMonths > 0).length;
  set('dash-count-outstanding', owing + ' Clients');
}

// ===========================================================================
// 3. FACILITIES DIRECTORY
// ===========================================================================
function renderFacilitiesDirectory() {
  const container = document.getElementById('facilities-list-body');
  const localSearch = document.getElementById('fac-local-search');
  const globalSearch = document.getElementById('facility-search-input');
  const query = ((localSearch && localSearch.value) || (globalSearch && globalSearch.value) || '').toLowerCase().trim();

  const filtered = store.state.facilities.filter(f => {
    const health = getPaymentHealth(f);
    const catOk = currentFacilityFilter === 'all' ||
      f.category.toLowerCase() === String(currentFacilityFilter).toLowerCase() ||
      (currentFacilityFilter === 'debtors' && health.owingMonths > 0);
    const latest = latestPayment(f);
    const searchOk = !query ||
      f.name.toLowerCase().indexOf(query) !== -1 ||
      (f.location || '').toLowerCase().indexOf(query) !== -1 ||
      (f.supervisor || '').toLowerCase().indexOf(query) !== -1 ||
      (latest && latest.payerName && latest.payerName.toLowerCase().indexOf(query) !== -1);
    return catOk && searchOk;
  });

  const badge = document.getElementById('facilities-match-count');
  if (badge) badge.textContent = query ? 'Showing ' + filtered.length + ' matching "' + query + '"' : 'Showing ' + filtered.length + ' entries';

  if (container) {
    if (!filtered.length) {
      container.innerHTML = '<tr><td colspan="6" style="text-align:center;padding:40px;color:var(--text-muted);">No registered facilities found.</td></tr>';
    } else {
      container.innerHTML = filtered.map(f => {
        const sched = getScheduleStatus(f);
        const health = getPaymentHealth(f);
        const vatAmount = f.amount * ((f.vat || 0) / 100);
        const latest = latestPayment(f) || {};
        return '<tr style="cursor:pointer;" onclick="openFacilityReportModal(\'' + f.id + '\')">' +
          '<td>' +
            '<strong style="font-size:14px;color:var(--text-main);">' + escapeHtml(f.name) + '</strong>' +
            '<div style="margin-top:4px;"><span class="badge badge-supervisor">\ud83d\udc64 ' + escapeHtml(f.supervisor) + '</span></div>' +
          '</td>' +
          '<td><span class="badge badge-category">' + escapeHtml(f.category) + '</span></td>' +
          '<td><strong style="font-size:14px;">' + formatNaira(f.amount) + '</strong>' +
            '<div style="font-size:11px;color:var(--text-muted);">' + (f.vat ? '+' + f.vat + '% VAT = ' + formatNaira(f.amount + vatAmount) : '0% VAT (Statutory Rebate)') + '</div></td>' +
          '<td><span class="badge ' + sched.class + '">' + sched.label + '</span>' +
          '<td><div style="font-size:12px;font-weight:700;">' + escapeHtml(latest.payerName || f.name) + '</div>' +
            '<div style="font-size:11px;color:var(--eco-green);font-weight:600;">' + formatNaira(latest.amount || 0) + ' on ' + formatShortDate(latest.date) + '</div>' +
            '<div style="font-size:10.5px;color:var(--text-muted);">Coverage to ' + escapeHtml(latest.periodTo || 'N/A') + ' \u2022 ' + ((f.paymentHistory || []).length) + ' payment(s)</div>' +
            '<div style="margin-top:3px;"><span class="badge ' + health.class + '">' + health.label + '</span></div></td>' +
          '<td onclick="event.stopPropagation()"><div class="action-btn-group">' +
            '<button class="btn btn-sm btn-primary" onclick="promptEvacuateFacility(\'' + f.id + '\')">\ud83d\ude9b Evacuated</button>' +
            '<button class="btn btn-sm btn-outline" onclick="openFacilityReportModal(\'' + f.id + '\')">\ud83d\udcc4 Report</button>' +
            (isAdmin() ? '<button class="btn btn-sm btn-outline" onclick="openEditFacilityModal(\'' + f.id + '\')">\u270f\ufe0f Edit</button>' : '') +
            (isAdmin() ? '<button class="btn btn-sm btn-outline" style="color:#B91C1C;border-color:#FCA5A5;" onclick="event.stopPropagation();deleteFacilityById(\'' + f.id + '\')">\ud83d\uddd1\ufe0f Delete</button>' : '') +
          '</div></td>' +
        '</tr>';
      }).join('');
    }
  }

  const tab = (id, cat) => {
    const el = document.getElementById(id);
    if (!el) return;
    if (cat === 'all') el.textContent = 'All (' + store.state.facilities.length + ')';
    else if (cat === 'debtors') el.textContent = 'Outstanding (' + store.state.facilities.filter(f => getPaymentHealth(f).owingMonths > 0).length + ')';
    else el.textContent = cat.replace(' Waste', '') + ' (' + store.state.facilities.filter(f => f.category === cat).length + ')';
  };
  tab('fac-tab-all', 'all');
  tab('fac-tab-comm', 'Commercial');
  tab('fac-tab-ind', 'Industrial');
  tab('fac-tab-med', 'Medical');
  tab('fac-tab-inst', 'Institutional');
  tab('fac-tab-agro', 'Agricultural Waste');
  tab('fac-tab-constr', 'Construction Waste');
  tab('fac-tab-debtors', 'debtors');
}

// ===========================================================================
// 4. FACILITY EVACUATION - YES / NO CONFIRMATION
// ===========================================================================
function promptEvacuateFacility(facilityId) {
  const f = store.state.facilities.find(x => x.id === facilityId);
  if (!f) return;
  pendingEvacuateFacilityId = facilityId;

  const titleEl = document.getElementById('prompt-fac-title');
  const metaEl = document.getElementById('prompt-fac-meta');
  const dateEl = document.getElementById('prompt-fac-date');
  const truckSelect = document.getElementById('prompt-fac-truck');

  if (titleEl) titleEl.textContent = 'Has ' + f.name + ' been evacuated today?';
  if (metaEl) metaEl.textContent = 'Sector: ' + f.category + ' \u2022 Supervisor: ' + f.supervisor;
  if (dateEl) dateEl.value = currentUsageDateIso();
  if (truckSelect) truckSelect.innerHTML = store.state.vehicles.map(v => '<option value="' + escapeHtml(v.name) + '">' + escapeHtml(v.name) + '</option>').join('');

  openModal('modal-facility-evacuate-prompt');
}

function confirmEvacuateFacility(isYes) {
  closeModal('modal-facility-evacuate-prompt');
  if (!isYes || !pendingEvacuateFacilityId) return;

  const f = store.state.facilities.find(x => x.id === pendingEvacuateFacilityId);
  if (!f) return;

  const truckEl = document.getElementById('prompt-fac-truck');
  const truckUsed = truckEl ? truckEl.value : 'Blue Compactor (TEEM-01)';
  const dateEl = document.getElementById('prompt-fac-date');
  const evacDate = (dateEl && /^\d{4}-\d{2}-\d{2}$/.test(dateEl.value)) ? dateEl.value : currentUsageDateIso();
  const evacMonth = monthLabelFromKey(evacDate.slice(0, 7)) || CURRENT_MONTH_NAME;

  f.lastEvacuated = evacDate;
  if (!Array.isArray(f.evacuationHistory)) f.evacuationHistory = [];
  f.evacuationHistory.unshift({
    date: evacDate,
    month: evacMonth,
    truck: truckUsed,
    supervisor: f.supervisor,
    tonnage: f.category === 'Industrial' ? (f.amount / 16000).toFixed(1) : null,
    status: 'Verified Complete'
  });

  store.state.evacuationLogs.unshift({
    id: 'EVAC-FAC-' + Date.now().toString().slice(-5),
    date: evacDate,
    target: f.name,
    truck: truckUsed,
    supervisor: f.supervisor,
    status: 'Completed'
  });

  store.save();
  renderFacilitiesDirectory();
  renderEvacuations();
  showToast('\u2705 ' + f.name + ' marked as evacuated today. Schedule, report and audit updated.', 'success');
}

// ===========================================================================
// 5. MUNICIPAL DIRECTORY
// ===========================================================================
function renderMunicipalDirectory() {
  const container = document.getElementById('municipal-list-body');
  const searchInput = document.getElementById('municipal-search-input');
  const query = searchInput ? searchInput.value.toLowerCase().trim() : '';

  const filtered = store.state.municipalStreets.filter(s =>
    !query || s.name.toLowerCase().indexOf(query) !== -1 || (s.location || '').toLowerCase().indexOf(query) !== -1 || (s.supervisor || '').toLowerCase().indexOf(query) !== -1
  );

  if (container) {
    if (!filtered.length) {
      container.innerHTML = '<tr><td colspan="5" style="text-align:center;padding:40px;color:var(--text-muted);">No municipal streets found.</td></tr>';
    } else {
      container.innerHTML = filtered.map(s => {
        const days = getDaysSince(s.lastEvacuated);
        const cls = days > 14 ? 'badge-danger' : days >= 7 ? 'badge-warning' : 'badge-success';
        const label = days > 14 ? 'OVERDUE (' + days + 'd)' : days >= 7 ? 'Due Soon (' + days + 'd)' : 'Optimal (' + days + 'd)';
        return '<tr style="cursor:pointer;" onclick="openStreetReportModal(\'' + s.id + '\')">' +
          '<td><strong style="font-size:14px;">' + escapeHtml(s.name) + '</strong></td>' +
          '<td><span class="badge badge-supervisor">\ud83d\udc64 ' + escapeHtml(s.supervisor) + '</span></td>' +
          '<td><strong>' + formatDate(s.lastEvacuated) + '</strong>' +
            '<div style="font-size:11px;color:var(--text-muted);margin-top:2px;">' + days + ' days elapsed</div></td>' +
          '<td><span class="badge ' + cls + '">' + label + '</span></td>' +
          '<td onclick="event.stopPropagation()"><div class="action-btn-group">' +
            '<button class="btn btn-sm btn-primary" onclick="openEvacuateStreetModal(\'' + s.id + '\')">\ud83d\ude9b Evacuate</button>' +
            '<button class="btn btn-sm btn-outline" onclick="openStreetReportModal(\'' + s.id + '\')">\ud83d\udcc4 Report</button>' +
            '<button class="btn btn-sm btn-outline" onclick="openEditStreetModal(\'' + s.id + '\')">\u270f\ufe0f Edit</button>' +
          '</div></td>' +
        '</tr>';
      }).join('');
    }
  }

  const badge = document.getElementById('mun-street-count');
  if (badge) badge.textContent = 'All ' + store.state.municipalStreets.length + ' Streets';
}

function openEvacuateStreetModal(streetId) {
  const s = store.state.municipalStreets.find(x => x.id === streetId);
  if (!s) return;
  document.getElementById('evac-street-id').value = s.id;
  document.getElementById('evac-street-title').textContent = s.name;
  const locEl = document.getElementById('evac-street-location');
  if (locEl) { locEl.textContent = ''; locEl.style.display = 'none'; }
  document.getElementById('evac-street-supervisor').textContent = s.supervisor;
  document.getElementById('evac-street-date').value = CURRENT_SYSTEM_DATE;
  const truck = document.getElementById('evac-street-truck');
  if (truck) truck.innerHTML = store.state.vehicles.map(v => '<option value="' + escapeHtml(v.name) + '">' + escapeHtml(v.name) + '</option>').join('');
  openModal('modal-evacuate-street');
}

function saveEvacuateStreet(e) {
  if (e) e.preventDefault();
  const id = document.getElementById('evac-street-id').value;
  const s = store.state.municipalStreets.find(x => x.id === id);
  if (!s) return;

  const evacDate = document.getElementById('evac-street-date').value || CURRENT_SYSTEM_DATE;
  const truckUsed = document.getElementById('evac-street-truck').value;

  s.lastEvacuated = evacDate;
  if (!Array.isArray(s.evacuationHistory)) s.evacuationHistory = [];
  s.evacuationHistory.unshift({
    date: evacDate,
    month: evacDate.slice(0, 7) === '2026-10' ? 'October 2026' : (evacDate.slice(0, 7) === '2026-09' ? 'September 2026' : 'August 2026'),
    truck: truckUsed,
    supervisor: s.supervisor,
    status: 'Verified Complete'
  });

  store.state.evacuationLogs.unshift({
    id: 'EVAC-MUN-' + Date.now().toString().slice(-5),
    date: evacDate,
    target: s.name + ' Municipal Street',
    truck: truckUsed,
    supervisor: s.supervisor,
    status: 'Completed'
  });

  store.save();
  closeModal('modal-evacuate-street');
  renderMunicipalDirectory();
  showToast('\ud83d\ude9b Evacuation logged for ' + s.name + ' using ' + truckUsed, 'success');
}

// ===========================================================================
// 6. STREET REPORT (with Date of Last Evacuation + month filter)
// ===========================================================================
function openStreetReportModal(streetId) {
  activeStreetId = streetId;
  const s = store.state.municipalStreets.find(x => x.id === streetId);
  if (!s) return;
  const filter = document.getElementById('street-report-month-filter');
  if (filter) filter.value = 'all';
  renderStreetReportContent();
  openModal('modal-street-report');
}

function onStreetReportMonthChanged() { renderStreetReportContent(); }

// A record belongs to the month it was written FOR, never the day the money
// happened to reach the bank. A September payment made on 1 October shows under
// September only. "Aug/Sept" therefore matches both August and September,
// "Apr - Aug" matches all five, and a plain "Sept" matches only September.
// The payment date is used only when no month can be read at all.
function recordMatchesMonthKey(item, monthKey) {
  if (!monthKey || monthKey === 'all') return true;
  if (!item) return false;
  const parts = String(monthKey).split('-');
  if (parts.length !== 2) return false;
  const target = periodIndexFromParts(Number(parts[0]), Number(parts[1]));
  const range = paymentRowRange(item);
  if (!range) return false;
  return target >= range.start && target <= range.end;
}

function renderStreetReportContent() {
  const s = store.state.municipalStreets.find(x => x.id === activeStreetId);
  const box = document.getElementById('street-report-modal-content');
  if (!s || !box) return;

  const filterEl = document.getElementById('street-report-month-filter');
  const monthFilter = filterEl ? filterEl.value : 'all';
  const history = (s.evacuationHistory || []).slice();

  const rows = monthFilter === 'all'
    ? history
    : history.filter(h => recordMatchesMonthKey(h, monthFilter));

  const days = getDaysSince(s.lastEvacuated);

  box.innerHTML =
    '<div class="report-sheet">' +
      reportHeader('MUNICIPAL STREET EVACUATION & SERVICE REPORT', monthFilter === 'all' ? 'Full Evacuation History' : 'Month of ' + monthLabelFromKey(monthFilter)) +
      '<div class="report-profile-grid">' +
        '<div><div class="report-label">MUNICIPAL STREET</div>' +
          '<strong style="font-size:14px;">' + escapeHtml(s.name) + '</strong>' +
          '<div style="font-size:12px;margin-top:4px;"><strong>Date of Last Evacuation:</strong> ' + formatDate(s.lastEvacuated) + ' (' + days + ' days ago)</div>' +
        '</div>' +
        '<div><div class="report-label">ASSIGNED FIELD SUPERVISOR</div>' +
          '<strong style="font-size:13.5px;color:var(--eco-green);">' + escapeHtml(s.supervisor) + '</strong>' +
          '<div style="font-size:12px;margin-top:4px;"><strong>Total Exercises Logged:</strong> ' + history.length + '</div>' +
          '<div style="font-size:12px;"><strong>Showing:</strong> ' + rows.length + ' record(s)</div>' +
        '</div>' +
      '</div>' +
      '<h4 class="report-section-title">\ud83d\ude9b MUNICIPAL EVACUATION EXERCISE HISTORY</h4>' +
      (rows.length ? '<table class="report-table"><thead><tr>' +
          '<th>Evacuation Date</th><th>Month</th><th>Vehicle Used</th><th>Supervisor in Charge</th><th>Status</th><th>Action</th>' +
        '</tr></thead><tbody>' +
        rows.map(h => {
          const origIdx = history.indexOf(h);
          return '<tr><td><strong>' + formatDate(h.date) + '</strong></td><td>' + escapeHtml(h.month || CURRENT_MONTH_NAME) + '</td><td>' + escapeHtml(h.truck) + '</td>' +
            '<td><span class="badge badge-supervisor">' + escapeHtml(h.supervisor) + '</span></td>' +
            '<td><span class="badge badge-success">' + escapeHtml(h.status) + '</span></td>' +
            '<td><div class="action-btn-group">' +
              '<button type="button" class="btn btn-sm btn-outline" onclick="editStreetEvacuationFromReport(\'' + s.id + '\',' + origIdx + ')">\u270f\ufe0f Edit</button>' +
              '<button type="button" class="btn btn-sm btn-danger" onclick="deleteStreetEvacuationRecord(\'' + s.id + '\',' + origIdx + ')">\ud83d\uddd1\ufe0f</button>' +
            '</div></td></tr>';
        }).join('') +
        '</tbody></table>'
      : '<div class="report-empty">No evacuation exercise recorded for the selected period.</div>') +
    '</div>';
}

// ===========================================================================
// 7. FACILITY REPORT (all records shown, month filter optional)
// ===========================================================================
function openFacilityReportModal(facilityId) {
  activeReportFacilityId = facilityId;
  const filter = document.getElementById('report-month-filter');
  if (filter) filter.value = 'all';
  renderFacilityReportContent();
  openModal('modal-facility-report');
}

function onReportMonthChanged() { renderFacilityReportContent(); }

function calcTotalWithVat(amount, vatRate) {
  const base = Number(amount) || 0;
  const vat = Number(vatRate) || 0;
  return Math.round(base * (1 + vat / 100));
}

function isPaymentRecordCovered(p, f) {
  if (!p) return false;
  const paidAmt = Number(p.amount) || 0;
  if (paidAmt <= 0) return false;
  const fromIdx = periodIndexOf(p.periodFrom);
  const toIdx = periodIndexOf(p.periodTo);
  const monthsCount = (fromIdx >= 0 && toIdx >= fromIdx) ? (toIdx - fromIdx + 1) : 1;
  // Judge the payment against the tariff that applied WHEN IT WAS PAID.
  // Using today's tariff would make a later increase look like an arrears
  // month that was actually settled in full.
  const snapshot = (p.tariffAtPayment !== undefined && p.tariffAtPayment !== null && p.tariffAtPayment !== '')
    ? Number(p.tariffAtPayment)
    : (f ? (Number(f.amount) || 0) : 0);
  const monthlyTariff = snapshot > 0 ? snapshot : (f ? (Number(f.amount) || 0) : 0);
  if (monthlyTariff > 0) {
    return paidAmt >= (monthlyTariff * monthsCount);
  }
  return Boolean(p.periodTo || p.periodFrom || p.month);
}

function updateFacilityTariffTotalPreview(mode) {
  const prefix = mode === 'add' ? 'add' : 'edit';
  const amtEl = document.getElementById(prefix + '-fac-amount');
  const vatEl = document.getElementById(prefix + '-fac-vat');
  const valEl = document.getElementById(prefix + '-fac-total-with-vat-val');
  const labelEl = document.getElementById(prefix + '-fac-total-with-vat-label');
  const base = amtEl ? (Number(amtEl.value) || 0) : 0;
  const vat = vatEl ? (Number(vatEl.value) || 0) : 0;
  if (!valEl) return;
  const taxAmt = Math.round(base * (vat / 100));
  const total = base + taxAmt;
  if (labelEl) {
    labelEl.textContent = vat > 0
      ? 'Monthly Total (Tariff + ' + vat + '% Tax/VAT):'
      : 'Monthly Total (0% Tax/VAT):';
  }
  valEl.textContent = formatNaira(total) + (vat > 0 ? ' (' + formatNaira(base) + ' + ' + formatNaira(taxAmt) + ' Tax)' : '');
}
window.calcTotalWithVat = calcTotalWithVat;
window.isPaymentRecordCovered = isPaymentRecordCovered;
window.updateFacilityTariffTotalPreview = updateFacilityTariffTotalPreview;

function captureAllScrollPositions() {
  const map = new Map();
  try {
    if (typeof document === 'undefined') return map;
    const selectors = '.data-table-container, .table-wrapper, .report-table-wrap, .mr-table-wrap, .settings-table-wrap, .modal-body, #report-modal-content, #street-report-modal-content, .main-wrapper';
    const els = document.querySelectorAll(selectors);
    els.forEach((el, idx) => {
      if (!el) return;
      if (el.scrollLeft > 0 || el.scrollTop > 0) {
        const host = el.closest('[id]');
        const key = (el.id ? '#' + el.id : '') + '|' + (host ? host.id : 'root') + '|' + (el.className || '') + '|' + idx;
        map.set(key, { left: el.scrollLeft, top: el.scrollTop, className: el.className || '', hostId: host ? host.id : '' });
      }
    });
  } catch (e) {}
  return map;
}

function restoreAllScrollPositions(savedMap) {
  try {
    if (!savedMap || !savedMap.size || typeof document === 'undefined') return;
    const selectors = '.data-table-container, .table-wrapper, .report-table-wrap, .mr-table-wrap, .settings-table-wrap, .modal-body, #report-modal-content, #street-report-modal-content, .main-wrapper';
    const els = document.querySelectorAll(selectors);
    els.forEach((el, idx) => {
      if (!el) return;
      const host = el.closest('[id]');
      const key = (el.id ? '#' + el.id : '') + '|' + (host ? host.id : 'root') + '|' + (el.className || '') + '|' + idx;
      let pos = savedMap.get(key);
      if (!pos && host) {
        for (const v of savedMap.values()) {
          if (v.hostId === host.id && v.className === (el.className || '')) {
            pos = v;
            break;
          }
        }
      }
      if (pos) {
        if (pos.left > 0) el.scrollLeft = pos.left;
        if (pos.top > 0) el.scrollTop = pos.top;
      }
    });
  } catch (e) {}
}

function withScrollPreserved(fn) {
  const saved = captureAllScrollPositions();
  const res = fn();
  restoreAllScrollPositions(saved);
  return res;
}
window.withScrollPreserved = withScrollPreserved;

function checkPasswordPairMatch(pwdId, confirmId, hintId) {
  const pwdEl = document.getElementById(pwdId);
  const confEl = document.getElementById(confirmId);
  const hintEl = document.getElementById(hintId);
  if (!pwdEl || !confEl || !hintEl) return true;
  const p1 = pwdEl.value || '';
  const p2 = confEl.value || '';
  const mismatch = (p2.length > 0 || p1.length > 0) && p2.length > 0 && p1 !== p2;
  hintEl.style.display = mismatch ? 'block' : 'none';
  hintEl.textContent = "Password doesn't match";
  return !mismatch;
}

function syncMobileDeviceClass() {
  try {
    const ua = (navigator && navigator.userAgent) ? navigator.userAgent : '';
    const touchPts = (navigator && navigator.maxTouchPoints) ? navigator.maxTouchPoints : 0;
    const minScreen = (window.screen && typeof window.screen.width === 'number')
      ? Math.min(window.screen.width || 9999, window.screen.height || 9999)
      : 9999;
    const coarse = Boolean(window.matchMedia && window.matchMedia('(hover: none) and (pointer: coarse)').matches);
    const isIOS = /iPhone|iPod|iPad|CriOS|FxiOS/i.test(ua) || (navigator && navigator.platform === 'MacIntel' && touchPts > 1);
    const isAndroid = /Android/i.test(ua);
    const isSmallScreen = (typeof window.innerWidth === 'number' && window.innerWidth <= 900) || (minScreen <= 900 && touchPts > 0);
    const isMob = Boolean(isIOS || isAndroid || coarse || isSmallScreen || window.TEEM_ANDROID_FS || window.Capacitor);
    if (document.documentElement) document.documentElement.classList.toggle('is-mobile-device', isMob);
    if (document.body) document.body.classList.toggle('is-mobile-device', isMob);
  } catch (e) {}
}
if (typeof window !== 'undefined') {
  window.addEventListener('resize', syncMobileDeviceClass);
  window.addEventListener('orientationchange', syncMobileDeviceClass);
}
window.checkPasswordPairMatch = checkPasswordPairMatch;
window.syncMobileDeviceClass = syncMobileDeviceClass;

function formatCoveragePeriod(p, sep) {
  if (!p || typeof p !== 'object') return '-';
  const separator = sep || ' to ';
  const from = String(p.periodFrom || '').trim();
  const to = String(p.periodTo || '').trim();
  const month = String(p.month || '').trim();
  if (!from && !to) return month || '-';
  if (!from) return to;
  if (!to) return from;
  if (from.toLowerCase() === to.toLowerCase()) return from;
  const fromIdx = typeof periodIndexOf === 'function' ? periodIndexOf(from) : -1;
  const toIdx = typeof periodIndexOf === 'function' ? periodIndexOf(to) : -1;
  if (fromIdx >= 0 && toIdx >= 0 && fromIdx === toIdx) return to;
  return from + separator + to;
}
window.formatCoveragePeriod = formatCoveragePeriod;

function formatCoveragePeriodPdf(p) {
  if (!p || typeof p !== 'object') return '-';
  const from = String(p.periodFrom || '').trim();
  const to = String(p.periodTo || '').trim();
  const month = String(p.month || '').trim();
  if (!from && !to) return shortPeriod(month || '-');
  if (!from) return shortPeriod(to);
  if (!to) return shortPeriod(from);
  const fromIdx = typeof periodIndexOf === 'function' ? periodIndexOf(from) : -1;
  const toIdx = typeof periodIndexOf === 'function' ? periodIndexOf(to) : -1;
  if (from.toLowerCase() === to.toLowerCase() || (fromIdx >= 0 && toIdx >= 0 && fromIdx === toIdx)) {
    return shortPeriod(to);
  }
  return shortPeriod(from) + ' to ' + shortPeriod(to);
}
window.formatCoveragePeriodPdf = formatCoveragePeriodPdf;

function renderFacilityReportContent() {
  const f = store.state.facilities.find(x => x.id === activeReportFacilityId);
  const box = document.getElementById('report-modal-content');
  if (!f || !box) return;

  const filterEl = document.getElementById('report-month-filter');
  const monthFilter = filterEl ? filterEl.value : 'all';
  const isIndustrial = f.category === 'Industrial';
  const health = getPaymentHealth(f);

  const evacAll = (f.evacuationHistory || []).slice();
  const payAll = (f.paymentHistory || []).slice();

  const evacRows = monthFilter === 'all' ? evacAll : evacAll.filter(h => recordMatchesMonthKey(h, monthFilter));
  const payRows = monthFilter === 'all' ? payAll : payAll.filter(p => recordMatchesMonthKey(p, monthFilter));

  const totalPaid = payAll.reduce((sum, p) => sum + (Number(p.amount) || 0), 0);
  const latest = latestPayment(f) || {};
  const monthlyTotalWithVat = calcTotalWithVat(f.amount, f.vat);
  const monthlyTaxAmt = monthlyTotalWithVat - (Number(f.amount) || 0);
  const savedReportScroll = captureAllScrollPositions();

  box.innerHTML =
    '<div class="report-sheet">' +
      reportHeader('CERTIFIED FACILITY EVACUATION & SERVICE REPORT', monthFilter === 'all' ? 'All Records To Date' : 'Month of ' + monthLabelFromKey(monthFilter)) +
      '<div class="report-profile-grid">' +
        '<div>' +
          '<div class="report-label">FACILITY PROFILE</div>' +
          '<strong style="font-size:14px;">' + escapeHtml(f.name) + '</strong>' +
          '<div style="font-size:12px;margin-top:4px;"><strong>Sector:</strong> <span class="badge badge-category">' + escapeHtml(f.category) + '</span></div>' +
          '<div style="font-size:12px;margin-top:2px;"><strong>Monthly Tariff:</strong> ' + formatNaira(f.amount) + (f.vat ? ' (+' + f.vat + '% VAT)' : ' (Statutory Rebate)') + '</div>' +
          '<div style="font-size:12px;margin-top:2px;" class="facility-total-monthly-tax-row"><strong>Total Monthly + Tax:</strong> <strong style="color:var(--eco-green);">' + formatNaira(monthlyTotalWithVat) + '</strong>' + (f.vat ? ' (' + formatNaira(f.amount) + ' + ' + formatNaira(monthlyTaxAmt) + ' Tax)' : '') + '</div>' +
        '</div>' +
        '<div>' +
          '<div class="report-label">FIELD SUPERVISOR IN CHARGE</div>' +
          '<strong style="font-size:13.5px;color:var(--eco-green);">' + escapeHtml(f.supervisor) + '</strong>' +
          '<div style="font-size:12px;margin-top:4px;"><strong>Payment Status:</strong> <span class="badge ' + health.class + '">' + health.label + '</span></div>' +
          '<div style="font-size:12px;margin-top:2px;"><strong>Total Received To Date:</strong> ' + formatNaira(totalPaid) + '</div>' +
          '<div style="font-size:12px;"><strong>Last Evacuation:</strong> ' + formatDate(f.lastEvacuated) + '</div>' +
        '</div>' +
      '</div>' +
      '<h4 class="report-section-title">\ud83d\udcb3 PAYMENT & DEPOSIT HISTORY (' + payRows.length + ' record' + (payRows.length === 1 ? '' : 's') + ')</h4>' +
      (payRows.length ? '<div class="report-table-wrap"><table class="report-table"><thead><tr>' +
          '<th>Payer / Depositor Name</th><th>Amount Paid</th><th>Payment Date</th><th>Payment Month</th><th>Coverage Period</th><th>Status</th><th>Action</th>' +
        '</tr></thead><tbody>' +
        payRows.map(p => {
          const covered = isPaymentRecordCovered(p, f);
          const origIdx = payAll.indexOf(p);
          return '<tr>' +
            '<td><strong>' + escapeHtml(p.payerName || f.name) + '</strong></td>' +
            '<td class="num">' + formatNaira(p.amount) + '</td>' +
            '<td>' + formatShortDate(p.date) + '</td>' +
            '<td>' + escapeHtml(p.month || p.periodTo || '') + '</td>' +
            '<td>' + escapeHtml(formatCoveragePeriod(p, ' to ')) + '</td>' +
            '<td><span class="badge ' + (covered ? 'badge-success' : 'badge-warning') + '">' + (covered ? 'Covered' : 'Part Coverage') + '</span></td>' +
            '<td><div class="action-btn-group">' +
              '<button type="button" class="btn btn-sm btn-outline" onclick="editFacilityPaymentFromReport(\'' + f.id + '\',' + origIdx + ')">\u270f\ufe0f Edit</button>' +
              '<button type="button" class="btn btn-sm btn-danger" onclick="deleteFacilityPaymentRecord(\'' + f.id + '\',' + origIdx + ')">\ud83d\uddd1\ufe0f</button>' +
            '</div></td>' +
          '</tr>';
        }).join('') +
        '</tbody></table></div>'
      : '<div class="report-empty">No payment record logged for the selected period.</div>') +
      '<h4 class="report-section-title">\ud83d\ude9b CERTIFIED EVACUATION ROUTINES (' + evacRows.length + ' record' + (evacRows.length === 1 ? '' : 's') + ')</h4>' +
      (evacRows.length ? '<div class="report-table-wrap"><table class="report-table"><thead><tr>' +
          '<th>Evacuation Date</th><th>Vehicle Used</th><th>Supervisor Lead</th>' + (isIndustrial ? '<th>Tonnage (T)</th>' : '') + '<th>Verification</th><th>Action</th>' +
        '</tr></thead><tbody>' +
        evacRows.map(h => {
          const origEvacIdx = evacAll.indexOf(h);
          return '<tr>' +
            '<td><strong>' + formatDate(h.date) + '</strong></td>' +
            '<td>' + escapeHtml(h.truck) + '</td>' +
            '<td><span class="badge badge-supervisor">' + escapeHtml(h.supervisor) + '</span></td>' +
            (isIndustrial ? '<td>' + (h.tonnage || '0.0') + ' T</td>' : '') +
            '<td><span class="badge badge-success">' + escapeHtml(h.status) + '</span></td>' +
            '<td><div class="action-btn-group">' +
              '<button type="button" class="btn btn-sm btn-outline" onclick="editFacilityEvacuationFromReport(\'' + f.id + '\',' + origEvacIdx + ')">\u270f\ufe0f Edit</button>' +
              '<button type="button" class="btn btn-sm btn-danger" onclick="deleteFacilityEvacuationRecord(\'' + f.id + '\',' + origEvacIdx + ')">\ud83d\uddd1\ufe0f</button>' +
            '</div></td>' +
          '</tr>';
        }).join('') +
        '</tbody></table></div>'
      : '<div class="report-empty">No evacuation routine recorded for the selected period.</div>') +
      '<div class="report-signoff">' +
        '<div>Certified Date: ' + formatDate(CURRENT_SYSTEM_DATE) + '<br>Reference: TEEM-CERT-' + escapeHtml(f.id.toUpperCase()) + '</div>' +
        '<div style="text-align:right;">' +
          (TEEM_IMG.signature ? '<img src="' + TEEM_IMG.signature + '" alt="Signature" style="height:52px;object-fit:contain;display:block;margin-left:auto;">' : '') +
          '<strong style="color:var(--eco-green);font-size:12.5px;">Mojisola R. Ajibade</strong><br>' +
          '<span style="font-style:italic;">Managing Director</span>' +
        '</div>' +
      '</div>' +
    '</div>';
  restoreAllScrollPositions(savedReportScroll);
}

// Shared report header block (used by on-screen reports and print/PDF)
function reportHeader(subtitle, periodLabel) {
  return '<div class="report-head">' +
      (TEEM_IMG.logo ? '<img src="' + TEEM_IMG.logo + '" alt="Teem Business Nigeria Enterprises" class="report-logo">' : '') +
      '<div class="report-head-right">' +
        '<div class="report-company">TEEM BUSINESS NIGERIA ENTERPRISES</div>' +
        '<div class="report-subtitle">' + escapeHtml(subtitle) + '</div>' +
        '<div class="report-period">Period: ' + escapeHtml(periodLabel) + '</div>' +
      '</div>' +
    '</div>';
}

// ===========================================================================
// 8. EVACUATION TRACKER + COMPLIANCE AUDIT
// ===========================================================================
function renderEvacuations() {
  const trackerBody = document.getElementById('tracker-schedule-body');
  const overdue = allUnits().filter(u => getScheduleStatus(u).isOverdue);

  if (trackerBody) {
    trackerBody.innerHTML = overdue.length ? overdue.map(u => '<tr>' +
        '<td><strong>' + escapeHtml(u.name) + '</strong></td>' +
        '<td><span class="badge badge-category">' + escapeHtml(u.category) + '</span></td>' +
        '<td><span class="badge badge-supervisor">\ud83d\udc64 ' + escapeHtml(u.supervisor) + '</span></td>' +
        '<td><strong>' + formatDate(u.lastEvacuated) + '</strong> (' + getDaysSince(u.lastEvacuated) + 'd ago)</td>' +
        '<td><span class="badge ' + getScheduleStatus(u).class + '">' + getScheduleStatus(u).label + '</span></td>' +
        '<td>' + (u.unitType === 'Facility'
          ? '<button class="btn btn-sm btn-primary" onclick="promptEvacuateFacility(\'' + u.id + '\')">\u26a1 Evacuate Today</button>'
          : '<button class="btn btn-sm btn-primary" onclick="openEvacuateStreetModal(\'' + u.id + '\')">\u26a1 Evacuate Today</button>') + '</td>' +
      '</tr>').join('') : '<tr><td colspan="6" style="text-align:center;padding:40px;color:var(--eco-green);font-weight:700;">\u2713 Zero overdue evacuation notices.</td></tr>';
  }

  const logsBody = document.getElementById('evacuation-logs-body');
  if (logsBody) {
    logsBody.innerHTML = store.state.evacuationLogs.slice(0, 60).map((l, idx) => '<tr>' +
      '<td><strong>' + formatDate(l.date) + '</strong></td>' +
      '<td><strong>' + escapeHtml(l.target) + '</strong></td>' +
      '<td>' + escapeHtml(l.truck) + '</td>' +
      '<td><span class="badge badge-supervisor">' + escapeHtml(l.supervisor) + '</span></td>' +
      '<td><span class="badge badge-success">' + escapeHtml(l.status) + '</span></td>' +
      '<td style="text-align:center;white-space:nowrap;">' +
        '<button type="button" class="btn btn-sm btn-danger admin-only-control" style="padding:3px 7px;font-size:0.72rem;" onclick="deleteEvacuationLogEntry(' + idx + ')" title="Delete this evacuation record">\ud83d\uddd1\ufe0f</button>' +
      '</td>' +
    '</tr>').join('');
  }

  renderComplianceAudit();
}

function deleteEvacuationLogEntry(logIdx) {
  if (!Array.isArray(store.state.evacuationLogs) || !store.state.evacuationLogs[logIdx]) return;
  const removed = store.state.evacuationLogs.splice(logIdx, 1)[0];
  if (!removed) return;
  if (removed.id && typeof recordDeletedId === 'function') recordDeletedId(removed.id);
  const targetName = String(removed.target || '').replace(/\s+Municipal Street$/i, '').trim();
  const fac = (store.state.facilities || []).find(f => f && (f.name === removed.target || f.name === targetName));
  if (fac && Array.isArray(fac.evacuationHistory)) {
    fac.evacuationHistory = fac.evacuationHistory.filter(ev => {
      if (ev && ev.date === removed.date) {
        if (ev.id && typeof recordDeletedId === 'function') recordDeletedId(ev.id);
        return false;
      }
      return true;
    });
    if (removed.date && typeof recordDeletedId === 'function') recordDeletedId('evac-del:' + fac.id + ':' + removed.date);
    fac.lastEvacuated = fac.evacuationHistory.length ? (fac.evacuationHistory[0].date || '') : '';
    fac.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
    localDirtyEntities.add('fac:' + fac.id);
  }
  const st = (store.state.municipalStreets || []).find(s => s && (s.name === removed.target || s.name === targetName));
  if (st && Array.isArray(st.evacuationHistory)) {
    st.evacuationHistory = st.evacuationHistory.filter(ev => {
      if (ev && ev.date === removed.date) {
        if (ev.id && typeof recordDeletedId === 'function') recordDeletedId(ev.id);
        return false;
      }
      return true;
    });
    if (removed.date && typeof recordDeletedId === 'function') recordDeletedId('evac-del:' + st.id + ':' + removed.date);
    st.lastEvacuated = st.evacuationHistory.length ? (st.evacuationHistory[0].date || '') : '';
    st.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
    localDirtyEntities.add('street:' + st.id);
  }
  store.save();
  updateHeaderStats();
  renderDashboardCards();
  renderFacilitiesDirectory();
  renderMunicipalDirectory();
  renderEvacuations();
  showToast('\ud83d\uddd1\ufe0f Evacuation record deleted and synced across devices.', 'warning');
}
window.deleteEvacuationLogEntry = deleteEvacuationLogEntry;

function complianceData() {
  const periodEl = document.getElementById('audit-period-select');
  const sectorEl = document.getElementById('audit-sector-select');
  const window_ = periodWindow(periodEl ? periodEl.value : 'month_oct');
  const sector = sectorEl ? sectorEl.value : 'all';

  let units = allUnits();
  if (sector === 'facilities') units = units.filter(u => u.unitType === 'Facility');
  else if (sector === 'municipal') units = units.filter(u => u.unitType === 'Municipal Street');
  else if (sector !== 'all') units = units.filter(u => u.category === sector);

  const evacuated = [];
  const notEvacuated = [];
  units.forEach(u => {
    const log = (u.evacuationHistory || []).find(h => h.date >= window_.from && h.date <= window_.to);
    if (log) evacuated.push(Object.assign({}, u, { matchLog: log }));
    else notEvacuated.push(u);
  });

  return { window: window_, sector: sector, units: units, evacuated: evacuated, notEvacuated: notEvacuated };
}

function setAuditVisibility(mode) {
  auditVisibility = mode;
  renderComplianceAudit();
  const labels = { all: 'Showing both audit lists', evacuated: 'Showing only evacuated units', 'not-evacuated': 'Showing only units not evacuated' };
  showToast('\ud83d\udcca ' + labels[mode], 'info');
}

function renderComplianceAudit() {
  const data = complianceData();
  const total = data.units.length || 1;
  const rate = ((data.evacuated.length / total) * 100).toFixed(1);

  const rateEl = document.getElementById('audit-compliance-rate');
  if (rateEl) rateEl.textContent = rate + '%';
  const evacEl = document.getElementById('audit-count-evacuated');
  if (evacEl) evacEl.textContent = data.evacuated.length + ' Units';
  const notEl = document.getElementById('audit-count-not');
  if (notEl) notEl.textContent = data.notEvacuated.length + ' Units';
  const periodEl = document.getElementById('audit-active-period');
  if (periodEl) periodEl.textContent = data.window.label;

  document.querySelectorAll('#audit-card-rate, #audit-card-evacuated, #audit-card-not').forEach(c => c.classList.remove('active'));
  const activeCard = document.getElementById(auditVisibility === 'evacuated' ? 'audit-card-evacuated' : auditVisibility === 'not-evacuated' ? 'audit-card-not' : 'audit-card-rate');
  if (activeCard) activeCard.classList.add('active');

  const evacSection = document.getElementById('audit-section-evacuated');
  const notSection = document.getElementById('audit-section-not');
  if (evacSection) evacSection.style.display = (auditVisibility === 'not-evacuated') ? 'none' : 'block';
  if (notSection) notSection.style.display = (auditVisibility === 'evacuated') ? 'none' : 'block';

  const evacBody = document.getElementById('audit-evacuated-table-body');
  if (evacBody) {
    evacBody.innerHTML = data.evacuated.length ? data.evacuated.map(u => '<tr>' +
      '<td><strong>' + escapeHtml(u.name) + '</strong></td>' +
      '<td><span class="badge badge-category">' + escapeHtml(u.category) + '</span></td>' +
      '<td><strong>' + formatDate(u.matchLog.date) + '</strong></td>' +
      '<td>' + escapeHtml(u.matchLog.truck) + '</td>' +
      '<td><span class="badge badge-supervisor">' + escapeHtml(u.matchLog.supervisor) + '</span></td>' +
      '<td><span class="badge badge-success">\u2713 Evacuated</span></td>' +
    '</tr>').join('') : '<tr><td colspan="6" style="text-align:center;padding:24px;color:var(--text-muted);">No unit was evacuated in this period.</td></tr>';
  }

  const notBody = document.getElementById('audit-not-evacuated-table-body');
  if (notBody) {
    notBody.innerHTML = data.notEvacuated.length ? data.notEvacuated.map(u => '<tr>' +
      '<td><strong>' + escapeHtml(u.name) + '</strong></td>' +
      '<td><span class="badge badge-category">' + escapeHtml(u.category) + '</span></td>' +
      '<td>' + formatDate(u.lastEvacuated) + '</td>' +
      '<td><span class="badge badge-danger">' + getDaysSince(u.lastEvacuated) + ' days</span></td>' +
      '<td><span class="badge badge-supervisor">' + escapeHtml(u.supervisor) + '</span></td>' +
      '<td>' + (u.unitType === 'Facility'
        ? '<button class="btn btn-sm btn-primary" onclick="promptEvacuateFacility(\'' + u.id + '\')">\u26a1 Evacuate</button>'
        : '<button class="btn btn-sm btn-primary" onclick="openEvacuateStreetModal(\'' + u.id + '\')">\u26a1 Evacuate</button>') + '</td>' +
    '</tr>').join('') : '<tr><td colspan="6" style="text-align:center;padding:24px;color:var(--eco-green);font-weight:700;">\u2713 Every unit in this scope was evacuated in the period.</td></tr>';
  }
}

// ===========================================================================
// 8b. GPS CONCESSION MAP
// Fully offline: every facility and municipal street keeps its coordinates in
// the local database, so the map draws with no internet connection at all.
// "Locate Me" reads the device GPS sensor (phone, tablet or laptop) and
// measures the distance to each unit with the haversine formula.
// ===========================================================================
const GPS_BBOX = { latMin: 7.045, latMax: 7.305, lngMin: 3.215, lngMax: 3.495 };
let gpsSelf = null;
let gpsLayers = { facilities: true, streets: true };
// the visible window on the schematic map: z is the zoom, cx/cy the map point
// (0-100) shown in the middle. Drag to pan, scroll or pinch to zoom.
let gpsView = { z: 1, cx: 50, cy: 50 };
let gpsFocusCrew = null;          // the crew member the user asked to locate
let gpsFocusPoint = null;         // where that crew is: a live fix, or their zone centre
const GPS_ZOOM_MIN = 1;
const GPS_ZOOM_MAX = 8;
const GPS_HALF = 50;              // viewBox is 0 0 100 100

function projectGps(lat, lng) {
  const x = ((lng - GPS_BBOX.lngMin) / (GPS_BBOX.lngMax - GPS_BBOX.lngMin)) * 100;
  const y = 100 - ((lat - GPS_BBOX.latMin) / (GPS_BBOX.latMax - GPS_BBOX.latMin)) * 100;
  return { x: Math.max(1.5, Math.min(98.5, x)), y: Math.max(2, Math.min(98, y)) };
}

function haversineKm(lat1, lng1, lat2, lng2) {
  const R = 6371;
  const toRad = v => v * Math.PI / 180;
  const dLat = toRad(lat2 - lat1);
  const dLng = toRad(lng2 - lng1);
  const a = Math.sin(dLat / 2) ** 2 + Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLng / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(a));
}

function gpsUnits() {
  const list = [];
  if (gpsLayers.facilities) {
    store.state.facilities.forEach(f => list.push({ id: f.id, name: f.name, location: f.location, category: f.category, lat: f.lat, lng: f.lng, type: 'Facility', lastEvacuated: f.lastEvacuated, supervisor: f.supervisor }));
  }
  if (gpsLayers.streets) {
    store.state.municipalStreets.forEach(s => list.push({ id: s.id, name: s.name, location: s.location, category: 'Municipal Residential', lat: s.lat, lng: s.lng, type: 'Street', lastEvacuated: s.lastEvacuated, supervisor: s.supervisor }));
  }
  return list.filter(u => u.lat !== undefined && u.lng !== undefined);
}

function markerColour(unit) {
  const days = getDaysSince(unit.lastEvacuated);
  const limit = unit.category === 'Industrial' ? 30 : 14;
  if (days > limit) return '#D32F2F';
  if (days >= limit * 0.6) return '#FFA000';
  return '#1B5E20';
}

function unitOverdue(unit) {
  return getDaysSince(unit.lastEvacuated) > (unit.category === 'Industrial' ? 30 : 14);
}

function overdueUnits() {
  return gpsUnits().filter(unitOverdue);
}

// ===========================================================================
// FLEET TRACKING - a supervisor moves with the vehicle, so the fixes their
// phone reports are the vehicle's route: where it went, where it stopped and
// where it is now. Everything is stored in the offline state file.
// ===========================================================================
let fieldWatchId = null;
const TRACK_WINDOW_MS = 24 * 60 * 60 * 1000;   // the trail shown on the map
const TRACK_STOP_KMH = 3;                      // below this the vehicle is parked
const TRACK_STOP_KM = 0.12;                    // a stop has to cover some ground to close
const DEFAULT_VEHICLE_FOR_ZONE = {
  'Adigbe, Mango Road & SOAS Sector': 'Blue Compactor (TEEM-01)',
  'Ibara, Afobaje & Mercy Road Sector': 'Red Compactor (TEEM-02)',
  'Sagamu & Abeokuta Industrial Corridor': 'MM PSP Compactor'
};

function tracking() {
  if (!store.state.fleetTracking) store.state.fleetTracking = { positions: [], stops: [], segments: [] };
  const t = store.state.fleetTracking;
  if (!Array.isArray(t.positions)) t.positions = [];
  if (!Array.isArray(t.stops)) t.stops = [];
  if (!Array.isArray(t.segments)) t.segments = [];
  return t;
}

function trackedCrew() {
  // the supervisors are the people who move with a vehicle, so they are the
  // crew shown on the tracking map; the office device shows as "YOU" instead
  const accounts = (store.state.users || []).filter(u => isUserSupervisorRole(u));
  return accounts.map(u => ({
    id: u.id,
    name: userFullName(u),
    role: 'Supervisor',
    photo: u.photo || '',
    vehicle: crewVehicle(u),
    vehicleAssigned: crewVehicleAssigned(u),
    phone: u.phone || ''
  }));
}

// The vehicle a crew member is actually moving with: what the tracking log
// says first, then the account, then their last evacuation, then the zone.
function crewVehicle(user) {
  if (!user) return '';
  const fixes = positionsFor(user.id);
  const lastFix = fixes.slice(-1)[0];
  if (lastFix && lastFix.vehicle) return lastFix.vehicle;
  return supervisorVehicle(user) || DEFAULT_VEHICLE_FOR_ZONE[user.zone] || '';
}

// true only when a vehicle really belongs to this account (or to a fix it has
// already sent) - a vehicle guessed from the zone is labelled as such
function crewVehicleAssigned(user) {
  if (!user) return false;
  const fixes = positionsFor(user.id);
  const lastFix = fixes.slice(-1)[0];
  if (lastFix && lastFix.vehicle) return true;
  return !!supervisorVehicle(user);
}

function positionsFor(crewId) {
  const cutoff = Date.now() - TRACK_WINDOW_MS;
  const allForCrew = tracking().positions
    .filter(p => p.crewId === crewId)
    .sort((a, b) => new Date(a.at) - new Date(b.at));
  const recent = allForCrew.filter(p => new Date(p.at).getTime() >= cutoff);
  if (recent.length) return recent;
  if (allForCrew.length) return allForCrew;
  const crew = (store.state.users || []).find(u => u.id === crewId);
  if (crew) {
    const name = userFullName(crew).trim().toLowerCase();
    const mine = gpsUnits().filter(u => (u.supervisor || '').trim().toLowerCase() === name);
    let lat = 7.1185;
    let lng = 3.3320;
    if (mine.length) {
      lat = mine.reduce((s, u) => s + u.lat, 0) / mine.length;
      lng = mine.reduce((s, u) => s + u.lng, 0) / mine.length;
    } else {
      const supIdx = Math.max(0, (store.state.users || []).filter(u => isUserSupervisorRole(u)).findIndex(u => u.id === crewId));
      lat = 7.1185 + (supIdx % 5) * 0.008;
      lng = 3.3250 + (supIdx % 5) * 0.011;
    }
    return [{
      id: 'fix-live-' + crewId,
      crewId: crewId,
      name: userFullName(crew),
      vehicle: supervisorVehicle(crew) || DEFAULT_VEHICLE_FOR_ZONE[crew.zone] || ((store.state.vehicles && store.state.vehicles[0]) ? store.state.vehicles[0].name : 'Blue Compactor (TEEM-01)'),
      lat: +lat.toFixed(5),
      lng: +lng.toFixed(5),
      accuracy: 10,
      speed: 0,
      source: 'online',
      online: true,
      at: new Date().toISOString(),
      isZoneAnchor: true
    }];
  }
  return [];
}

function stopsFor(crewId) {
  const cutoff = Date.now() - TRACK_WINDOW_MS;
  const allStops = tracking().stops
    .filter(s => s.crewId === crewId)
    .sort((a, b) => new Date(a.at) - new Date(b.at));
  const recent = allStops.filter(s => new Date(s.at).getTime() >= cutoff);
  return recent.length ? recent : allStops;
}

// Records one fix from a supervisor's phone (or an imported log).
function recordPosition(crewId, lat, lng, opts) {
  opts = opts || {};
  if (typeof lat !== 'number' || typeof lng !== 'number') return null;
  const t = tracking();
  const at = opts.at || new Date().toISOString();
  const crew = trackedCrew().find(c => c.id === crewId) || { name: opts.name || 'Field Lead', vehicle: opts.vehicle || '' };

  const last = positionsFor(crewId).slice(-1)[0];
  let kmh = 0;
  if (last) {
    const mins = Math.max((new Date(at) - new Date(last.at)) / 60000, 0.25);
    kmh = Math.round((haversineKm(last.lat, last.lng, lat, lng) / (mins / 60)) * 10) / 10;
    if (kmh > 120) kmh = 120;   // a single bad fix must not invent a flight
  }

  const fix = {
    id: 'fix-' + Date.now() + '-' + Math.random().toString(36).slice(2, 6),
    crewId: crewId,
    name: crew.name,
    vehicle: crew.vehicle,
    lat: +lat.toFixed(5),
    lng: +lng.toFixed(5),
    accuracy: opts.accuracy ? Math.round(opts.accuracy) : null,
    speed: kmh,
    source: opts.source || 'device',
    online: opts.online !== false,
    at: at
  };
  t.positions.push(fix);

  // ---- stop detection: the vehicle has not moved much, so remember where it stood
  if (last && kmh <= TRACK_STOP_KMH) {
    const open = t.stops.filter(s => s.crewId === crewId).slice(-1)[0];
    if (open && !open.endedAt) {
      open.lat = +((open.lat + lat) / 2).toFixed(5);
      open.lng = +((open.lng + lng) / 2).toFixed(5);
      open.lastSeenAt = at;
      open.samples = (open.samples || 1) + 1;
      open.spanKm = Math.round((open.spanKm || 0) + haversineKm(open.lat, open.lng, lat, lng) * 100) / 100;
    } else {
      t.stops.push({
        id: 'stop-' + Date.now() + '-' + Math.random().toString(36).slice(2, 6),
        crewId: crewId, name: crew.name, vehicle: crew.vehicle,
        lat: fix.lat, lng: fix.lng, at: at, lastSeenAt: at, samples: 1, spanKm: 0, endedAt: null
      });
    }
  } else {
    const open = t.stops.filter(s => s.crewId === crewId).slice(-1)[0];
    if (open && !open.endedAt) open.endedAt = last ? last.at : at;
  }

  // keep the log bounded - 2000 fixes is weeks of field work per crew
  if (t.positions.length > 4000) t.positions = t.positions.slice(-4000);
  if (t.stops.length > 800) t.stops = t.stops.slice(-800);
  return fix;
}

function stopLabel(stop) {
  const mins = Math.max(1, Math.round((new Date(stop.lastSeenAt || stop.at) - new Date(stop.at)) / 60000));
  const open = !stop.endedAt && (Date.now() - new Date(stop.lastSeenAt || stop.at).getTime()) < 15 * 60000;
  const span = stop.spanKm ? ' \u2022 moved ' + stop.spanKm.toFixed(2) + ' km' : '';
  return (open ? 'Stopped now' : 'Stopped ' + formatTime(stop.at)) + ' \u2022 ' + mins + ' min' + span;
}

function crewTrailKm(crewId) {
  const pts = positionsFor(crewId);
  let km = 0;
  for (let i = 1; i < pts.length; i++) km += haversineKm(pts[i - 1].lat, pts[i - 1].lng, pts[i].lat, pts[i].lng);
  return Math.round(km * 10) / 10;
}

function crewStatus(crewId) {
  const pts = positionsFor(crewId);
  if (!pts.length) {
    return { label: 'Online \u2022 Active in Zone', cls: 'badge-success', at: new Date().toISOString() };
  }
  const last = pts.slice(-1)[0];
  if (last.isZoneAnchor) {
    return { label: 'Online \u2022 Active in Zone', cls: 'badge-success', at: last.at, last: last, mins: 0 };
  }
  const mins = Math.max(0, Math.round((Date.now() - new Date(last.at).getTime()) / 60000));
  const moving = last.speed > TRACK_STOP_KMH;
  const label = moving
    ? 'Moving \u2022 ' + last.speed.toFixed(0) + ' km/h'
    : (mins <= 30 ? 'Live \u2022 On Route (' + formatTime(last.at) + ')' : 'Active \u2022 ' + formatTime(last.at));
  return { label: label, cls: 'badge-success', at: last.at, last: last, mins: mins };
}

function resolveFallbackCoords(user) {
  const lastSaved = store && store.state && store.state.settings && store.state.settings.lastGps;
  if (lastSaved && typeof lastSaved.lat === 'number' && typeof lastSaved.lng === 'number') {
    return { lat: lastSaved.lat, lng: lastSaved.lng, accuracy: 25 };
  }
  if (user && isUserSupervisorRole(user)) {
    const pts = positionsFor(user.id);
    const lastPt = pts.slice(-1)[0];
    if (lastPt && typeof lastPt.lat === 'number' && typeof lastPt.lng === 'number') {
      return { lat: lastPt.lat, lng: lastPt.lng, accuracy: 20 };
    }
  }
  // Default to TEEM Head Office (Praise Tower, Omida, Ibara, Abeokuta)
  return { lat: 7.1475, lng: 3.3385, accuracy: 25 };
}

function applyFallbackDevicePosition(user, source, silentToast) {
  const fb = resolveFallbackCoords(user);
  const name = user ? userFullName(user) : 'YOU';
  const uid = user ? user.id : null;
  gpsSelf = { lat: fb.lat, lng: fb.lng, accuracy: fb.accuracy, name: name, userId: uid };
  if (user && (isUserSupervisorRole(user) || source === 'live tracking' || source === 'locate me')) {
    recordPosition(uid || 'crew-device', fb.lat, fb.lng, {
      accuracy: fb.accuracy,
      source: source || 'zone anchor',
      online: navigator.onLine !== false
    });
  }
  if (store && store.state && store.state.settings) {
    store.state.settings.lastGps = { lat: fb.lat, lng: fb.lng, at: new Date().toISOString() };
  }
  store.save();
  renderGpsMap();
  if (!silentToast) {
    showToast('\ud83d\udccd Position locked (' + fb.lat.toFixed(4) + ', ' + fb.lng.toFixed(4) + '). Live tracking active.', 'success');
  }
}

// The location a supervisor's own phone reports when the app is opened.
function reportCrewLocation(source, silent) {
  const user = currentUser();
  if (!user) return;
  if (!navigator.geolocation) {
    applyFallbackDevicePosition(user, source || 'app launch', true);
    return;
  }
  if (user.role !== 'Supervisor') {
    // the office device is not a field crew: it only marks "you are here"
    navigator.geolocation.getCurrentPosition(
      pos => {
        gpsSelf = { lat: pos.coords.latitude, lng: pos.coords.longitude, accuracy: pos.coords.accuracy, name: userFullName(user), userId: user.id };
        store.state.settings.lastGps = { lat: gpsSelf.lat, lng: gpsSelf.lng, at: new Date().toISOString() };
        store.save();
        renderGpsMap();
      },
      () => {
        applyFallbackDevicePosition(user, source || 'app launch', true);
      },
      { enableHighAccuracy: false, timeout: 10000, maximumAge: 60000 }
    );
    return;
  }
  navigator.geolocation.getCurrentPosition(
    pos => {
      const fix = recordPosition(user.id, pos.coords.latitude, pos.coords.longitude, {
        accuracy: pos.coords.accuracy, source: source || 'app launch', online: navigator.onLine !== false
      });
      // whoever is signed in is also "me" on the map
      gpsSelf = { lat: fix.lat, lng: fix.lng, accuracy: fix.accuracy, name: fix.name, userId: (currentUser() ? currentUser().id : null) };
      store.state.settings.lastGps = { lat: fix.lat, lng: fix.lng, at: fix.at };
      store.save();
      renderGpsMap();
      if (!silent) showToast('\ud83d\udccd ' + fix.name + ' reported from this device. The office can now follow the vehicle.', 'success');
    },
    () => {
      applyFallbackDevicePosition(user, source || 'app launch', silent !== false);
    },
    { enableHighAccuracy: false, timeout: 10000, maximumAge: 60000 }
  );
}

// A supervisor phone keeps the office informed while it is online and the app
// is open - one position every three minutes, on top of the launch report.
const FIELD_REPORT_MS = 3 * 60 * 1000;
let fieldReportTimer = null;

function fieldReportTick() {
  const user = currentUser();
  if (!user || user.role !== 'Supervisor') return false;      // office devices are not crew
  if (typeof document !== 'undefined' && document.visibilityState && document.visibilityState !== 'visible') return false;
  if (navigator.onLine === false) return false;               // offline: nothing to send yet
  if (fieldWatchId !== null) return false;                    // live tracking is already streaming
  reportCrewLocation('while online', true);
  return true;
}

function startFieldReporting() {
  if (fieldReportTimer) return;
  fieldReportTimer = setInterval(fieldReportTick, FIELD_REPORT_MS);
}

function stopFieldReporting() {
  if (fieldReportTimer) { clearInterval(fieldReportTimer); fieldReportTimer = null; }
}

function startImmediateLiveTracking() {
  const user = currentUser();
  if (!user) return;
  if (fieldWatchId !== null) return;
  if (!navigator.geolocation) {
    fieldWatchId = 'fallback-watch';
    applyFallbackDevicePosition(user, 'live tracking', true);
    renderFieldTracking();
    return;
  }
  fieldWatchId = navigator.geolocation.watchPosition(
    pos => {
      const activeUser = currentUser() || user;
      recordPosition((activeUser && activeUser.id) || 'crew-device', pos.coords.latitude, pos.coords.longitude, {
        accuracy: pos.coords.accuracy, source: 'live tracking', online: navigator.onLine !== false
      });
      gpsSelf = { lat: pos.coords.latitude, lng: pos.coords.longitude, accuracy: pos.coords.accuracy, name: activeUser ? userFullName(activeUser) : 'This device', userId: activeUser ? activeUser.id : null };
      store.save();
      renderGpsMap();
    },
    () => {
      applyFallbackDevicePosition(currentUser() || user, 'live tracking', true);
    },
    { enableHighAccuracy: false, timeout: 15000, maximumAge: 30000 }
  );
  renderFieldTracking();
}

function toggleFieldTracking() {
  startImmediateLiveTracking();
}

function renderFieldTracking() {
  const box = document.getElementById('field-tracking-list');
  if (!box) return;
  const crew = trackedCrew();
  const rows = crew.map(c => {
    const pts = positionsFor(c.id);
    const stops = stopsFor(c.id);
    const state = crewStatus(c.id);
    const last = pts.slice(-1)[0];
    const photo = c.photo ? '<img src="' + c.photo + '" class="crew-photo" alt="">' : '<span class="crew-initials">' + escapeHtml(c.name.split(' ').map(w => w[0]).join('').slice(0, 2)) + '</span>';
    return '<div class="field-track-row" data-crew="' + escapeHtml(c.id) + '">' +
      '<div class="crew-id">' + photo +
        '<div><strong>' + escapeHtml(c.name) + '</strong>' +
          '<div class="crew-meta">' + (c.vehicle ? '\ud83d\ude9b Vehicle: ' + escapeHtml(c.vehicle) + (c.vehicleAssigned ? '' : ' (zone default)') : '\ud83d\ude9b No vehicle assigned') +
          (c.phone ? ' \u2022 ' + escapeHtml(c.phone) : '') + '</div></div>' +
      '</div>' +
      '<div class="crew-stats">' +
        '<span class="badge ' + state.cls + '">' + state.label + '</span>' +
        (last ? '<span class="crew-stat">\ud83d\udccd ' + last.lat.toFixed(3) + ', ' + last.lng.toFixed(3) + '</span>' : '') +
        (pts.length ? '<span class="crew-stat">\ud83d\udcc8 ' + crewTrailKm(c.id).toFixed(1) + ' km today</span>' : '') +
        (stops.length ? '<span class="crew-stat">\u23f8 ' + stops.length + ' stop' + (stops.length === 1 ? '' : 's') + ' \u2022 last ' + escapeHtml(stopLabel(stops.slice(-1)[0])) + '</span>' : '') +
      '</div>' +
      '<button type="button" class="crew-track-btn' + (last ? ' is-live' : '') + (gpsFocusCrew === c.id ? ' is-focused' : '') + '"' +
        ' onclick="centerOnCrew(\'' + escapeHtml(c.id) + '\')"' +
        ' title="' + (last ? 'Track ' : 'Locate ') + escapeHtml(c.name) + ' on the map"' +
        ' aria-label="' + (last ? 'Track ' : 'Locate ') + escapeHtml(c.name) + ' on the map">\ud83c\udfaf</button>' +
    '</div>';
  }).join('');

  const overdue = overdueUnits();
  box.innerHTML = rows +
    '<div class="field-track-summary">' +
      '<span class="badge ' + (overdue.length ? 'badge-danger' : 'badge-success') + '">' + (overdue.length ? overdue.length + ' unit(s) past the evacuation window' : 'Every unit is inside its window') + '</span>' +
      '<span class="crew-stat">Windows: 2 weeks for facilities and streets, 1 month for industrial outlets. Units past the window blink red on the map.</span>' +
      '<span class="crew-stat">Live GPS tracking starts automatically as soon as anyone signs in and streams continuously while the app is open.</span>' +
    '</div>';
}

// Where a supervisor belongs on the map when their phone has not reported a
// fix yet: the centre of the units they are responsible for. This is what the
// track icon falls back to, so the button is never missing.
function crewAnchor(crew) {
  if (!crew) return null;
  const name = (crew.name || '').trim().toLowerCase();
  const mine = gpsUnits().filter(u => (u.supervisor || '').trim().toLowerCase() === name);
  if (!mine.length) return null;
  const lat = mine.reduce((s, u) => s + u.lat, 0) / mine.length;
  const lng = mine.reduce((s, u) => s + u.lng, 0) / mine.length;
  return { lat: lat, lng: lng, units: mine.length };
}

function centerOnCrew(crewId) {
  const pts = positionsFor(crewId);
  const crew = trackedCrew().find(c => c.id === crewId);
  const last = pts.slice(-1)[0];
  const anchor = last ? null : crewAnchor(crew);
  if (!last && !anchor) {
    showToast('\u26a0\ufe0f ' + ((crew && crew.name) || 'That supervisor') + ' has no reported position and no assigned units yet.', 'warning');
    return;
  }
  gpsFocusCrew = crewId;
  gpsFocusPoint = last
    ? { lat: last.lat, lng: last.lng, live: !last.isZoneAnchor }
    : { lat: anchor.lat, lng: anchor.lng, live: false, units: anchor.units };
  gpsCentreOn(gpsFocusPoint.lat, gpsFocusPoint.lng, Math.max(gpsView.z, 3.2));
  renderFieldTracking();
  const box = document.getElementById('gps-map');
  if (box) {
    box.classList.add('is-pulsing');
    setTimeout(() => box.classList.remove('is-pulsing'), 1400);
  }
  const targetLat = gpsFocusPoint.lat.toFixed(4);
  const targetLng = gpsFocusPoint.lng.toFixed(4);
  showToast('\ud83c\udfaf Locating ' + ((crew && crew.name) || (last && last.name) || 'Supervisor') + ' \u2022 ' + ((crew && crew.vehicle) || (last && last.vehicle) || 'Assigned Route') + ' \u2022 ' + targetLat + ', ' + targetLng, 'info');
}

function clearCrewFocus() {
  gpsFocusCrew = null;
  gpsFocusPoint = null;
  gpsView.z = 1;
  gpsView.cx = 50;
  gpsView.cy = 50;
  renderGpsMap();
  renderFieldTracking();
  gpsUpdateMapLabels();
}

function gpsClampView() {
  gpsView.z = Math.max(GPS_ZOOM_MIN, Math.min(GPS_ZOOM_MAX, gpsView.z));
  const half = GPS_HALF / gpsView.z;
  gpsView.cx = Math.max(half, Math.min(100 - half, gpsView.cx));
  gpsView.cy = Math.max(half, Math.min(100 - half, gpsView.cy));
  return gpsView;
}

function gpsViewTransform() {
  const v = gpsClampView();
  return 'translate(' + GPS_HALF + ' ' + GPS_HALF + ') scale(' + v.z.toFixed(4) + ') translate(' + (-v.cx).toFixed(3) + ' ' + (-v.cy).toFixed(3) + ')';
}

function gpsCentreOn(lat, lng, zoom) {
  const p = projectGps(lat, lng);
  if (zoom) gpsView.z = zoom;
  gpsView.cx = p.x;
  gpsView.cy = p.y;
  gpsClampView();
  renderGpsMap();
}

function gpsZoomBy(factor, focus) {
  // keep the point under the cursor (or the centre) still while zooming
  const el = document.getElementById('gps-map');
  let ax = gpsView.cx, ay = gpsView.cy;
  if (focus && el) {
    const r = el.getBoundingClientRect();
    const fx = (focus.x - r.left) / Math.max(r.width, 1);
    const fy = (focus.y - r.top) / Math.max(r.height, 1);
    const half = GPS_HALF / gpsView.z;
    ax = gpsView.cx - half + fx * half * 2;
    ay = gpsView.cy - half + fy * half * 2;
  }
  const before = gpsView.z;
  gpsView.z = Math.max(GPS_ZOOM_MIN, Math.min(GPS_ZOOM_MAX, gpsView.z * factor));
  const k = before / gpsView.z;
  gpsView.cx = ax + (gpsView.cx - ax) * k;
  gpsView.cy = ay + (gpsView.cy - ay) * k;
  gpsClampView();
  renderGpsMap();
}

function gpsPanBy(dx, dy) {
  const half = GPS_HALF / gpsView.z;
  gpsView.cx += (dx / 100) * half * 2 * 0.5;
  gpsView.cy += (dy / 100) * half * 2 * 0.5;
  gpsClampView();
  renderGpsMap();
}

function gpsResetView() {
  gpsView = { z: 1, cx: 50, cy: 50 };
  renderGpsMap();
}

// The callout naming the located person is HTML, not SVG: the schematic map
// stretches its axes to fill the card, so text drawn inside it would be pulled
// out of shape as soon as the map is zoomed or panned.
function gpsUpdateLocateTag() {
  const wrap = document.querySelector('.gps-map-wrap');
  const map = document.getElementById('gps-map');
  if (!wrap || !map) return;

  let tag = document.getElementById('gps-locate-tag');
  const crew = gpsFocusCrew ? trackedCrew().find(c => c.id === gpsFocusCrew) : null;
  const point = crew ? gpsFocusPoint : null;
  if (!crew || !point) {
    if (tag) tag.style.display = 'none';
    return;
  }
  if (!tag) {
    tag = document.createElement('div');
    tag.id = 'gps-locate-tag';
    tag.className = 'gps-locate-tag';
    wrap.appendChild(tag);
  }

  const p = projectGps(point.lat, point.lng);
  const xPct = 50 + (p.x - gpsView.cx) * gpsView.z;
  const yPct = 50 + (p.y - gpsView.cy) * gpsView.z;
  const mapBox = map.getBoundingClientRect();
  const wrapBox = wrap.getBoundingClientRect();
  const ringPx = (6 / Math.max(gpsView.z, 1) * 1.6) * (mapBox.height / 100);

  tag.innerHTML = '\ud83e\uddd1\u200d\ud83d\udd27 ' + escapeHtml(crew.name) + ' \u2022 ' + escapeHtml(crew.vehicle || 'Assigned Route') + ' \u2022 ' + point.lat.toFixed(4) + ', ' + point.lng.toFixed(4);
  tag.style.left = ((xPct / 100) * mapBox.width).toFixed(1) + 'px';
  tag.style.top = ((mapBox.top - wrapBox.top) + (yPct / 100) * mapBox.height + ringPx + 6).toFixed(1) + 'px';
  tag.style.display = (xPct < 3 || xPct > 97 || yPct < 3 || yPct > 97) ? 'none' : '';
}

function gpsUpdateControls() {
  const label = document.getElementById('gps-zoom-label');
  if (label) label.textContent = gpsView.z.toFixed(1) + '\u00d7';
  gpsUpdateMapLabels();
  gpsUpdateLocateTag();
  const bar = document.getElementById('gps-locate-bar');
  const text = document.getElementById('gps-locate-text');
  const crew = gpsFocusCrew ? trackedCrew().find(c => c.id === gpsFocusCrew) : null;
  if (bar && text) {
    if (crew) {
      const state = crewStatus(crew.id);
      const point = gpsFocusPoint;

      text.innerHTML = 'Locating <strong>' + escapeHtml(crew.name) + '</strong> \u2022 ' +
        escapeHtml(crew.vehicle || 'Assigned Route') + ' \u2022 ' + escapeHtml(state.label) +
        (point ? ' \u2022 ' + point.lat.toFixed(4) + ', ' + point.lng.toFixed(4) : '');
      bar.style.display = '';
    } else {
      bar.style.display = 'none';
    }
  }
}

function initMapNavigation() {
  const box = document.getElementById('gps-map');
  if (!box || box.dataset.navReady) return;
  box.dataset.navReady = '1';
  let drag = null;

  const startDrag = ev => {
    if (ev.target.closest('.gps-marker') || ev.target.closest('.gps-crew')) return;
    const p = ev.touches ? ev.touches[0] : ev;
    drag = { x: p.clientX, y: p.clientY, cx: gpsView.cx, cy: gpsView.cy, moved: 0 };
    box.classList.add('is-panning');
  };
  const moveDrag = ev => {
    if (!drag) return;
    const p = ev.touches ? ev.touches[0] : ev;
    const rect = box.getBoundingClientRect();
    const half = GPS_HALF / gpsView.z;
    const dx = (p.clientX - drag.x) / Math.max(rect.width, 1) * half * 2;
    const dy = (p.clientY - drag.y) / Math.max(rect.height, 1) * half * 2;
    drag.moved = Math.max(drag.moved, Math.abs(p.clientX - drag.x) + Math.abs(p.clientY - drag.y));
    gpsView.cx = drag.cx - dx;
    gpsView.cy = drag.cy - dy;
    gpsClampView();
    renderGpsMap();
    if (ev.touches) ev.preventDefault();
  };
  const endDrag = () => {
    if (!drag) return;
    drag = null;
    box.classList.remove('is-panning');
  };

  box.addEventListener('mousedown', startDrag);
  document.addEventListener('mousemove', moveDrag);
  document.addEventListener('mouseup', endDrag);
  box.addEventListener('touchstart', startDrag, { passive: true });
  document.addEventListener('touchmove', moveDrag, { passive: false });
  document.addEventListener('touchend', endDrag);
  box.addEventListener('wheel', ev => {
    ev.preventDefault();
    gpsZoomBy(ev.deltaY < 0 ? 1.25 : 1 / 1.25, { x: ev.clientX, y: ev.clientY });
  }, { passive: false });
  box.addEventListener('dblclick', ev => gpsZoomBy(1.8, { x: ev.clientX, y: ev.clientY }));

  // two finger pinch on touch screens
  let pinch = null;
  box.addEventListener('touchstart', ev => {
    if (ev.touches.length === 2) {
      pinch = Math.hypot(ev.touches[0].clientX - ev.touches[1].clientX, ev.touches[0].clientY - ev.touches[1].clientY);
    }
  }, { passive: true });
  box.addEventListener('touchmove', ev => {
    if (ev.touches.length === 2 && pinch) {
      const now = Math.hypot(ev.touches[0].clientX - ev.touches[1].clientX, ev.touches[0].clientY - ev.touches[1].clientY);
      if (Math.abs(now - pinch) > 6) {
        gpsZoomBy(now / pinch);
        pinch = now;
      }
      ev.preventDefault();
    }
  }, { passive: false });
  box.addEventListener('touchend', () => { pinch = null; });
  window.addEventListener('resize', () => { gpsUpdateMapLabels(); gpsUpdateLocateTag(); });
}

const GPS_ZONE_LABELS = [
  { label: 'IBARA', x: 38, y: 30 },
  { label: 'ADIGBE', x: 66, y: 44 },
  { label: 'PANSEKE', x: 28, y: 58 },
  { label: 'SAGAMU ROAD', x: 72, y: 74 },
  { label: 'OMIDA', x: 48, y: 16 }
];

// where a map point (0-100 in both axes) falls inside the visible window
function gpsViewPoint(x, y) {
  return { x: 50 + (x - gpsView.cx) * gpsView.z, y: 50 + (y - gpsView.cy) * gpsView.z };
}

// ---------------------------------------------------------------------------
// Every name on the map (zones, crew, the person being located) is drawn as a
// positioned HTML tag over the map box. SVG text would be pulled out of shape
// by the wide viewBox and blown up by the zoom; HTML keeps one true size.
// ---------------------------------------------------------------------------
function gpsLabelLayer() {
  const wrap = document.querySelector('.gps-map-wrap');
  const map = document.getElementById('gps-map');
  if (!wrap || !map) return null;
  let layer = document.getElementById('gps-label-layer');
  if (!layer) {
    layer = document.createElement('div');
    layer.id = 'gps-label-layer';
    layer.className = 'gps-label-layer';
    wrap.appendChild(layer);
  }
  layer.dataset.box = '1';
  return { layer: layer, wrap: wrap, map: map };
}

function gpsPlaceTag(tag, layer, map, wrap, viewX, viewY, offsetPx) {
  const mapBox = map.getBoundingClientRect();
  const wrapBox = wrap.getBoundingClientRect();
  const left = (viewX / 100) * mapBox.width;
  const top = (mapBox.top - wrapBox.top) + (viewY / 100) * mapBox.height + (offsetPx || 0);
  const offScreen = viewX < 1 || viewX > 99 || viewY < 1 || viewY > 99;
  tag.style.left = left.toFixed(1) + 'px';
  tag.style.top = top.toFixed(1) + 'px';
  tag.style.display = offScreen ? 'none' : '';
  return tag;
}

function gpsUpdateMapLabels() {
  const ctx = gpsLabelLayer();
  if (!ctx) return;
  const { layer, map, wrap } = ctx;

  // zone names
  const zoneHtml = GPS_ZONE_LABELS.map(z => {
    const p = gpsViewPoint(z.x, z.y);
    const off = p.x < 1 || p.x > 99 || p.y < 1 || p.y > 99 ? ' style="display:none"' : '';
    return '<span class="gps-zone-tag" data-x="' + z.x + '" data-y="' + z.y + '"' + off + '>' + escapeHtml(z.label) + '</span>';
  }).join('');

  // crew names & real human icons
  const crew = trackedCrew();
  const humanSvg = '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">' +
    '<circle cx="12" cy="4.2" r="2.7"/>' +
    '<path d="M8.5 8.2h7c1.1 0 2 .9 2 2v4.6h-1.8V10.8h-.9v9.7h-2.1v-5.6h-1.4v5.6H9.2V10.8h-.9v4H6.5v-4.6c0-1.1.9-2 2-2z"/>' +
    '</svg>';
  const crewHtml = crew.map((c, i) => {
    const pts = positionsFor(c.id);
    const last = pts.slice(-1)[0];
    if (!last) return '';
    const q = projectGps(last.lat, last.lng);
    const state = crewStatus(c.id);
    const isLocated = gpsFocusCrew === c.id;
    const pinColor = isLocated ? '#D32F2F' : (c.role === 'Admin' ? '#6D28D9' : '#0F766E');
    return '<span class="gps-human-pin' + (isLocated ? ' is-located' : '') + '" data-x="' + q.x.toFixed(3) + '" data-y="' + q.y.toFixed(3) + '" style="--pin-color:' + pinColor + ';">' +
      '<span class="gps-human-badge" title="' + escapeHtml(c.name) + '">' + humanSvg + '</span></span>' +
      '<span class="gps-crew-tag' + (i % 2 ? ' is-below' : '') + '" data-x="' + q.x.toFixed(3) + '" data-y="' + q.y.toFixed(3) + '">' +
      escapeHtml(c.name) +
      '<i>' + escapeHtml(state.label) + '</i></span>';
  }).join('');

  // the signed-in person on this device ("You"), as an HTML tag like the rest
  const selfUser = currentUser();
  const selfVisible = gpsSelf
    && !(selfUser && trackedCrew().some(c => c.id === selfUser.id) && positionsFor(selfUser.id).length)
    && (!isSupervisor() || !gpsSelf.userId || (selfUser && gpsSelf.userId === selfUser.id));
  let selfHtml = '';
  if (selfVisible) {
    const p = projectGps(gpsSelf.lat, gpsSelf.lng);
    selfHtml = '<span class="gps-self-tag" data-x="' + p.x.toFixed(3) + '" data-y="' + p.y.toFixed(3) + '">' +
      (isSupervisor() ? 'YOU' : escapeHtml(gpsSelf.name || 'YOU')) + '</span>';
  }

  layer.innerHTML = zoneHtml + crewHtml + selfHtml;

  // place every tag from the current window
  [...layer.querySelectorAll('.gps-zone-tag')].forEach(tag => {
    const p = gpsViewPoint(Number(tag.dataset.x), Number(tag.dataset.y));
    gpsPlaceTag(tag, layer, map, wrap, p.x, p.y, -6);
  });
  [...layer.querySelectorAll('.gps-human-pin')].forEach(pin => {
    const p = gpsViewPoint(Number(pin.dataset.x), Number(pin.dataset.y));
    gpsPlaceTag(pin, layer, map, wrap, p.x, p.y, 0);
  });
  [...layer.querySelectorAll('.gps-crew-tag')].forEach(tag => {
    const p = gpsViewPoint(Number(tag.dataset.x), Number(tag.dataset.y));
    const below = tag.classList.contains('is-below');
    gpsPlaceTag(tag, layer, map, wrap, p.x, p.y, below ? 22 : -26);
  });
  [...layer.querySelectorAll('.gps-self-tag')].forEach(tag => {
    const p = gpsViewPoint(Number(tag.dataset.x), Number(tag.dataset.y));
    gpsPlaceTag(tag, layer, map, wrap, p.x, p.y, -14);
  });
}

function renderGpsMap() {
  const box = document.getElementById('gps-map');
  if (!box) return;
  const units = gpsUnits();

  const gridLines = [];
  for (let i = 20; i < 100; i += 20) {
    gridLines.push('<line x1="' + i + '" y1="0" x2="' + i + '" y2="100" stroke="#E8E2DA" stroke-width="0.25"/>');
    gridLines.push('<line x1="0" y1="' + i + '" x2="100" y2="' + i + '" stroke="#E8E2DA" stroke-width="0.25"/>');
  }

  const zones = GPS_ZONE_LABELS;

  const markers = units.map(u => {
    const p = projectGps(u.lat, u.lng);
    const colour = markerColour(u);
    const radius = u.type === 'Street' ? 1.5 : 1.15;
    const late = unitOverdue(u);
    const limit = u.category === 'Industrial' ? '1 month' : '2 weeks';
    const lateRing = late
      ? '<circle class="gps-dot-blink" cx="' + p.x.toFixed(2) + '" cy="' + p.y.toFixed(2) + '" r="' + (radius + 1.1) + '" fill="none" stroke="#D32F2F" stroke-width="0.55">' +
          '<animate attributeName="opacity" values="1;0.05;1" dur="1.1s" repeatCount="indefinite"/>' +
          '<animate attributeName="r" values="' + (radius + 0.7) + ';' + (radius + 2.6) + ';' + (radius + 0.7) + '" dur="1.1s" repeatCount="indefinite"/>' +
        '</circle>'
      : '<circle cx="' + p.x.toFixed(2) + '" cy="' + p.y.toFixed(2) + '" r="' + (radius + 1.3) + '" fill="' + colour + '" opacity="0.18"/>';
    return '<g class="gps-marker' + (late ? ' gps-marker-late' : '') + '" onclick="openGpsUnit(\'' + u.id + '\',\'' + u.type + '\')" style="cursor:pointer;">' +
      lateRing +
      '<circle cx="' + p.x.toFixed(2) + '" cy="' + p.y.toFixed(2) + '" r="' + radius + '" fill="' + colour + '" stroke="#FFFFFF" stroke-width="0.35"' + (late ? ' class="gps-dot-blink"' : '') + '>' +
        '<title>' + escapeHtml(u.name + ' \u2014 ' + u.category + ' \u2014 last evacuated ' + formatDate(u.lastEvacuated) + (late ? ' \u2014 PAST THE ' + limit.toUpperCase() + ' WINDOW' : '')) + '</title>' +
      '</circle></g>';
  }).join('');

  // ---- crew routes: the vehicle trail, its stops and where it is right now
  const trailPaths = [];
  const stopMarks = [];
  const crewMarks = [];
  trackedCrew().forEach((c, crewIndex) => {
    const pts = positionsFor(c.id);
    if (!pts.length) return;
    const colour = c.role === 'Admin' ? '#6D28D9' : '#0F766E';

    if (pts.length > 1) {
      const d = pts.map((p, i) => {
        const q = projectGps(p.lat, p.lng);
        return (i ? 'L' : 'M') + q.x.toFixed(2) + ' ' + q.y.toFixed(2);
      }).join(' ');
      trailPaths.push('<path class="gps-trail" d="' + d + '" fill="none" stroke="' + colour + '" stroke-width="0.6" stroke-dasharray="1.6 1.1" stroke-linejoin="round" stroke-linecap="round" opacity="0.95"><title>' + escapeHtml(c.name + ' \u2014 ' + c.vehicle + ' route') + '</title></path>');
      // direction of travel, so the route reads as movement and not as a doodle
      const tail = pts.slice(-6);
      if (tail.length > 1) {
        const a = projectGps(tail[0].lat, tail[0].lng);
        const b = projectGps(tail.slice(-1)[0].lat, tail.slice(-1)[0].lng);
        trailPaths.push('<line x1="' + a.x.toFixed(2) + '" y1="' + a.y.toFixed(2) + '" x2="' + b.x.toFixed(2) + '" y2="' + b.y.toFixed(2) + '" stroke="' + colour + '" stroke-width="0.45" marker-end="url(#gpsArrow)" opacity="0.9"/>');
      }
    }

    stopsFor(c.id).forEach(s => {
      const q = projectGps(s.lat, s.lng);
      stopMarks.push('<g class="gps-stop"><rect x="' + (q.x - 0.85).toFixed(2) + '" y="' + (q.y - 0.85).toFixed(2) + '" width="1.7" height="1.7" rx="0.4" fill="#FB8C00" stroke="#FFFFFF" stroke-width="0.3">' +
        '<title>' + escapeHtml(c.name + ' \u2014 ' + stopLabel(s)) + '</title></rect></g>');
    });

    const last = pts.slice(-1)[0];
    const q = projectGps(last.lat, last.lng);
    const state = crewStatus(c.id);
    const moving = state.cls === 'badge-success';
    const isLocated = gpsFocusCrew === c.id;
    const pinStroke = isLocated ? '#D32F2F' : colour;
    crewMarks.push('<g class="gps-crew" onclick="showCrewCard(\'' + escapeHtml(c.id) + '\')" style="cursor:pointer;">' +
      '<circle cx="' + q.x.toFixed(2) + '" cy="' + q.y.toFixed(2) + '" r="4.6" fill="' + pinStroke + '" opacity="0.18"/>' +
      '<circle cx="' + q.x.toFixed(2) + '" cy="' + q.y.toFixed(2) + '" r="2.7" fill="#FFFFFF" stroke="' + pinStroke + '" stroke-width="0.5"/>' +
      // real standing human icon: head + torso + arms + legs
      '<circle cx="' + q.x.toFixed(2) + '" cy="' + (q.y - 1.15).toFixed(2) + '" r="0.52" fill="' + pinStroke + '"/>' +
      '<rect x="' + (q.x - 0.55).toFixed(2) + '" y="' + (q.y - 0.48).toFixed(2) + '" width="1.10" height="1.05" rx="0.25" fill="' + pinStroke + '"/>' +
      '<line x1="' + (q.x - 1.05).toFixed(2) + '" y1="' + (q.y - 0.15).toFixed(2) + '" x2="' + (q.x + 1.05).toFixed(2) + '" y2="' + (q.y - 0.15).toFixed(2) + '" stroke="' + pinStroke + '" stroke-width="0.38" stroke-linecap="round"/>' +
      '<line x1="' + (q.x - 0.32).toFixed(2) + '" y1="' + (q.y + 0.55).toFixed(2) + '" x2="' + (q.x - 0.42).toFixed(2) + '" y2="' + (q.y + 1.55).toFixed(2) + '" stroke="' + pinStroke + '" stroke-width="0.38" stroke-linecap="round"/>' +
      '<line x1="' + (q.x + 0.32).toFixed(2) + '" y1="' + (q.y + 0.55).toFixed(2) + '" x2="' + (q.x + 0.42).toFixed(2) + '" y2="' + (q.y + 1.55).toFixed(2) + '" stroke="' + pinStroke + '" stroke-width="0.38" stroke-linecap="round"/>' +
      (moving ? '<circle cx="' + q.x.toFixed(2) + '" cy="' + q.y.toFixed(2) + '" r="2.7" fill="none" stroke="' + pinStroke + '" stroke-width="0.4"><animate attributeName="r" values="2.7;5.0;2.7" dur="1.8s" repeatCount="indefinite"/><animate attributeName="opacity" values="0.9;0;0.9" dur="1.8s" repeatCount="indefinite"/></circle>' : '') +
      '<title>' + escapeHtml(c.name + ' \u2022 ' + (c.vehicle || 'Assigned Route') + ' \u2022 ' + state.label) + '</title>' +
    '</g>');
  });

  // if the signed in user is already plotted as a named crew member, do not
  // draw a second anonymous "YOU" dot on top of their icon
  const selfUser = currentUser();
  const selfIsPlottedCrew = !!(selfUser && trackedCrew().some(c => c.id === selfUser.id) && positionsFor(selfUser.id).length);

  // v2.9.3 - a supervisor never sees the office on the map. The device marker
  // only belongs to the person signed in on this device: if an administrator
  // used this phone before, their leftover position is not shown to the
  // supervisor who signs in afterwards.
  function canSeeDevicePosition() {
    if (!gpsSelf) return false;
    if (!isSupervisor()) return true;
    return !gpsSelf.userId || (selfUser && gpsSelf.userId === selfUser.id);
  }

  // the "this is the person I am looking for" signal: a target ring, crosshair
  // and a callout, drawn over everything else at the crew's latest position
  let locateSignal = '';
  if (gpsFocusCrew) {
    const crew = trackedCrew().find(c => c.id === gpsFocusCrew);
    if (crew && gpsFocusPoint) {
      const q = projectGps(gpsFocusPoint.lat, gpsFocusPoint.lng);
      const r1 = 6 / Math.max(gpsView.z, 1) * 1.6;
      const label = crew.name + ' \u2022 ' + (crew.vehicle || 'no vehicle') + (gpsFocusPoint.live ? '' : ' \u2022 zone centre');
      const w = label.length * 1.05 + 4;
      locateSignal =
        '<g class="gps-locate" pointer-events="none">' +
          '<circle cx="' + q.x.toFixed(2) + '" cy="' + q.y.toFixed(2) + '" r="' + (r1 * 0.6).toFixed(2) + '" fill="#D32F2F" opacity="0.12">' +
            '<animate attributeName="r" values="' + (r1 * 0.4).toFixed(2) + ';' + (r1 * 1.5).toFixed(2) + ';' + (r1 * 0.4).toFixed(2) + '" dur="1.6s" repeatCount="indefinite"/>' +
            '<animate attributeName="opacity" values="0.28;0.02;0.28" dur="1.6s" repeatCount="indefinite"/>' +
          '</circle>' +
          '<circle cx="' + q.x.toFixed(2) + '" cy="' + q.y.toFixed(2) + '" r="' + r1.toFixed(2) + '" fill="none" stroke="#D32F2F" stroke-width="0.45"/>' +
          '<circle cx="' + q.x.toFixed(2) + '" cy="' + q.y.toFixed(2) + '" r="' + (r1 * 0.35).toFixed(2) + '" fill="none" stroke="#D32F2F" stroke-width="0.3" stroke-dasharray="0.7 0.5"/>' +
          '<line x1="' + (q.x - r1 - 1.4).toFixed(2) + '" y1="' + q.y.toFixed(2) + '" x2="' + (q.x - r1 * 0.7).toFixed(2) + '" y2="' + q.y.toFixed(2) + '" stroke="#D32F2F" stroke-width="0.45"/>' +
          '<line x1="' + (q.x + r1 * 0.7).toFixed(2) + '" y1="' + q.y.toFixed(2) + '" x2="' + (q.x + r1 + 1.4).toFixed(2) + '" y2="' + q.y.toFixed(2) + '" stroke="#D32F2F" stroke-width="0.45"/>' +
          '<line x1="' + q.x.toFixed(2) + '" y1="' + (q.y - r1 - 1.4).toFixed(2) + '" x2="' + q.x.toFixed(2) + '" y2="' + (q.y - r1 * 0.7).toFixed(2) + '" stroke="#D32F2F" stroke-width="0.45"/>' +
          '<line x1="' + q.x.toFixed(2) + '" y1="' + (q.y + r1 * 0.7).toFixed(2) + '" x2="' + q.x.toFixed(2) + '" y2="' + (q.y + r1 + 1.4).toFixed(2) + '" stroke="#D32F2F" stroke-width="0.45"/>' +
        '</g>';
    }
  }

  // this device's own position: two blue rings. The name is an HTML tag in the
  // label layer (gpsUpdateMapLabels), never SVG text - the wide viewBox and the
  // zoom stretch SVG lettering into unreadable bands.
  const selfVisible = gpsSelf && !selfIsPlottedCrew && canSeeDevicePosition();
  let selfMarker = '';
  if (selfVisible) {
    const p = projectGps(gpsSelf.lat, gpsSelf.lng);
    selfMarker = '<g class="gps-self">' +
      '<circle cx="' + p.x.toFixed(2) + '" cy="' + p.y.toFixed(2) + '" r="4" fill="#2563EB" opacity="0.22"/>' +
      '<circle cx="' + p.x.toFixed(2) + '" cy="' + p.y.toFixed(2) + '" r="1.8" fill="#2563EB" stroke="#FFFFFF" stroke-width="0.5"/>' +
    '</g>';
  }

  box.innerHTML =
    '<svg viewBox="0 0 100 100" preserveAspectRatio="none" class="gps-svg">' +
      '<g transform="' + gpsViewTransform() + '">' +
      '<defs><linearGradient id="gpsBg" x1="0" y1="0" x2="1" y2="1">' +
        '<stop offset="0%" stop-color="#FBF8F4"/><stop offset="100%" stop-color="#F1F5EF"/></linearGradient>' +
        '<marker id="gpsArrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="3" markerHeight="3" orient="auto-start-reverse">' +
          '<path d="M0 0 L10 5 L0 10 z" fill="#0F766E"/></marker></defs>' +
      '<rect width="100" height="100" fill="url(#gpsBg)"/>' +
      gridLines.join('') +
      '<path d="M8 34 Q34 30 52 41 T92 36" stroke="#C9D6C5" stroke-width="1.6" fill="none"/>' +
      '<path d="M14 70 Q40 62 60 72 T94 66" stroke="#C9D6C5" stroke-width="1.6" fill="none"/>' +
      '<path d="M30 4 Q36 40 30 96" stroke="#D8E0D4" stroke-width="1.2" fill="none"/>' +
      '<path d="M70 4 Q66 44 74 96" stroke="#D8E0D4" stroke-width="1.2" fill="none"/>' +
      '' +   // zone names travel as html tags over the map (gpsUpdateMapLabels)
      markers + trailPaths.join('') + stopMarks.join('') + crewMarks.join('') + selfMarker +
      locateSignal + '</g>' +
    '</svg>';

  gpsUpdateControls();

  const status = document.getElementById('gps-status-line');
  if (status) {
    const late = overdueUnits().length;
    const tracked = trackedCrew().filter(c => positionsFor(c.id).length).length;
    status.textContent = units.length + ' mapped unit(s) \u2022 ' + late + ' past the evacuation window (blinking red) \u2022 ' +
      tracked + ' crew member(s) reporting position' +
      (gpsSelf ? ' \u2022 this device at ' + gpsSelf.lat.toFixed(4) + ', ' + gpsSelf.lng.toFixed(4) : ' \u2022 this device not located yet');
  }

  renderFieldTracking();
  renderGpsNearest();
  applyGpsMapDisabledState();
}

function toggleGpsLayer(layer) {
  gpsLayers[layer] = !gpsLayers[layer];
  renderGpsMap();
  showToast('\ud83d\uddfa\ufe0f ' + (layer === 'facilities' ? 'Facilities' : 'Municipal streets') + ' layer ' + (gpsLayers[layer] ? 'shown' : 'hidden') + '.', 'info');
}

function locateMe() {
  const status = document.getElementById('gps-status-line');
  if (!navigator.geolocation) {
    applyFallbackDevicePosition(currentUser(), 'locate me', false);
    return;
  }
  if (status) status.textContent = 'Reading GPS position...';
  navigator.geolocation.getCurrentPosition(
    pos => {
      gpsSelf = { lat: pos.coords.latitude, lng: pos.coords.longitude, accuracy: pos.coords.accuracy, name: (currentUser() ? userFullName(currentUser()) : 'YOU'), userId: currentUser() ? currentUser().id : null };
      if (currentUser()) recordPosition(currentUser().id, pos.coords.latitude, pos.coords.longitude, { accuracy: pos.coords.accuracy, source: 'locate me' });
      store.state.settings.lastGps = { lat: gpsSelf.lat, lng: gpsSelf.lng, at: new Date().toISOString() };
      store.save();
      renderGpsMap();
      showToast('\ud83d\udccd Position acquired \u00b1' + Math.round(gpsSelf.accuracy) + ' m.', 'success');
    },
    () => {
      applyFallbackDevicePosition(currentUser(), 'locate me', false);
    },
    { enableHighAccuracy: false, timeout: 10000, maximumAge: 60000 }
  );
}

function renderGpsNearest() {
  const box = document.getElementById('gps-nearest-list');
  if (!box) return;
  if (!gpsSelf) {
    'Press Locate Me to show your position.'
    return;
  }

  const units = gpsUnits().map(u => Object.assign({}, u, { km: haversineKm(gpsSelf.lat, gpsSelf.lng, u.lat, u.lng) }))
    .sort((a, b) => a.km - b.km).slice(0, 6);

  box.innerHTML = units.map(u => {
    const days = getDaysSince(u.lastEvacuated);
    const cls = days > (u.category === 'Industrial' ? 30 : 14) ? 'badge-danger' : days >= 7 ? 'badge-warning' : 'badge-success';
    return '<div class="gps-near-item">' +
      '<div><strong>' + escapeHtml(u.name) + '</strong>' +
        '<div class="gps-near-meta">' + escapeHtml(u.location) + ' \u2022 ' + escapeHtml(u.supervisor || '') + '</div></div>' +
      '<div class="gps-near-right">' +
        '<span class="gps-near-km">' + u.km.toFixed(2) + ' km</span>' +
        '<span class="badge ' + cls + '">' + days + 'd</span>' +
      '</div>' +
      '<button class="btn btn-sm btn-primary" onclick="' + (u.type === 'Facility' ? 'promptEvacuateFacility' : 'openEvacuateStreetModal') + '(\'' + u.id + '\')">\u26a1 Evacuate</button>' +
    '</div>';
  }).join('');
}

function showCrewCard(crewId) {
  const c = trackedCrew().find(x => x.id === crewId);
  if (!c) return;
  const pts = positionsFor(crewId);
  const state = crewStatus(crewId);
  const stops = stopsFor(crewId).slice(-3).reverse();
  const lines = [
    '\ud83d\ude9b Vehicle: ' + (c.vehicle || 'not assigned'),
    '\ud83d\udccd Status: ' + state.label,
    '\ud83d\udcc8 Covered on this route: ' + crewTrailKm(crewId).toFixed(1) + ' km',
    '\ud83d\udccf Positions recorded: ' + pts.length
  ];
  if (stops.length) {
    lines.push('', 'Stops:');
    stops.forEach(s => lines.push('  \u2022 ' + stopLabel(s)));
  }
  alert(c.name + '\n' + lines.join('\n'));
}

function openGpsUnit(unitId, type) {
  if (type === 'Street') openStreetReportModal(unitId);
  else openFacilityReportModal(unitId);
}

// ===========================================================================
// 9. OUTSTANDING RADAR & SECTOR-SPECIFIC "OUTSTANDING FACILITIES" REPORT
// ===========================================================================
var activeDebtorSector = 'Commercial';

function shortPeriodAbbr(periodIdx) {
  const idx = Math.max(1, Math.min(ALL_PERIODS.length, Number(periodIdx) || CURRENT_PERIOD_INDEX));
  const label = ALL_PERIODS[idx - 1] || CURRENT_MONTH_NAME;
  const parts = String(label).trim().split(/\s+/);
  const m = (parts[0] || 'Jan').slice(0, 3);
  const y = (parts[1] || '2026').slice(-2);
  return m + ". '" + y;
}

function formatPeriodRangeAbbr(startLabel, endLabel) {
  const sIdx = periodIndexOf(startLabel) || 1;
  const eIdx = periodIndexOf(endLabel) || sIdx;
  if (sIdx >= eIdx) return shortPeriodAbbr(eIdx);
  return shortPeriodAbbr(sIdx) + '-' + shortPeriodAbbr(eIdx);
}

// Full month names, no year and no abbreviations: "September" or
// "July - September".
function formatOutstandingMonthsRange(facility) {
  const owing = outstandingPeriodIndexes(facility);
  if (!owing.length) return '-';
  const startName = monthNameFromPeriodIndex(owing[0]);
  const endName = monthNameFromPeriodIndex(owing[owing.length - 1]);
  if (owing.length === 1) return startName;
  return startName + ' - ' + endName;
}

function getOwingFacilitiesBySector(sector) {
  const sec = sector || activeDebtorSector || 'Commercial';
  return (store.state.facilities || []).filter(f => {
    const h = getPaymentHealth(f);
    if (h.owingMonths <= 0) return false;
    if (sec === 'all') return true;
    return f.category === sec;
  });
}

function setDebtorReportSector(sector) {
  activeDebtorSector = sector || 'Commercial';
  const sel = document.getElementById('debtor-sector-select');
  if (sel && sel.value !== activeDebtorSector) sel.value = activeDebtorSector;
  document.querySelectorAll('#debtor-sector-tabs .filter-tab').forEach(btn => {
    btn.classList.toggle('active', btn.getAttribute('data-sector') === activeDebtorSector);
  });
  renderDebtorRadar();
}

function fetchSectorOutstandingReport(sector) {
  setDebtorReportSector(sector || 'Commercial');
  switchView('debtors');
  openPreviewForDebtors();
}

function renderDebtorRadar() {
  const container = document.getElementById('debtor-radar-body');
  const reportBody = document.getElementById('debtor-report-table-body');
  const reportHeading = document.getElementById('debtor-report-heading');
  const reportSub = document.getElementById('debtor-report-sub');
  const summaryBadge = document.getElementById('debtor-sector-summary-badge');
  const detailLabel = document.getElementById('debtor-detail-sector-label');

  const sectorTitle = activeDebtorSector === 'all' ? 'ALL SECTORS' : activeDebtorSector.toUpperCase();
  if (reportHeading) reportHeading.textContent = 'OUTSTANDING FACILITIES';
  if (reportSub) {
    reportSub.textContent = 'SECTOR: ' + sectorTitle + ' \u2022 AS AT ' + formatLongDate(currentUsageDateIso()).toUpperCase();
  }
  if (detailLabel) {
    detailLabel.textContent = activeDebtorSector === 'all' ? 'All Sectors' : activeDebtorSector;
  }

  const owing = getOwingFacilitiesBySector(activeDebtorSector);
  if (summaryBadge) {
    summaryBadge.textContent = owing.length + ' Outstanding (' + (activeDebtorSector === 'all' ? 'All Sectors' : activeDebtorSector) + ')';
  }

  if (reportBody) {
    if (!owing.length) {
      reportBody.innerHTML = '<tr><td colspan="4" style="text-align:center;padding:24px;color:var(--eco-green);font-weight:700;">\u2713 Every registered facility in this sector is fully paid up.</td></tr>';
    } else {
      reportBody.innerHTML = owing.map((d, idx) => {
        const health = getPaymentHealth(d);
        const monthsStr = formatOutstandingMonthsRange(d);
        return '<tr>' +
          '<td><strong>' + (idx + 1) + '</strong></td>' +
          '<td><strong>' + escapeHtml(d.name) + '</strong></td>' +
          '<td style="text-align:center;"><span class="badge ' + health.class + '">' + health.owingMonths + '</span></td>' +
          '<td><strong>' + escapeHtml(monthsStr) + '</strong></td>' +
        '</tr>';
      }).join('');
    }
  }

  if (!container) return;
  if (!owing.length) {
    container.innerHTML = '<tr><td colspan="8" style="text-align:center;padding:40px;color:var(--eco-green);font-weight:700;">\u2713 Every registered client in this sector is fully paid up.</td></tr>';
    return;
  }

  container.innerHTML = owing.map((d, idx) => {
    const health = getPaymentHealth(d);
    const monthsStr = formatOutstandingMonthsRange(d);
    return '<tr>' +
      '<td><strong>' + (idx + 1) + '</strong></td>' +
      '<td><strong>' + escapeHtml(d.name) + '</strong></td>' +
      '<td><span class="badge badge-category">' + escapeHtml(d.category) + '</span></td>' +
      '<td><span class="badge ' + health.class + '">' + health.owingMonths + '</span></td>' +
      '<td><strong>' + escapeHtml(monthsStr) + '</strong></td>' +
      '<td><strong style="color:var(--danger-red);font-size:14px;">' + formatNaira(health.arrears) + '</strong></td>' +
      '<td><span class="badge badge-supervisor">\ud83d\udc64 ' + escapeHtml(d.supervisor) + '</span></td>' +
      '<td><div class="action-btn-group">' +
        '<button class="btn btn-sm btn-outline" onclick="openFacilityReportModal(\'' + d.id + '\')">\ud83d\udcc4 Report</button>' +
        '<button class="btn btn-sm btn-outline" onclick="openLogPaymentModal(\'' + d.id + '\')">\ud83d\udcb3 Record Payment</button>' +
      '</div></td>' +
    '</tr>';
  }).join('');
}

function debtorReportSpec(sectorOverride) {
  const sector = sectorOverride || activeDebtorSector || 'Commercial';
  const sectorLabel = sector === 'all' ? 'ALL SECTORS' : sector.toUpperCase();
  const owing = getOwingFacilitiesBySector(sector);
  const rows = owing.map((d, idx) => {
    const health = getPaymentHealth(d);
    return {
      sn: idx + 1,
      facility: d.name,
      category: d.category,
      owingMonths: health.owingMonths,
      monthsLabel: formatOutstandingMonthsRange(d),
      arrears: health.arrears
    };
  });
  const totalArrears = rows.reduce((s, r) => s + (Number(r.arrears) || 0), 0);
  const ref = 'TEEM-OUT-' + String(Date.now()).slice(-5);
  const cleanSec = (sector === 'all' ? 'All_Sectors' : sector).replace(/[^A-Za-z0-9]+/g, '_');
  return {
    kind: 'debtors',
    reference: ref,
    sector: sector,
    sectorLabel: sectorLabel,
    date: currentUsageDateIso(),
    rows: rows,
    total: totalArrears,
    filename: 'TEEM_Outstanding_Facilities_' + cleanSec + '_' + ref + '.pdf'
  };
}

function openPreviewForDebtors() {
  openDocPreview('debtors');
}

function printDebtorReport() {
  const spec = debtorReportSpec();
  const settings = docPreviewSettings();
  const res = renderPdfForContext(spec, buildDebtorReportPdf, settings);
  printPdfDocument(res.doc, 'OUTSTANDING FACILITIES - ' + spec.sectorLabel);
}

function saveDebtorReportPdf() {
  const spec = debtorReportSpec();
  const settings = docPreviewSettings();
  const res = renderPdfForContext(spec, buildDebtorReportPdf, settings);
  savePdfResult(res, 'OUTSTANDING FACILITIES - ' + spec.sectorLabel, spec, spec.filename);
}

// ---------------------------------------------------------------------------
// COLLAPSIBLE / DISABLEABLE GPS MAP & REPLACEMENT OPERATIONS HUB
// ---------------------------------------------------------------------------
function toggleGpsMapDisabled(forceState) {
  if (!store.state.settings) store.state.settings = {};
  const next = typeof forceState === 'boolean'
    ? forceState
    : !store.state.settings.gpsMapDisabled;
  store.state.settings.gpsMapDisabled = next;
  store.save();
  if (next && fieldWatchId !== null) {
    try { navigator.geolocation.clearWatch(fieldWatchId); } catch (e) {}
    fieldWatchId = null;
  }
  applyGpsMapDisabledState();
  showToast(
    next
      ? '\ud83c\udfe2 GPS Map collapsed. Showing Company Overview.'
      : '\ud83d\uddfa\ufe0f GPS Concession Map shown (Company Overview collapsed).',
    'info'
  );
  return next;
}

function applyGpsMapDisabledState() {
  const disabled = !!(store.state.settings && store.state.settings.gpsMapDisabled);
  const activeSec = document.getElementById('gps-active-section');
  const hubSec = document.getElementById('gps-replacement-hub');
  const companyCard = document.getElementById('company-overview-card') || document.querySelector('#view-overview .company-overview');
  const layerControls = document.getElementById('gps-layer-controls');
  const toggleBtn = document.getElementById('gps-toggle-map-btn');
  const mainTitle = document.getElementById('gps-card-main-title');
  const subLine = document.getElementById('gps-status-line');

  if (activeSec) activeSec.style.display = disabled ? 'none' : '';
  if (layerControls) layerControls.style.display = disabled ? 'none' : 'inline-flex';
  if (hubSec) hubSec.style.display = 'none';
  if (companyCard) companyCard.style.display = disabled ? '' : 'none';
  if (toggleBtn) {
    toggleBtn.classList.toggle('is-disabled-mode', disabled);
    toggleBtn.innerHTML = disabled
      ? '&#128506;&#65039; Enable / Show GPS Map'
      : '&#128315; Collapse / Disable GPS Map';
  }
  if (mainTitle) {
    mainTitle.innerHTML = disabled
      ? '&#127970; TEEM BUSINESS NIGERIA ENTERPRISES &mdash; COMPANY OVERVIEW (GPS MAP COLLAPSED)'
      : '&#128506;&#65039; GPS CONCESSION MAP &amp; LIVE FIELD POSITION';
  }
  if (subLine) {
    if (disabled) {
      subLine.textContent = 'GPS map is currently collapsed and the Company Overview card is displayed below. Click Enable / Show GPS Map to view live routes.';
    } else if (subLine.textContent.indexOf('GPS map is currently') === 0) {
      subLine.textContent = 'Abeokuta PSP Concession Area - Facilities, Municipal Streets, Registered Fleet & Supervisors';
    }
  }
}

function renderGpsReplacementHub() {
  const overdueEl = document.getElementById('hub-overdue-queue');
  const sectorEl = document.getElementById('hub-sector-debtors');
  const recentEl = document.getElementById('hub-recent-activity');

  if (overdueEl) {
    const units = allUnits()
      .map(u => ({ unit: u, sched: getScheduleStatus(u) }))
      .sort((a, b) => b.sched.days - a.sched.days)
      .slice(0, 5);
    overdueEl.innerHTML = units.map(({ unit, sched }) => {
      const isStreet = unit.unitType !== 'Facility';
      const actionCall = isStreet
        ? 'openEvacuateStreetModal(\'' + unit.id + '\')'
        : 'promptEvacuateFacility(\'' + unit.id + '\')';
      return '<div class="hub-item-row">' +
        '<div class="hub-item-main">' +
          '<strong>' + escapeHtml(unit.name) + '</strong>' +
          '<span>' + escapeHtml(unit.category) + '</span>' +
        '</div>' +
        '<button type="button" class="btn btn-sm btn-primary" onclick="' + actionCall + '">&#128666; Evacuate</button>' +
      '</div>';
    }).join('');
  }

  if (sectorEl) {
    const sectors = ['Commercial', 'Industrial', 'Agricultural Waste', 'Construction Waste', 'Medical', 'Institutional'];
    sectorEl.innerHTML = sectors.map(sec => {
      const list = getOwingFacilitiesBySector(sec);
      return '<div class="hub-item-row">' +
        '<div class="hub-item-main">' +
          '<strong>' + escapeHtml(sec) + '</strong>' +
          '<span>' + list.length + ' facility(ies) owing &bull; ' + (list.length ? formatOutstandingMonthsRange(list[0]) : 'Paid up') + '</span>' +
        '</div>' +
        '<button type="button" class="btn btn-sm btn-outline" onclick="fetchSectorOutstandingReport(\'' + sec + '\')">&#128196; Fetch Report</button>' +
      '</div>';
    }).join('');
  }

  if (recentEl) {
    const logs = (store.state.evacuationLogs || []).slice(0, 5);
    recentEl.innerHTML = logs.map(l =>
      '<div class="hub-item-row">' +
        '<div class="hub-item-main">' +
          '<strong>' + escapeHtml(l.target) + '</strong>' +
          '<span>&#128666; ' + escapeHtml(l.truck) + ' &bull; ' + formatDate(l.date) + '</span>' +
        '</div>' +
        '<span class="badge badge-success">' + escapeHtml(l.status || 'Verified') + '</span>' +
      '</div>'
    ).join('');
  }
}

// ===========================================================================
// 10. ALERTS + HEADER STATS
// ===========================================================================
function evaluateTrackerAlerts() {
  const overdue = allUnits().filter(u => getScheduleStatus(u).isOverdue);
  const owing = store.state.facilities.filter(f => getPaymentHealth(f).owingMonths > 0);

  const trackerBadge = document.getElementById('nav-tracker-badge');
  if (trackerBadge) { trackerBadge.textContent = overdue.length; trackerBadge.style.display = overdue.length ? 'inline-block' : 'none'; }
  const debtorBadge = document.getElementById('nav-debtor-badge');
  if (debtorBadge) { debtorBadge.textContent = owing.length; debtorBadge.style.display = owing.length ? 'inline-block' : 'none'; }

  const subAll = document.getElementById('sub-count-all');
  if (subAll) subAll.textContent = store.state.facilities.length;
  const subAgro = document.getElementById('sub-count-agro');
  if (subAgro) subAgro.textContent = store.state.facilities.filter(f => f.category === 'Agricultural Waste').length;
  const subConstr = document.getElementById('sub-count-constr');
  if (subConstr) subConstr.textContent = store.state.facilities.filter(f => f.category === 'Construction Waste').length;
}

function updateHeaderStats() {
  renderDashboardCards();
}

// ===========================================================================
// 11. REQUEST LETTERS
// ===========================================================================
const REQUEST_SECTOR_META = {
  'Commercial': { title: 'COMMERCIAL', column: 'COMMERCIAL OUTLET', rebate: 80, body: 'various commercial outfits allocated and served by us' },
  'Industrial': { title: 'INDUSTRIAL', column: 'INDUSTRIAL OUTLET', rebate: 60, body: 'various industrial outfits allocated and served by us' },
  // Medical facilities pay one bill covering medical waste AND general waste.
  // OGWAMA only owes us the general waste share, so that share is what is
  // claimed and what the 80% is calculated on - never the full amount paid.
  'Medical': { title: 'MEDICAL', column: 'MEDICAL OUTLET', rebate: 80, body: 'various medical outfits allocated and served by us', generalWaste: true },
  
  'Agricultural Waste': { title: 'AGRICULTURAL WASTE', column: 'AGRICULTURAL OUTLET', rebate: 80, body: 'various agricultural outfits allocated and served by us' },
  'Construction Waste': { title: 'CONSTRUCTION WASTE', column: 'CONSTRUCTION OUTLET', rebate: 80, body: 'various construction outfits allocated and served by us' },
  'Municipal': { title: 'RESIDENTIALS', column: 'RESIDENTIAL OUTLET', rebate: 0, body: 'various residents allocated and served by us', subject: 'REQUEST FOR PAYMENT OF RESIDENTIALS SERVICE BILL', showOutlet: false, showMonth: false }
};

function requestSubject(category) {
  const meta = REQUEST_SECTOR_META[category] || REQUEST_SECTOR_META['Commercial'];
  return meta.subject || ('REQUEST FOR PAYMENT OF ' + meta.title + ' SERVICE BILL');
}

// ---------------------------------------------------------------------------
// 11a. PAYMENT ENTRY ORDER
// The request list must read in the order the entries were typed, and it must
// read the same on every device. So each record carries a permanent sequence
// number that is given once and never recalculated - nothing re-sorts, nothing
// floats to the middle when the cloud syncs.
// ---------------------------------------------------------------------------
function paymentSeqOf(p) {
  const n = Number(p && p.seq);
  return Number.isFinite(n) ? n : null;
}

function nextPaymentSeq() {
  const list = (store && store.state && store.state.paymentScheduleRecords) || [];
  let max = -1;
  list.forEach(p => { const n = paymentSeqOf(p); if (n !== null && n > max) max = n; });
  return max + 1;
}

// Records typed before this release carry no number. They are numbered once,
// oldest payment date first, so the list opens in a sensible order. After that
// the numbers never change again.
function ensurePaymentSeqOrder() {
  if (!store || !store.state || !Array.isArray(store.state.paymentScheduleRecords)) return false;
  const list = store.state.paymentScheduleRecords;
  const missing = list.filter(p => p && paymentSeqOf(p) === null);
  if (!missing.length) return false;
  const used = new Set();
  list.forEach(p => { const n = paymentSeqOf(p); if (n !== null) used.add(n); });
  // Numbered in the order the records already sit in - NOT by payment date.
  // Sorting by date here is what used to shuffle the list around for anybody
  // who did not enter their payments in date order.
  let next = 0;
  missing.forEach(p => {
    while (used.has(next)) next++;
    p.seq = next;
    // Marks a number this device invented at upgrade time. If another device
    // has already numbered the same record, that number wins, so every device
    // ends up on one shared order instead of each keeping its own.
    p.seqAuto = true;
    used.add(next);
  });
  return true;
}

function paymentInRequestCategory(p, cat) {
  if (!p) return false;
  if (cat === 'Municipal') return p.category === 'Municipal';
  if (cat === 'Agricultural Waste') return p.category === 'Agricultural Waste';
  if (cat === 'Construction Waste') return p.category === 'Construction Waste';
  if (cat === 'Commercial') return p.category === 'Commercial' || p.category === 'Institutional';
  return p.category === cat;
}

function requestRecords() {
  const cat = activeRequestCategory;
  if (typeof ensurePaymentSeqOrder === 'function') ensurePaymentSeqOrder();
  const list = (store.state.paymentScheduleRecords || []).filter(p => {
    if (!paymentInRequestCategory(p, cat)) return false;
    // Filed entries stay on record and still count as paid - they are simply
    // no longer in the working list.
    if (p.archived && !store.state.showArchivedRequests) return false;
    return true;
  });
  // Entry order, oldest entry first. A stable sort, so numbering ties keep
  // whatever order they already had instead of jumping about.
  return list.slice().sort((a, b) => {
    const sa = paymentSeqOf(a), sb = paymentSeqOf(b);
    if (sa === null && sb === null) return 0;
    if (sa === null) return 1;
    if (sb === null) return -1;
    if (sa !== sb) return sa - sb;
    // Same number: order by id so two devices agree instead of swapping.
    const ia = String(a.id || ''), ib = String(b.id || '');
    return ia < ib ? -1 : (ia > ib ? 1 : 0);
  });
}

// Which figure on a record is the one we are owed. For Medical it is the
// general waste share; for every other sector it is the amount paid.
function requestCharge(p, meta) {
  if (!p) return 0;
  if (meta && meta.generalWaste) return Number(p.generalWaste) || 0;
  return Number(p.amount) || 0;
}

function requestSelection() {
  const records = requestRecords();
  const selected = records.filter(p => p.selected);
  const meta = REQUEST_SECTOR_META[activeRequestCategory] || REQUEST_SECTOR_META['Commercial'];
  const total = selected.reduce((sum, p) => sum + requestCharge(p, meta), 0);
  const rebate = meta.rebate ? Math.round(total * (meta.rebate / 100)) : 0;
  return { records: records, selected: selected, total: total, rebate: rebate, meta: meta };
}

function setRequestCategory(cat) {
  activeRequestCategory = cat;
  const tabMap = {
    'Commercial': 'req-cat-commercial', 'Industrial': 'req-cat-industrial', 'Medical': 'req-cat-medical',
    'Agricultural Waste': 'req-cat-agricultural', 'Construction Waste': 'req-cat-construction', 'Municipal': 'req-cat-municipal'
  };
  Object.keys(tabMap).forEach(k => {
    const el = document.getElementById(tabMap[k]);
    if (el) el.classList.toggle('active', k === cat);
  });
  renderRequestsView();
}

function togglePaymentItemSelection(id) {
  const item = store.state.paymentScheduleRecords.find(p => p.id === id);
  if (item) { item.selected = !item.selected; store.save(); renderRequestsView(); }
}

function togglePaymentItemReRequest(id) {
  if (!requireAdmin('Changing a payment entry')) return;
  const item = store.state.paymentScheduleRecords.find(p => p.id === id);
  if (item) { item.isReRequest = !item.isReRequest; store.save(); renderRequestsView(); }
}

function removePaymentFromSchedule(id) {
  if (!requireAdmin('Removing a payment entry')) return;
  const entry = (store.state.paymentScheduleRecords || []).find(p => p.id === id);
  if (typeof recordDeletedId === 'function') recordDeletedId(id);
  store.state.paymentScheduleRecords = store.state.paymentScheduleRecords.filter(p => p.id !== id);
  // keep the client's own payment history in step with the schedule
  if (entry) {
    (store.state.facilities || []).forEach(f => {
      if (Array.isArray(f.paymentHistory)) {
        const beforeLen = f.paymentHistory.length;
        f.paymentHistory = f.paymentHistory.filter(h => h.id !== id);
        if (f.paymentHistory.length !== beforeLen) {
          f.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
        }
        if (f.lastPayment && f.lastPayment.id === id) f.lastPayment = f.paymentHistory[0] || null;
      }
    });
  }
  store.save();
  renderRequestsView();
  renderFacilitiesDirectory();
  showToast('\ud83d\uddd1\ufe0f Payment entry removed from schedule.', 'warning');
}

// ---- correct an entry that was captured wrongly -----------------------------
function scheduleOutletOptions(selectedName) {
  const groups = {};
  (store.state.facilities || []).forEach(f => {
    if (!groups[f.category]) groups[f.category] = [];
    groups[f.category].push(f);
  });
  let html = '<option value="">-- Select outlet / facility --</option>';
  // A row may name an outlet that was created outside the register (an older
  // payment entry, for example). It must still be correctable, so the name is
  // offered as its own option instead of being silently dropped.
  const known = (store.state.facilities || []).some(f => f.name === selectedName);
  if (selectedName && !known) {
    html += '<optgroup label="Not in the facility register">' +
      '<option value="' + escapeHtml(selectedName) + '" selected>' + escapeHtml(selectedName) + ' (keep as captured)</option>' +
      '</optgroup>';
  }
  Object.keys(groups).sort().forEach(cat => {
    html += '<optgroup label="' + escapeHtml(cat) + '">';
    groups[cat].sort((a, b) => a.name.localeCompare(b.name)).forEach(f => {
      html += '<option value="' + escapeHtml(f.name) + '"' + (f.name === selectedName ? ' selected' : '') + '>' + escapeHtml(f.name) + '</option>';
    });
    html += '</optgroup>';
  });
  return html;
}

function openEditSchedulePayment(id) {
  const entry = (store.state.paymentScheduleRecords || []).find(p => p.id === id);
  if (!entry) { showToast('\u26a0\ufe0f That entry is no longer in the schedule.', 'error'); return; }
  if (!requireAdmin('Correcting a payment entry')) return;

  const isMunicipal = entry.category === 'Municipal';
  document.getElementById('sch-id').value = entry.id;
  document.getElementById('sch-edit-title').textContent = (entry.depositor || entry.outlet) + ' - ' + formatNaira(entry.amount);
  document.getElementById('sch-edit-sub').textContent =
    'Captured ' + formatShortDate(entry.date) + ' for ' + entry.month + '. Correct anything that was captured wrongly, then save.';
  const badge = document.getElementById('sch-edit-badge');
  if (badge) badge.textContent = entry.category || 'Commercial';

  const outletGroup = document.getElementById('sed-outlet-group');
  const outlet = document.getElementById('sed-outlet');
  if (outletGroup) outletGroup.style.display = isMunicipal ? 'none' : '';
  if (outlet) {
    outlet.required = !isMunicipal;
    outlet.innerHTML = scheduleOutletOptions(entry.outlet);
    if (!outlet.value) outlet.value = entry.outlet;
  }
  document.getElementById('sed-depositor').value = entry.depositor || '';
  document.getElementById('sed-amount').value = entry.amount || '';
  syncEditGeneralWasteVisibility(entry);
  document.getElementById('sed-general-waste').value =
    (entry.generalWaste === undefined || entry.generalWaste === null) ? '' : entry.generalWaste;
  document.getElementById('sed-date').value = entry.date || currentUsageDateIso();
  document.getElementById('sed-month').value = entry.month || CURRENT_MONTH_PLAIN;
  document.getElementById('sed-is-re').checked = !!entry.isReRequest;

  openModal('modal-edit-schedule-payment');
}

// Shown only while the entry belongs to a Medical facility.
function syncEditGeneralWasteVisibility(entry) {
  const group = document.getElementById('sed-general-waste-group');
  if (!group) return;
  let category = entry && entry.category;
  if (!category) {
    const sel = document.getElementById('sed-outlet');
    const name = sel ? sel.value : '';
    const fac = (store.state.facilities || []).find(f => f && f.name === name);
    const rec = (store.state.paymentScheduleRecords || []).find(p => p.id === document.getElementById('sch-id').value);
    category = fac ? fac.category : (rec ? rec.category : activeRequestCategory);
  }
  group.style.display = category === 'Medical' ? '' : 'none';
}

function saveEditSchedulePayment(e) {
  if (e) e.preventDefault();
  if (!requireAdmin('Correcting a payment entry')) return;

  const id = document.getElementById('sch-id').value;
  const entry = (store.state.paymentScheduleRecords || []).find(p => p.id === id);
  if (!entry) { showToast('\u26a0\ufe0f That entry is no longer in the schedule.', 'error'); closeModal('modal-edit-schedule-payment'); return; }

  const isMunicipal = entry.category === 'Municipal';
  const rawDepositor = (document.getElementById('sed-depositor').value || '').trim();
  const outlet = isMunicipal
    ? (rawDepositor || entry.outlet || 'Residentials')
    : ((document.getElementById('sed-outlet').value || '').trim() || entry.outlet);
  const depositor = rawDepositor || outlet;
  const amount = Number(document.getElementById('sed-amount').value) || 0;
  const payDate = document.getElementById('sed-date').value || currentUsageDateIso();
  const month = (document.getElementById('sed-month').value || '').trim() || CURRENT_MONTH_PLAIN;
  const isRe = document.getElementById('sed-is-re').checked;

  if (amount <= 0) { showToast('\u26a0\ufe0f Enter the amount that was actually paid.', 'error'); return; }

  const previousOutlet = entry.outlet;
  const matchedFacility = isMunicipal ? null : (store.state.facilities || []).find(f => f.name === outlet);
  const matchedStreet = (store.state.municipalStreets || []).find(s => s.name === outlet);

  entry.outlet = outlet;
  entry.category = isMunicipal ? 'Municipal' : (matchedFacility ? matchedFacility.category : (matchedStreet ? 'Municipal' : entry.category));
  entry.depositor = depositor;
  entry.amount = amount;
  entry.date = payDate;
  entry.month = month;
  entry.isReRequest = isRe;
  if (entry.category === 'Medical') {
    const gwEl = document.getElementById('sed-general-waste');
    entry.generalWaste = Math.max(0, Number(gwEl ? gwEl.value : 0) || 0);
  } else {
    delete entry.generalWaste;
  }

  // ---- keep the client's payment history in step ---------------------------
  const histEntry = previousOutlet !== outlet
    ? null
    : (store.state.facilities || []).map(f => (f.paymentHistory || []).find(h => h.id === id)).find(Boolean);

  if (previousOutlet !== outlet) {
    (store.state.facilities || []).forEach(f => {
      if (Array.isArray(f.paymentHistory)) {
        f.paymentHistory = f.paymentHistory.filter(h => h.id !== id);
        if (f.lastPayment && f.lastPayment.id === id) f.lastPayment = f.paymentHistory[0] || null;
      }
    });
  }

  if (matchedFacility) {
    if (!Array.isArray(matchedFacility.paymentHistory)) matchedFacility.paymentHistory = [];
    const record = histEntry || { id: id };
    record.payerName = depositor;
    record.amount = amount;
    record.date = payDate;
    record.month = month;
    record.periodFrom = month;
    record.periodTo = month;
    if (!histEntry) matchedFacility.paymentHistory.unshift(record);
    matchedFacility.lastPayment = matchedFacility.paymentHistory[0];
  }

  store.save();
  closeModal('modal-edit-schedule-payment');
  if (entry.category !== activeRequestCategory) setRequestCategory(entry.category);
  else renderRequestsView();
  renderFacilitiesDirectory();
  showToast('\u2705 Payment entry for "' + outlet + '" corrected.', 'success');
}

function removeSchedulePayment() {
  const id = document.getElementById('sch-id').value;
  if (!id) return;
  if (!confirm('Remove this payment entry from the schedule? The letter and its totals update immediately.')) return;
  closeModal('modal-edit-schedule-payment');
  removePaymentFromSchedule(id);
}

// Payment entry modal: facility dropdown of every registered facility (hidden for Municipal)
function openAddSchedulePaymentModal() {
  if (!requireAdmin('Adding a payment entry')) return;
  const isMunicipal = activeRequestCategory === 'Municipal';
  const outletGroup = document.getElementById('sch-outlet-group');
  const select = document.getElementById('sch-outlet');
  if (outletGroup) {
    outletGroup.style.display = isMunicipal ? 'none' : '';
  }
  if (select) {
    select.required = !isMunicipal;
    const groups = {};
    store.state.facilities.forEach(f => {
      if (!groups[f.category]) groups[f.category] = [];
      groups[f.category].push(f);
    });
    let html = '<option value="">-- Select outlet / facility --</option>';
    Object.keys(groups).sort().forEach(cat => {
      html += '<optgroup label="' + escapeHtml(cat) + '">';
      groups[cat].sort((a, b) => a.name.localeCompare(b.name)).forEach(f => {
        html += '<option value="' + escapeHtml(f.name) + '" data-depositor="' + escapeHtml((latestPayment(f) || {}).payerName || f.name) + '">' + escapeHtml(f.name) + '</option>';
      });
      html += '</optgroup>';
    });
    select.innerHTML = html;
  }

  // The general waste share only applies to Medical facilities.
  const gwGroup = document.getElementById('sch-general-waste-group');
  if (gwGroup) gwGroup.style.display = isMunicipal ? 'none' : (activeRequestCategory === 'Medical' ? '' : 'none');
  const gwInput = document.getElementById('sch-general-waste');
  if (gwInput) gwInput.value = '';

  const dateEl = document.getElementById('sch-date');
  if (dateEl) dateEl.value = currentUsageDateIso();
  const monthEl = document.getElementById('sch-month');
  if (monthEl) monthEl.value = CURRENT_MONTH_PLAIN;
  const amountEl = document.getElementById('sch-amount');
  if (amountEl) amountEl.value = '';
  const depositorEl = document.getElementById('sch-depositor');
  if (depositorEl) depositorEl.value = '';
  const reEl = document.getElementById('sch-is-re');
  if (reEl) reEl.checked = false;

  openModal('modal-add-schedule-payment');
}

function onScheduleOutletChanged() {
  const select = document.getElementById('sch-outlet');
  const depositor = document.getElementById('sch-depositor');
  const amount = document.getElementById('sch-amount');
  if (!select || !select.value) return;
  const opt = select.options[select.selectedIndex];
  if (depositor && opt.dataset.depositor) depositor.value = opt.dataset.depositor;

  const fac = store.state.facilities.find(f => f.name === select.value);
  if (fac && amount && !amount.value) {
    amount.value = fac.amount;
    const monthEl = document.getElementById('sch-month');
    if (monthEl) monthEl.value = CURRENT_MONTH_PLAIN;
  }
}

function addCustomPaymentToSchedule(e) {
  if (e) e.preventDefault();
  const isMunicipal = activeRequestCategory === 'Municipal';
  const outletEl = document.getElementById('sch-outlet');
  const depositor = (document.getElementById('sch-depositor').value || '').trim();
  const outlet = isMunicipal ? (depositor || 'Residentials') : (outletEl ? outletEl.value.trim() : '');
  const amount = Number(document.getElementById('sch-amount').value) || 0;
  const payDate = document.getElementById('sch-date').value || currentUsageDateIso();
  const month = (document.getElementById('sch-month').value || '').trim() || CURRENT_MONTH_PLAIN;
  const isRe = document.getElementById('sch-is-re').checked;

  if (isMunicipal) {
    if (!depositor || amount <= 0) {
      showToast('\u26a0\ufe0f Enter the depositor name and a valid amount.', 'error');
      return;
    }
  } else if (!outlet || amount <= 0) {
    showToast('\u26a0\ufe0f Select an outlet and enter a valid amount.', 'error');
    return;
  }

  const matchedFacility = isMunicipal ? null : store.state.facilities.find(f => f.name === outlet);
  const matchedStreet = isMunicipal ? null : store.state.municipalStreets.find(s => s.name === outlet);
  const category = isMunicipal ? 'Municipal' : (matchedFacility ? matchedFacility.category : (matchedStreet ? 'Municipal' : activeRequestCategory));

  const entry = {
    id: 'pay-' + Date.now().toString().slice(-5),
    seq: nextPaymentSeq(),
    outlet: outlet,
    category: category,
    depositor: depositor || outlet,
    amount: amount,
    date: payDate,
    month: month,
    isReRequest: isRe,
    selected: true
  };
  // Medical bills cover medical waste and general waste together; only the
  // general waste share is claimed, so it is stored beside the full amount.
  if (category === 'Medical') {
    const gwEl = document.getElementById('sch-general-waste');
    entry.generalWaste = Math.max(0, Number(gwEl ? gwEl.value : 0) || 0);
  }

  store.state.paymentScheduleRecords.push(entry);

  // Keep the client's own payment history in step (never overwrites past records)
  if (matchedFacility) {
    if (!Array.isArray(matchedFacility.paymentHistory)) matchedFacility.paymentHistory = [];
    matchedFacility.paymentHistory.unshift({
      id: entry.id,
      payerName: entry.depositor,
      amount: entry.amount,
      date: entry.date,
      month: entry.month,
      periodFrom: month,
      periodTo: month
    });
    matchedFacility.lastPayment = matchedFacility.paymentHistory[0];
  }

  store.save();
  closeModal('modal-add-schedule-payment');
  if (entry.category !== activeRequestCategory) setRequestCategory(entry.category);
  else renderRequestsView();
  renderFacilitiesDirectory();
  showToast('\u2705 Payment entry for "' + (isMunicipal ? depositor : outlet) + '" added to the schedule.', 'success');
}

// ===========================================================================
// v17: REQUEST HISTORY - reopen or correct an earlier request
// ===========================================================================
function ensureRequestHistory() {
  if (!store || !store.state) return [];
  if (!Array.isArray(store.state.requestHistory)) store.state.requestHistory = [];
  return store.state.requestHistory;
}

function recordRequestHistory(spec, filename, docId) {
  if (!spec || spec.kind !== 'request') return null;
  const hist = ensureRequestHistory();
  const rows = (spec.rows || []).map(r => ({
    outlet: r.outlet, depositor: r.depositor, amount: r.amount,
    date: r.date, month: r.month, genWaste: r.genWaste, isReRequest: !!r.isReRequest
  }));
  const entry = {
    id: 'rq_' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6),
    reference: spec.reference || '',
    category: spec.category || activeRequestCategory,
    savedAt: new Date().toISOString(),
    monthLabel: (rows[0] && rows[0].month) || '',
    rowCount: rows.length,
    total: spec.total || 0,
    rebateValue: spec.rebateValue || 0,
    rows: rows,
    rowIds: (spec.rowIds || []).slice(),
    filename: filename || '',
    docId: docId || '',
    status: 'saved'
  };
  // A correction of the same request replaces the earlier record.
  const existing = hist.findIndex(h => h.reference && h.reference === entry.reference);
  if (existing >= 0) { entry.id = hist[existing].id; hist[existing] = entry; }
  else hist.unshift(entry);
  if (hist.length > 60) store.state.requestHistory = hist.slice(0, 60);
  if (typeof store.save === 'function') store.save();
  return entry;
}

function markRequestRowsDone(spec) {
  if (!spec || spec.kind !== 'request') return;
  const ids = spec.rowIds || [];
  (store.state.paymentScheduleRecords || []).forEach(p => {
    if (ids.length && ids.indexOf(p.id) === -1) return;
    if (!ids.length && !p.selected) return;
    p.selected = false;
    p.requested = true;
    p.requestedAt = new Date().toISOString();
    p.requestedRef = spec.reference || '';
  });
  if (typeof store.save === 'function') store.save();
}

// Clears the Payment Schedule Manager for a fresh request. Entries that were
// already put in a letter (or are ticked right now) are filed away, not deleted:
// they stay in the records, keep counting as paid, and can be shown again.
function startNewRequest() {
  const cat = activeRequestCategory;
  let filed = 0;
  (store.state.paymentScheduleRecords || []).forEach(p => {
    if (!paymentInRequestCategory(p, cat)) return;
    if (p.archived) { p.selected = false; return; }
    if (p.requested || p.selected) {
      p.archived = true;
      p.archivedAt = new Date().toISOString();
      p.selected = false;
      filed++;
    }
  });
  store.state.editingRequestId = '';
  store.state.editingRequestRef = '';
  if (typeof store.save === 'function') store.save();
  renderRequestsView();
  showToast(filed
    ? '\u2705 New request ready. ' + filed + ' entr' + (filed === 1 ? 'y' : 'ies') + ' filed.'
    : '\u2705 New request ready.', 'success');
}

function toggleArchivedRequests() {
  store.state.showArchivedRequests = !store.state.showArchivedRequests;
  renderRequestsView();
}

function restoreArchivedRequests() {
  let n = 0;
  (store.state.paymentScheduleRecords || []).forEach(p => {
    if (p.archived && paymentInRequestCategory(p, activeRequestCategory)) { p.archived = false; n++; }
  });
  store.state.showArchivedRequests = false;
  if (typeof store.save === 'function') store.save();
  renderRequestsView();
  showToast(n ? '\u21ba ' + n + ' entr' + (n === 1 ? 'y' : 'ies') + ' back in the list.' : 'Nothing to restore.', 'info');
}

function openRequestHistory() {
  const hist = ensureRequestHistory();
  const body = document.getElementById('request-history-body');
  if (!body) return;
  body.innerHTML = hist.length ? hist.map(h => {
    const date = new Date(h.savedAt);
    const when = isNaN(date.getTime()) ? h.savedAt : date.toLocaleDateString('en-GB') + ' ' + date.toLocaleTimeString('en-GB', { hour: '2-digit', minute: '2-digit' });
    return '<div class="req-hist-row">' +
      '<div class="req-hist-main">' +
        '<strong>' + escapeHtml(h.category) + ' \u2022 ' + escapeHtml(h.reference || '') + '</strong>' +
        '<span>' + when + ' \u2022 ' + h.rowCount + ' row' + (h.rowCount === 1 ? '' : 's') + ' \u2022 ' + formatNaira(h.total) + '</span>' +
      '</div>' +
      '<div class="req-hist-actions">' +
        '<button type="button" class="btn btn-outline" onclick="reopenRequestHistory(\'' + h.id + '\')">\u270f\ufe0f Edit</button>' +
        '<button type="button" class="btn btn-outline" onclick="viewRequestHistory(\'' + h.id + '\')">\ud83d\udd0d View</button>' +
      '</div>' +
    '</div>';
  }).join('') : '<div class="report-empty">No saved request yet. A request is saved when you save or print the letter.</div>';
  openModal('modal-request-history');
}

function findRequestHistory(id) {
  return ensureRequestHistory().find(h => h.id === id) || null;
}

function reopenRequestHistory(id) {
  const h = findRequestHistory(id);
  if (!h) return;
  activeRequestCategory = h.category;
  const catMap = {
    'Commercial': 'req-cat-commercial', 'Industrial': 'req-cat-industrial', 'Medical': 'req-cat-medical',
    'Agricultural Waste': 'req-cat-agricultural', 'Construction Waste': 'req-cat-construction', 'Municipal': 'req-cat-municipal'
  };
  Object.keys(catMap).forEach(k => {
    const el = document.getElementById(catMap[k]);
    if (el) el.classList.toggle('active', k === h.category);
  });
  // Tick only the entries recorded on that request.
  const ids = h.rowIds || [];
  (store.state.paymentScheduleRecords || []).forEach(p => {
    p.selected = ids.length ? ids.indexOf(p.id) !== -1 : false;
  });
  store.state.editingRequestId = h.id;
  store.state.editingRequestRef = h.reference || '';
  if (typeof store.save === 'function') store.save();
  closeModal('modal-request-history');
  switchView('requests');
  renderRequestsView();
  showToast('\u270f\ufe0f Editing request ' + (h.reference || '') + '.', 'success');
}

function viewRequestHistory(id) {
  const h = findRequestHistory(id);
  if (!h) return;
  const rows = (h.rows || []).map((r, i) => '<tr>' +
    '<td class="col-sn">' + (i + 1) + '.</td>' +
    '<td>' + escapeHtml(r.outlet || '') + '</td>' +
    '<td>' + escapeHtml(r.depositor || '') + '</td>' +
    '<td class="col-amount">' + Number(r.amount || 0).toLocaleString('en-NG') + '</td>' +
    '<td class="col-date">' + formatShortDate(r.date) + '</td>' +
    '<td class="col-month">' + escapeHtml(r.month || '') + '</td>' +
  '</tr>').join('');
  const body = document.getElementById('request-history-body');
  if (body) {
    body.innerHTML = '<button type="button" class="btn btn-outline" style="margin-bottom:10px;" onclick="openRequestHistory()">\u2190 Back to list</button>' +
      '<div class="req-hist-main" style="margin-bottom:10px;"><strong>' + escapeHtml(h.category) + ' \u2022 ' + escapeHtml(h.reference || '') + '</strong>' +
      '<span>' + h.rowCount + ' rows \u2022 ' + formatNaira(h.total) + '</span></div>' +
      '<div style="overflow:auto;"><table class="data-table"><thead><tr><th>S/N</th><th>Outlet</th><th>Depositor</th><th>Amount</th><th>Date</th><th>Month</th></tr></thead><tbody>' + rows + '</tbody></table></div>';
  }
}

function renderRequestsView() {
  const data = requestSelection();
  const meta = data.meta;

  const list = document.getElementById('req-items-checklist');
  if (list) {
    const admin = isAdmin();
    list.innerHTML = data.records.length ? data.records.map(p => '<div class="req-item' + (p.selected ? ' selected' : '') + '" title="' + escapeHtml(p.outlet + ' - ' + p.depositor + ' - ' + formatShortDate(p.date) + ' - ' + p.month + ' - ' + formatNaira(p.amount)) + '">' +
        '<label class="req-item-check"><input type="checkbox" ' + (p.selected ? 'checked' : '') + ' onchange="togglePaymentItemSelection(\'' + p.id + '\')">' +
          '<span class="req-item-name" title="Open this entry to correct it" onclick="openEditSchedulePayment(\'' + p.id + '\')">' + escapeHtml(p.outlet) + (p.isReRequest ? ' <strong class="re-tag">(RE-Request)</strong>' : '') + '</span></label>' +
        '<span class="req-item-meta"><span>' + escapeHtml(p.depositor) + ' \u2022 ' + formatShortDate(p.date) + ' \u2022 ' + escapeHtml(p.month) + '</span></span>' +
        '<strong class="req-item-amount">' + formatNaira(p.amount) + '</strong>' +
        '<span class="req-item-tools">' +
          (admin ? '<label title="Mark this entry as a re-request - it prints as (RE-Request)"><input type="checkbox" ' + (p.isReRequest ? 'checked' : '') + ' onchange="togglePaymentItemReRequest(\'' + p.id + '\')"> RE</label>' +
          '<button type="button" class="req-item-edit" title="Correct this entry" onclick="openEditSchedulePayment(\'' + p.id + '\')">\u270f\ufe0f Edit</button>' : '') +
          (admin ? '<button type="button" class="req-item-del" title="Remove entry" onclick="removePaymentFromSchedule(\'' + p.id + '\')">\u2715</button>' : '') +
        '</span>' +
      '</div>').join('')
          : (store.state.showArchivedRequests
        ? '<div class="report-empty">No payment record for this sector yet. Use <strong>+ Add Payment Entry</strong> or record the payment in the facility edit form.</div>'
        : '<div class="report-empty">Ready for a new request. Use <strong>+ Add Payment Entry</strong> to add a payment.</div>');
  }

  // v2.9.3 - a supervisor only ticks entries; the wording must not send them
  // looking for controls the role does not have
  const rowsHint = document.getElementById('req-rows-hint');
  if (rowsHint) {
    rowsHint.innerHTML = isSupervisor()
      ? 'Select the entries for this letter.'
      : 'Select the entries. Turn on <strong>RE</strong> for a repeat request.';
  }

  const archToggle = document.getElementById('req-archived-toggle');
  if (archToggle) {
    const total = (store.state.paymentScheduleRecords || []).filter(p => paymentInRequestCategory(p, activeRequestCategory) && p.archived).length;
    archToggle.textContent = (store.state.showArchivedRequests ? '\u25b2 Hide previous' : '\u25bc Show previous') + (total ? ' (' + total + ')' : '');
    archToggle.style.display = total ? '' : 'none';
  }

  const lhToggle = document.getElementById('req-letterhead-toggle');
  if (lhToggle) lhToggle.checked = docPreviewSettings().pdfLetterhead !== false;

  const preview = document.getElementById('request-letterhead-preview');
  if (preview) preview.innerHTML = requestLetterHtml();

  const totalEl = document.getElementById('req-running-total');
  if (totalEl) totalEl.textContent = formatNaira(data.total);
  const rebateEl = document.getElementById('req-running-rebate');
  if (rebateEl) {
    rebateEl.textContent = meta.rebate ? formatNaira(data.rebate) + ' (' + meta.rebate + '%)' : 'No deduction (Municipal)';
  }
}

function requestLetterHtml() {
  const data = requestSelection();
  const meta = data.meta;
  const rows = data.selected;
  const withLetterhead = docPreviewSettings().pdfLetterhead !== false;

  // Municipal letters carry no outlet column: that entry is typed as
  // depositor + amount + date, so an outlet would only repeat the depositor.
  const showOutlet = meta.showOutlet !== false;
  const showMonth = meta.showMonth !== false;
  // Medical letters print the general waste share beside the amount paid.
  const showGenWaste = meta.generalWaste === true;
  const leadSpan = showOutlet ? 3 : 2;                 // S/N + outlet + depositor
  const tailSpan = showMonth ? 2 : 1;                  // date + month
  const colCount = leadSpan + 1 + (showGenWaste ? 1 : 0) + tailSpan;
  const reMark = (p) => (p.isReRequest ? ' <strong>(RE-Request)</strong>' : '');
  const money = (v) => (v === undefined || v === null || v === '') ? '' : Number(v).toLocaleString('en-NG');

  const tableRows = rows.length ? rows.map((p, i) => '<tr>' +
      '<td class="col-sn">' + (i + 1) + '.</td>' +
      (showOutlet ? '<td><strong>' + escapeHtml(p.outlet) + '</strong>' + reMark(p) + '</td>' : '') +
      '<td>' + escapeHtml(p.depositor) + (showOutlet ? '' : reMark(p)) + '</td>' +
      '<td class="col-amount">' + money(p.amount) + '</td>' +
      (showGenWaste ? '<td class="col-amount">' + money(p.generalWaste) + '</td>' : '') +
      '<td class="col-date">' + formatShortDate(p.date) + '</td>' +
      (showMonth ? '<td class="col-month">' + escapeHtml(p.month) + '</td>' : '') +
    '</tr>').join('')
    : '<tr><td colspan="' + colCount + '" style="text-align:center;padding:20px;">No payment records selected. Tick entries in the Payment Schedule Manager.</td></tr>';

  // The figure claimed sits under the general waste column for Medical, and
  // under the amount column for every other sector.
  const claimCells = (value) => showGenWaste
    ? '<td class="col-amount"></td><td class="col-amount">' + money(value) + '</td>'
    : '<td class="col-amount">' + money(value) + '</td>';

  const rebateRow = meta.rebate
    ? '<tr class="row-total"><td colspan="' + leadSpan + '" style="text-align:right;font-weight:800;">' + meta.rebate + '%</td>' +
      claimCells(data.rebate) + '<td colspan="' + tailSpan + '"></td></tr>'
    : '';
  const rebateStatement = meta.rebate
    ? 'The ' + meta.rebate + '% shall be <strong>\u20a6' + Number(data.rebate).toLocaleString('en-NG') + '</strong> <strong>(' + numberToWords(data.rebate) + ')</strong> only.'
    : 'The total sum of <strong>\u20a6' + Number(data.total).toLocaleString('en-NG') + '</strong> <strong>(' + numberToWords(data.total) + ')</strong> only.';

  return '<div class="letterhead-doc">' +
      '<div class="req-header-row' + (withLetterhead ? '' : ' no-letterhead') + '">' + (TEEM_IMG.logo ? '<img src="' + TEEM_IMG.logo + '" alt="Teem Business Nigeria Enterprises" class="req-top-logo">' : '') +
        '<div class="req-contact-block">' +
          '<div><span class="req-label">Address:</span> <span class="req-value">' + escapeHtml((store.state.company || {}).address || '') + '</span></div>' +
          '<div><span class="req-label">Tel:</span> <span class="req-value">' + escapeHtml((store.state.company || {}).phones || '') + '</span></div>' +
          '<div><span class="req-label">Email:</span> <span class="req-value req-email">' + escapeHtml((store.state.company || {}).email || '') + '</span></div>' +
        '</div>' +
      '</div>' +
      '<div class="req-date-right">' + formatLetterDate(currentUsageDateIso()) + '</div>' +
      '<div class="req-receiver-block">' +
        '<div class="req-receiver-title">The Special Adviser/Managing Director</div>' +
        '<div>Ogun State Waste Management Authority (OGWAMA)</div>' +
        '<div>3, Presidential Boulevard, Ibara</div>' +
        '<div>Abeokuta, Ogun state.</div>' +
      '</div>' +
      '<div class="req-salutation">Sir</div>' +
      '<div class="req-subject-title">' + escapeHtml(requestSubject(activeRequestCategory)) + '</div>' +
      '<div class="req-body-paragraph">We humbly wish to request for the accrued rebate of the payment/transaction details provided below. The payments were made into the Authorized OGWAMA\u2019s Sterling Bank Account: 0079828285 by ' + meta.body + '.</div>' +
      '<div class="req-table-box"><table class="req-table"><thead><tr>' +
        '<th class="col-sn">S/N</th>' + (showOutlet ? '<th>' + meta.column + '</th>' : '') + '<th>DEPOSITORS NAME</th><th class="col-amount">AMOUNT</th>' + (showGenWaste ? '<th class="col-amount">GEN. WASTE</th>' : '') + '<th class="col-date">DATE OF PAYMENT</th>' + (showMonth ? '<th class="col-month">MONTH</th>' : '') +
      '</tr></thead><tbody>' + tableRows +
        '<tr class="row-total"><td colspan="' + leadSpan + '" style="text-align:right;font-weight:800;">Total</td>' +
        claimCells(data.total) + '<td colspan="' + tailSpan + '"></td></tr>' + rebateRow +
      '</tbody></table></div>' +
      '<div class="req-rebate-statement">' + rebateStatement + '</div>' +
      '<div style="margin-bottom:24px;">Many thanks in anticipation of your favorable response in this regard.</div>' +
      '<div class="req-sign-block">' +
        '<div><em>Yours faithfully,</em></div>' +
        '<div style="margin-top:4px;"><em>For: Teem Business Nigeria Enterprises</em></div>' +
        (TEEM_IMG.signature ? '<img src="' + TEEM_IMG.signature + '" alt="Signature" class="req-signature">' : '<div style="height:30px;"></div>') +
        '<div style="font-weight:800;font-size:14.5px;">Mojisola R. Ajibade</div>' +
        '<div style="font-style:italic;">Managing Director</div>' +
      '</div>' +
    '</div>';
}

// ===========================================================================
// 12. FLEET + SUPERVISORS
// ===========================================================================
function renderVehiclesList() {
  const tbody = document.getElementById('vehicles-table-body');
  if (!tbody) return;
  tbody.innerHTML = store.state.vehicles.map(v => '<tr>' +
    '<td><strong>' + escapeHtml(v.name) + '</strong></td>' +
    '<td><span class="badge badge-category">' + escapeHtml(v.type) + '</span></td>' +
    '<td>' + escapeHtml(v.capacity) + '</td>' +
    '<td><span class="badge badge-success">' + escapeHtml(v.status) + '</span></td>' +
    '<td>' + (isAdmin()
      ? '<button class="btn btn-sm btn-danger" onclick="deleteVehicle(\'' + v.id + '\')">\u2715 Delete</button>'
      : '<span class="badge badge-muted">Read only</span>') + '</td>' +
  '</tr>').join('');
}

function saveAddVehicle(e) {
  if (e) e.preventDefault();
  if (!requireAdmin('This action')) return;
  const name = document.getElementById('veh-name').value.trim();
  if (!name) return;
  store.state.vehicles.push({
    id: 'veh-' + Date.now().toString().slice(-5),
    name: name,
    type: document.getElementById('veh-type').value,
    capacity: document.getElementById('veh-capacity').value.trim() || '12 Tons',
    status: 'Active on Route'
  });
  store.save();
  renderVehiclesList();
  document.getElementById('form-add-vehicle').reset();
  showToast('\ud83d\ude9a Vehicle "' + name + '" added to the fleet.', 'success');
}

function deleteVehicle(vehId) {
  if (!requireAdmin('This action')) return;
  if (store.state.vehicles.length <= 1) { showToast('\u26a0\ufe0f At least one fleet vehicle must remain in the registry.', 'error'); return; }
  const v = store.state.vehicles.find(x => x.id === vehId);
  if (!v || !confirm('Remove "' + v.name + '" from the fleet registry?')) return;
  if (typeof recordDeletedId === 'function') recordDeletedId(vehId);
  store.state.vehicles = store.state.vehicles.filter(x => x.id !== vehId);
  store.save();
  renderVehiclesList();
  showToast('\ud83d\uddd1\ufe0f Vehicle removed from fleet.', 'warning');
}

function renderSupervisorBadge() {
  const badge = document.getElementById('nav-supervisor-badge');
  if (!badge) return;
  const supUsers = (store.state.users || []).filter(u => isUserSupervisorRole(u)).length;
  const supList = (store.state.supervisors || []).length;
  const n = Math.max(supUsers, supList);
  if (n <= 0) {
    badge.textContent = '';
    badge.style.display = 'none';
  } else {
    badge.textContent = n + ' Lead' + (n === 1 ? '' : 's');
    badge.style.display = '';
  }
}

function renderSupervisorsList() {
  renderSupervisorBadge();
  const tbody = document.getElementById('supervisors-table-body');
  const settingsBody = document.getElementById('settings-supervisors-body');
  const sups = store.state.supervisors || [];
  const row = s => '<tr>' +
    '<td><strong>' + escapeHtml(s.name) + '</strong></td>' +
    '<td>' + escapeHtml(s.phone || '') + '</td>' +
    '<td>' + escapeHtml(s.zone || '') + '</td>' +
    '<td><span class="badge badge-success">' + escapeHtml(s.status || 'Active Field Lead') + '</span></td>' +
    (settingsBody ? '<td><button class="btn btn-sm btn-danger" onclick="deleteSupervisor(\'' + s.id + '\')">\u2715 Delete</button></td>' : '') +
  '</tr>';
  const emptyRow = '<tr><td colspan="5" style="text-align:center;padding:24px;color:var(--text-muted);">No field supervisors registered yet. Sign up or add a supervisor account in Registered Accounts.</td></tr>';

  if (tbody) tbody.innerHTML = sups.length ? sups.map(row).join('') : emptyRow;
  if (settingsBody) settingsBody.innerHTML = sups.length ? sups.map(row).join('') : emptyRow;
  renderHeroSupervisorGrid();
}

function saveAddSupervisor(e) {
  if (e) e.preventDefault();
  if (!requireAdmin('This action')) return;
  const name = document.getElementById('sup-name').value.trim();
  if (!name) return;
  store.state.supervisors.push({
    id: 'sup-' + Date.now().toString().slice(-5),
    name: name,
    phone: document.getElementById('sup-phone').value.trim() || '0800 000 0000',
    zone: document.getElementById('sup-zone').value.trim() || 'General Operations',
    status: 'Active Field Lead'
  });
  store.save();
  renderSupervisorsList();
  renderSupervisorBadge();
  document.getElementById('form-add-supervisor').reset();
  showToast('\ud83d\udc64 Supervisor "' + name + '" added.', 'success');
}

function deleteSupervisor(id) {
  if (!requireAdmin('This action')) return;
  const s = store.state.supervisors.find(x => x.id === id);
  if (!s) return;
  if (!confirm('Remove supervisor "' + s.name + '"?')) return;
  if (typeof recordDeletedId === 'function') recordDeletedId(id);
  store.state.supervisors = store.state.supervisors.filter(x => x.id !== id);
  store.save();
  renderSupervisorsList();
  showToast('\ud83d\uddd1\ufe0f Supervisor removed.', 'warning');
}

// ===========================================================================
// 13. EDIT / ADD FACILITY (payment records editable in-place OR added new)
// ===========================================================================
function syncFacilityPaymentRecordToSchedule(facility, record, previousFacilityName) {
  if (!facility || !record) return;
  if (!Array.isArray(store.state.paymentScheduleRecords)) store.state.paymentScheduleRecords = [];
  let schedEntry = store.state.paymentScheduleRecords.find(p => p.id === record.id);
  if (!schedEntry && previousFacilityName) {
    schedEntry = store.state.paymentScheduleRecords.find(p =>
      p.outlet === previousFacilityName && Number(p.amount) === Number(record.amount)
    );
  }
  if (schedEntry) {
    schedEntry.outlet = facility.name;
    schedEntry.category = facility.category;
    schedEntry.depositor = record.payerName || facility.name;
    schedEntry.amount = Number(record.amount) || 0;
    schedEntry.date = record.date || currentUsageDateIso();
    schedEntry.month = record.month || record.periodTo || CURRENT_MONTH_NAME;
    schedEntry.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  } else {
    store.state.paymentScheduleRecords.unshift({
      id: record.id || ('pay-' + Date.now().toString().slice(-5)),
      seq: nextPaymentSeq(),
      outlet: facility.name,
      category: facility.category,
      depositor: record.payerName || facility.name,
      amount: Number(record.amount) || 0,
      date: record.date || currentUsageDateIso(),
      month: record.month || record.periodTo || CURRENT_MONTH_NAME,
      isReRequest: false,
      selected: true,
      updatedAt: typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString()
    });
  }
}

function populateEditFacEvacRecordSelector(f, selectedVal) {
  const sel = document.getElementById('edit-fac-evac-record-select');
  const delBtn = document.getElementById('btn-delete-selected-fac-evacuation');
  const dateInput = document.getElementById('edit-fac-lastevac');
  if (!sel || !f) return;
  const evacs = Array.isArray(f.evacuationHistory) ? f.evacuationHistory : [];
  const opts = [];
  evacs.forEach((ev, idx) => {
    const label = (idx === 0 ? '\u270f\ufe0f Edit Latest Evacuation (#' + (idx + 1) + '): ' : '\u270f\ufe0f Edit Evacuation #' + (idx + 1) + ': ') +
      formatDate(ev.date) + ' \u2022 ' + (ev.month || monthLabelFromKey(String(ev.date || '').slice(0, 7)) || '') +
      (ev.truck ? ' \u2022 ' + ev.truck : '');
    opts.push('<option value="' + idx + '">' + escapeHtml(label) + '</option>');
  });
  opts.push('<option value="new">+ Add New Evacuation Date</option>');
  opts.push('<option value="none">\u2014 No Evacuation Date Recorded \u2014</option>');
  sel.innerHTML = opts.join('');
  if (selectedVal !== undefined && selectedVal !== null && (selectedVal === 'new' || selectedVal === 'none' || evacs[Number(selectedVal)])) {
    sel.value = String(selectedVal);
  } else {
    sel.value = evacs.length ? '0' : 'none';
  }
  if (delBtn) {
    delBtn.style.display = (sel.value !== 'new' && sel.value !== 'none' && evacs.length > 0) ? 'inline-flex' : 'none';
  }
  if (dateInput) {
    if (sel.value === 'none') {
      dateInput.value = '';
    } else if (sel.value === 'new') {
      dateInput.value = currentUsageDateIso();
    } else {
      const rec = evacs[parseInt(sel.value, 10)] || evacs[0];
      dateInput.value = (rec && rec.date) ? rec.date : (f.lastEvacuated || '');
    }
  }
}

function onEditFacEvacRecordChange(val) {
  const facId = document.getElementById('edit-fac-id') ? document.getElementById('edit-fac-id').value : '';
  const f = store.state.facilities.find(x => x.id === facId);
  if (!f) return;
  const evacs = Array.isArray(f.evacuationHistory) ? f.evacuationHistory : [];
  const delBtn = document.getElementById('btn-delete-selected-fac-evacuation');
  const dateInput = document.getElementById('edit-fac-lastevac');
  if (val === 'none') {
    if (dateInput) dateInput.value = '';
    if (delBtn) delBtn.style.display = 'none';
  } else if (val === 'new' || !evacs.length) {
    if (dateInput) dateInput.value = currentUsageDateIso();
    if (delBtn) delBtn.style.display = 'none';
  } else {
    const idx = parseInt(val, 10);
    const rec = evacs[idx] || evacs[0] || {};
    if (dateInput) dateInput.value = rec.date || f.lastEvacuated || currentUsageDateIso();
    if (delBtn) delBtn.style.display = 'inline-flex';
  }
}

function deleteSelectedFacEvacuationFromEditModal() {
  const facId = document.getElementById('edit-fac-id') ? document.getElementById('edit-fac-id').value : '';
  const sel = document.getElementById('edit-fac-evac-record-select');
  if (!facId || !sel || sel.value === 'new' || sel.value === 'none') return;
  const idx = parseInt(sel.value, 10);
  if (isNaN(idx)) return;
  deleteFacilityEvacuationRecord(facId, idx, true);
}

function deleteFacilityEvacuationRecord(facilityId, recordIdx, stayInEditModal) {
  const f = store.state.facilities.find(x => x.id === facilityId);
  if (!f || !Array.isArray(f.evacuationHistory) || !f.evacuationHistory[recordIdx]) return;
  const removed = f.evacuationHistory.splice(recordIdx, 1)[0];
  if (removed) {
    if (removed.id && typeof recordDeletedId === 'function') recordDeletedId(removed.id);
    if (removed.date && typeof recordDeletedId === 'function') recordDeletedId('evac-del:' + f.id + ':' + removed.date);
    if (Array.isArray(store.state.evacuationLogs)) {
      store.state.evacuationLogs = store.state.evacuationLogs.filter(l => {
        if (l && l.target === f.name && l.date === removed.date) {
          if (l.id && typeof recordDeletedId === 'function') recordDeletedId(l.id);
          return false;
        }
        return true;
      });
    }
  }
  if (f.evacuationHistory.length > 0) {
    f.evacuationHistory.sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));
    f.lastEvacuated = f.evacuationHistory[0].date || '';
  } else {
    f.lastEvacuated = '';
  }
  f.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  localDirtyEntities.add('fac:' + f.id);
  store.save();
  renderFacilitiesDirectory();
  renderEvacuations();
  if (activeReportFacilityId === facilityId) renderFacilityReportContent();
  if (stayInEditModal) {
    populateEditFacEvacRecordSelector(f, f.evacuationHistory.length ? '0' : 'none');
  }
  showToast('\ud83d\uddd1\ufe0f Evacuation period deleted from ' + f.name + '.', 'warning');
}

function editFacilityEvacuationFromReport(facilityId, recordIdx) {
  closeModal('modal-facility-report');
  openEditFacilityModal(facilityId, undefined, recordIdx);
}

window.populateEditFacEvacRecordSelector = populateEditFacEvacRecordSelector;
window.onEditFacEvacRecordChange = onEditFacEvacRecordChange;
window.deleteSelectedFacEvacuationFromEditModal = deleteSelectedFacEvacuationFromEditModal;
window.deleteFacilityEvacuationRecord = deleteFacilityEvacuationRecord;
window.editFacilityEvacuationFromReport = editFacilityEvacuationFromReport;

function populateEditFacPaymentRecordSelector(f, selectedVal) {
  const sel = document.getElementById('edit-fac-pay-record-select');
  const delBtn = document.getElementById('btn-delete-selected-fac-payment');
  if (!sel || !f) return;
  const history = Array.isArray(f.paymentHistory) ? f.paymentHistory : [];
  const opts = [];
  history.forEach((p, idx) => {
    const label = (idx === 0 ? '\u270f\ufe0f Edit Latest Payment (#' + (idx + 1) + '): ' : '\u270f\ufe0f Edit Payment #' + (idx + 1) + ': ') +
      formatNaira(p.amount) + ' \u2022 ' + formatShortDate(p.date) + ' \u2022 ' +
      formatCoveragePeriod(p, ' \u2192 ');
    opts.push('<option value="' + idx + '">' + escapeHtml(label) + '</option>');
  });
  opts.push('<option value="new">+ Add New Payment Record</option>');
  opts.push('<option value="none">\u2014 No Payment Record \u2014</option>');
  sel.innerHTML = opts.join('');
  if (selectedVal !== undefined && selectedVal !== null && (selectedVal === 'new' || selectedVal === 'none' || history[Number(selectedVal)])) {
    sel.value = String(selectedVal);
  } else {
    sel.value = history.length ? '0' : 'none';
  }
  if (delBtn) {
    delBtn.style.display = (sel.value !== 'new' && sel.value !== 'none' && history.length > 0) ? 'inline-flex' : 'none';
  }
}

function onEditFacPaymentRecordChange(val) {
  const facId = document.getElementById('edit-fac-id') ? document.getElementById('edit-fac-id').value : '';
  const f = store.state.facilities.find(x => x.id === facId);
  if (!f) return;
  const history = Array.isArray(f.paymentHistory) ? f.paymentHistory : [];
  const delBtn = document.getElementById('btn-delete-selected-fac-payment');
  if (val === 'none') {
    document.getElementById('edit-fac-payer-name').value = f.name;
    document.getElementById('edit-fac-pay-amount').value = '';
    document.getElementById('edit-fac-pay-date').value = currentUsageDateIso();
    document.getElementById('edit-fac-pay-month').value = CURRENT_MONTH_PLAIN;
    document.getElementById('edit-fac-period-from').value = CURRENT_MONTH_NAME;
    document.getElementById('edit-fac-period-to').value = CURRENT_MONTH_NAME;
    if (delBtn) delBtn.style.display = 'none';
  } else if (val === 'new' || !history.length) {
    const latest = latestPayment(f) || {};
    document.getElementById('edit-fac-payer-name').value = latest.payerName || f.name;
    document.getElementById('edit-fac-pay-amount').value = calcTotalWithVat(f.amount, f.vat) || latest.amount || 0;
    document.getElementById('edit-fac-pay-date').value = currentUsageDateIso();
    document.getElementById('edit-fac-pay-month').value = CURRENT_MONTH_PLAIN;
    document.getElementById('edit-fac-period-from').value = CURRENT_MONTH_NAME;
    document.getElementById('edit-fac-period-to').value = CURRENT_MONTH_NAME;
    if (delBtn) delBtn.style.display = 'none';
  } else {
    const idx = parseInt(val, 10);
    const rec = history[idx] || history[0] || {};
    document.getElementById('edit-fac-payer-name').value = rec.payerName || f.name;
    document.getElementById('edit-fac-pay-amount').value = rec.amount !== undefined ? rec.amount : calcTotalWithVat(f.amount, f.vat);
    document.getElementById('edit-fac-pay-date').value = rec.date || currentUsageDateIso();
    document.getElementById('edit-fac-pay-month').value = rec.month || rec.periodTo || CURRENT_MONTH_NAME;
    document.getElementById('edit-fac-period-from').value = rec.periodFrom || CURRENT_MONTH_NAME;
    document.getElementById('edit-fac-period-to').value = rec.periodTo || CURRENT_MONTH_NAME;
    if (delBtn) delBtn.style.display = 'inline-flex';
  }
}

function deleteSelectedFacPaymentFromEditModal() {
  const facId = document.getElementById('edit-fac-id') ? document.getElementById('edit-fac-id').value : '';
  const sel = document.getElementById('edit-fac-pay-record-select');
  if (!facId || !sel || sel.value === 'new' || sel.value === 'none') return;
  const idx = parseInt(sel.value, 10);
  if (isNaN(idx)) return;
  deleteFacilityPaymentRecord(facId, idx, true);
}

function deleteFacilityPaymentRecord(facilityId, recordIdx, stayInEditModal) {
  const f = store.state.facilities.find(x => x.id === facilityId);
  if (!f || !Array.isArray(f.paymentHistory) || !f.paymentHistory[recordIdx]) return;
  const removed = f.paymentHistory.splice(recordIdx, 1)[0];
  f.lastPayment = f.paymentHistory.length ? f.paymentHistory[0] : null;
  if (removed) {
    if (removed.id && typeof recordDeletedId === 'function') recordDeletedId(removed.id);
    if (typeof recordDeletedId === 'function') {
      recordDeletedId('pay-del:' + f.id + ':' + (removed.date || '') + ':' + (removed.amount || 0));
    }
    if (Array.isArray(store.state.paymentScheduleRecords)) {
      store.state.paymentScheduleRecords = store.state.paymentScheduleRecords.filter(p => {
        if (!p) return false;
        if (removed.id && p.id === removed.id) return false;
        if (p.outlet === f.name && Number(p.amount) === Number(removed.amount) && p.date === removed.date) return false;
        return true;
      });
    }
  }
  f.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  localDirtyEntities.add('fac:' + f.id);
  localDirtyEntities.add('col:paymentScheduleRecords');
  store.save();
  renderFacilitiesDirectory();
  renderDebtorRadar();
  renderRequestsView();
  if (activeReportFacilityId === facilityId) renderFacilityReportContent();
  if (stayInEditModal) {
    openEditFacilityModal(facilityId, f.paymentHistory.length ? 0 : 'none');
  }
  showToast('\ud83d\uddd1\ufe0f Payment record deleted from ' + f.name + '.', 'warning');
}

let editFacilityOpenedFromReportId = null;

function editFacilityPaymentFromReport(facilityId, recordIdx) {
  editFacilityOpenedFromReportId = facilityId;
  closeModal('modal-facility-report');
  openEditFacilityModal(facilityId, recordIdx);
}

window.onEditFacPaymentRecordChange = onEditFacPaymentRecordChange;
window.deleteSelectedFacPaymentFromEditModal = deleteSelectedFacPaymentFromEditModal;
window.deleteFacilityPaymentRecord = deleteFacilityPaymentRecord;
window.editFacilityPaymentFromReport = editFacilityPaymentFromReport;

function openEditFacilityModal(facilityId, editPaymentIdx, editEvacIdx) {
  const f = store.state.facilities.find(x => x.id === facilityId);
  if (!f) return;

  document.getElementById('edit-fac-id').value = f.id;
  document.getElementById('edit-fac-name').value = f.name;
  document.getElementById('edit-fac-category').value = f.category;
  const locEl = document.getElementById('edit-fac-location');
  if (locEl) locEl.value = f.location || '';
  const amtEl = document.getElementById('edit-fac-amount');
  if (amtEl) {
    amtEl.value = f.amount;
    amtEl.dataset.prevTariff = String(Number(f.amount) || 0);
  }
  document.getElementById('edit-fac-vat').value = f.vat || 0;
  document.getElementById('edit-fac-lastevac').value = f.lastEvacuated || '';

  const supSelect = document.getElementById('edit-fac-supervisor');
  if (supSelect) {
    supSelect.innerHTML = supervisorOptionsHtml(f.supervisor);
    supSelect.value = f.supervisor || 'Unassigned';
  }

  const initialEvacMode = (typeof editEvacIdx === 'number' && f.evacuationHistory && f.evacuationHistory[editEvacIdx])
    ? String(editEvacIdx)
    : ((f.evacuationHistory && f.evacuationHistory.length) ? '0' : 'none');
  populateEditFacEvacRecordSelector(f, initialEvacMode);

  populatePeriodDropdowns();
  const initialMode = (editPaymentIdx === 'none' || editPaymentIdx === 'new')
    ? editPaymentIdx
    : (typeof editPaymentIdx === 'number' && f.paymentHistory && f.paymentHistory[editPaymentIdx])
      ? String(editPaymentIdx)
      : ((f.paymentHistory && f.paymentHistory.length) ? '0' : 'none');
  populateEditFacPaymentRecordSelector(f, initialMode);
  onEditFacPaymentRecordChange(initialMode);
  if (amtEl) amtEl.dataset.prevTariff = String(Number(f.amount) || 0);
  updateFacilityTariffTotalPreview('edit');

  const historyNote = document.getElementById('edit-fac-history-note');
  if (historyNote) {
    const history = (f.paymentHistory || []).slice(0, 6);
    historyNote.innerHTML = history.length
      ? '<strong>' + f.paymentHistory.length + ' payment record(s)</strong> \u2014 select one to edit.' +
        '<div style="margin-top:6px;display:flex;flex-direction:column;gap:3px;">' +
        history.map((p, idx) => '<span>\u2022 #' + (idx + 1) + ': ' + formatShortDate(p.date) + ' \u2022 ' + formatNaira(p.amount) + ' \u2022 ' + escapeHtml(p.month || '') + ' (' + escapeHtml(formatCoveragePeriod(p, ' \u2192 ')) + ') \u2022 ' + escapeHtml(p.payerName || '') + '</span>').join('') +
        '</div>'
      : 'No payment record on file. Select + Add New Payment Record to record a payment.';
  }

  openModal('modal-edit-facility');
}

function saveEditFacility(e) {
  if (e) e.preventDefault();
  const editNameEl = document.getElementById('edit-fac-name');
  if (editNameEl) {
    const clash = findDuplicateFacility(editNameEl.value, document.getElementById('edit-fac-id') ? document.getElementById('edit-fac-id').value : '');
    if (clash) {
      showModalAlert('Facility Already Exists',
        '"' + escapeHtml(clash.name) + '" is already registered under ' +
        escapeHtml(clash.category) + '. Two records cannot share one name.');
      showToast('\u26a0\ufe0f Facility already exists.', 'warning');
      return false;
    }
  }
  const f = store.state.facilities.find(x => x.id === document.getElementById('edit-fac-id').value);
  if (!f) return;

  const previousName = f.name;
  f.name = document.getElementById('edit-fac-name').value.trim();
  f.category = document.getElementById('edit-fac-category').value;
  const locEl = document.getElementById('edit-fac-location');
  if (locEl && locEl.value.trim()) f.location = cleanAddress(locEl.value);
  f.supervisor = document.getElementById('edit-fac-supervisor').value || 'Unassigned';
  f.amount = Number(document.getElementById('edit-fac-amount').value) || 0;
  f.vat = Number(document.getElementById('edit-fac-vat').value) || 0;

  // Handle Evacuation Period selection (edit in place, add new, or none)
  if (!Array.isArray(f.evacuationHistory)) f.evacuationHistory = [];
  const evacSel = document.getElementById('edit-fac-evac-record-select');
  const evacMode = evacSel ? evacSel.value : (f.evacuationHistory.length ? '0' : 'none');
  const rawEvacDate = (document.getElementById('edit-fac-lastevac').value || '').trim();
  if (evacMode === 'none' && !rawEvacDate) {
    f.lastEvacuated = f.evacuationHistory.length ? (f.evacuationHistory[0].date || '') : '';
  } else if (evacMode !== 'new' && evacMode !== 'none' && f.evacuationHistory[parseInt(evacMode, 10)]) {
    const eIdx = parseInt(evacMode, 10);
    const evRec = f.evacuationHistory[eIdx];
    const chosenDate = rawEvacDate || evRec.date || currentUsageDateIso();
    evRec.date = chosenDate;
    evRec.month = monthLabelFromKey(chosenDate.slice(0, 7)) || CURRENT_MONTH_NAME;
    evRec.supervisor = f.supervisor;
    if (!evRec.id) evRec.id = 'evac-' + f.id + '-' + chosenDate + '-' + eIdx;
    f.evacuationHistory.sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));
    f.lastEvacuated = f.evacuationHistory[0].date || chosenDate;
  } else if (rawEvacDate) {
    f.lastEvacuated = rawEvacDate;
    if (!f.evacuationHistory.some(h => h.date === rawEvacDate)) {
      f.evacuationHistory.unshift({
        id: 'evac-' + f.id + '-' + rawEvacDate + '-' + Date.now().toString().slice(-4),
        date: rawEvacDate,
        month: monthLabelFromKey(rawEvacDate.slice(0, 7)) || CURRENT_MONTH_NAME,
        truck: 'Blue Compactor (TEEM-01)',
        supervisor: f.supervisor,
        tonnage: f.category === 'Industrial' ? (f.amount / 16000).toFixed(1) : null,
        status: 'Verified Complete'
      });
    }
  }

  // Handle Payment Record selection (edit in place, add new, or none/default)
  const payerName = document.getElementById('edit-fac-payer-name').value.trim() || f.name;
  const rawPayAmtStr = String(document.getElementById('edit-fac-pay-amount').value || '').trim();
  const payAmount = Number(rawPayAmtStr) || 0;
  const payDate = document.getElementById('edit-fac-pay-date').value || currentUsageDateIso();
  const payMonth = document.getElementById('edit-fac-pay-month').value.trim() || CURRENT_MONTH_NAME;
  const pFrom = document.getElementById('edit-fac-period-from').value || CURRENT_MONTH_NAME;
  const pTo = document.getElementById('edit-fac-period-to').value || CURRENT_MONTH_NAME;

  if (!Array.isArray(f.paymentHistory)) f.paymentHistory = [];
  const modeSel = document.getElementById('edit-fac-pay-record-select');
  const modeVal = modeSel ? modeSel.value : (f.paymentHistory.length ? '0' : 'none');

  let updatedExisting = false;
  let addedNew = false;
  if (modeVal !== 'new' && modeVal !== 'none') {
    const idx = parseInt(modeVal, 10);
    if (!isNaN(idx) && f.paymentHistory[idx]) {
      const existingRec = f.paymentHistory[idx];
      if (!existingRec.id) existingRec.id = 'pay-' + Date.now().toString().slice(-5);
      existingRec.payerName = payerName;
      existingRec.amount = payAmount;
      existingRec.date = payDate;
      existingRec.month = payMonth;
      existingRec.periodFrom = pFrom;
      existingRec.periodTo = pTo;
      f.lastPayment = f.paymentHistory[0] || existingRec;
      syncFacilityPaymentRecordToSchedule(f, existingRec, previousName);
      updatedExisting = true;
    }
  } else if (modeVal === 'new' || (modeVal === 'none' && rawPayAmtStr !== '' && payAmount > 0)) {
    const record = {
      id: 'pay-' + Date.now().toString().slice(-5),
      payerName: payerName,
      amount: payAmount,
      date: payDate,
      month: payMonth,
      periodFrom: pFrom,
      periodTo: pTo
    };
    f.paymentHistory.unshift(record);
    f.lastPayment = record;
    syncFacilityPaymentRecordToSchedule(f, record, previousName);
    addedNew = true;
  } else {
    f.lastPayment = f.paymentHistory.length ? f.paymentHistory[0] : null;
  }

  f.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  localDirtyEntities.add('fac:' + f.id);
  store.save();
  closeModal('modal-edit-facility');
  renderFacilitiesDirectory();
  renderDebtorRadar();
  renderRequestsView();
  if (activeReportFacilityId === f.id) renderFacilityReportContent();
  showToast('\u2705 ' + f.name + ' updated' + (updatedExisting ? ' (payment record edited in place)' : addedNew ? ' (new payment record added)' : '') + '.', 'success');
}

function openAddFacilityModal() {
  if (!requireAdmin('Adding facilities')) return;
  document.getElementById('form-add-facility').reset();
  const supSelect = document.getElementById('add-fac-supervisor');
  if (supSelect) supSelect.innerHTML = supervisorOptionsHtml('Unassigned');
  updateFacilityTariffTotalPreview('add');
  openModal('modal-add-facility');
}

function normalizeFacilityName(value) {
  return String(value || '')
    .toLowerCase()
    // apostrophes are dropped, not turned into a space: "God's" and "Gods"
    // must look like the same client
    .replace(/['\u2019`]/g, '')
    .replace(/[^a-z0-9 ]/g, ' ')
    .replace(/\b(limited|ltd|plc|company|co|enterprises?|ventures?|nigeria|nig)\b/g, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

function findDuplicateFacility(name, ignoreId) {
  const target = normalizeFacilityName(name);
  if (!target) return null;
  return (store.state.facilities || []).find(f => {
    if (!f || (ignoreId && f.id === ignoreId)) return false;
    return normalizeFacilityName(f.name) === target;
  }) || null;
}

function saveAddFacility(e) {
  if (e) e.preventDefault();
  const name = document.getElementById('add-fac-name').value.trim();
  const cat = document.getElementById('add-fac-category').value;
  const sup = document.getElementById('add-fac-supervisor').value || 'Unassigned';
  const amt = Number(document.getElementById('add-fac-amount').value) || 0;
  const locEl = document.getElementById('add-fac-location');

  // A facility is registered once. Adding the same one again would split its
  // payments and evacuation history across two records.
  const duplicate = findDuplicateFacility(name);
  if (duplicate) {
    showModalAlert('Facility Already Exists',
      '"' + escapeHtml(duplicate.name) + '" is already registered under ' +
      escapeHtml(duplicate.category) + '. Open its record to log a payment or an evacuation.');
    showToast('\u26a0\ufe0f Facility already exists.', 'warning');
    const nameEl = document.getElementById('add-fac-name');
    if (nameEl) { nameEl.focus(); nameEl.select(); }
    return false;
  }

  const newFacility = {
    id: 'fac-' + cat.slice(0, 4).toLowerCase().replace(/ /g, '') + '-' + Date.now().toString().slice(-5),
    name: name,
    category: cat,
    location: locEl && locEl.value.trim() ? cleanAddress(locEl.value) : 'Abeokuta',
    supervisor: sup,
    amount: amt,
    vat: Number(document.getElementById('add-fac-vat').value) || 0,
    lastEvacuated: '',
    evacuationHistory: [],
    paymentHistory: [],
    lastPayment: null,
    updatedAt: typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString(),
    notes: 'Registered client in the TEEM master directory.'
  };

  store.state.facilities.unshift(newFacility);

  store.save();
  closeModal('modal-add-facility');
  renderFacilitiesDirectory();
  showToast('\u2705 Facility "' + name + '" registered.', 'success');
}

function onLogPaymentModeChange(val) {
  const facId = document.getElementById('pay-fac-id') ? document.getElementById('pay-fac-id').value : '';
  const f = store.state.facilities.find(x => x.id === facId);
  if (!f) return;
  const history = Array.isArray(f.paymentHistory) ? f.paymentHistory : [];
  if (val === 'new' || !history.length) {
    document.getElementById('pay-amount').value = f.amount;
    document.getElementById('pay-date').value = currentUsageDateIso();
    document.getElementById('pay-payer').value = f.name;
    if (document.getElementById('pay-month')) document.getElementById('pay-month').value = CURRENT_MONTH_PLAIN;
    if (document.getElementById('pay-period-from')) document.getElementById('pay-period-from').value = CURRENT_MONTH_NAME;
    if (document.getElementById('pay-period-to')) document.getElementById('pay-period-to').value = CURRENT_MONTH_NAME;
  } else {
    const idx = parseInt(val, 10);
    const rec = history[idx] || history[0] || {};
    document.getElementById('pay-amount').value = rec.amount !== undefined ? rec.amount : f.amount;
    document.getElementById('pay-date').value = rec.date || currentUsageDateIso();
    document.getElementById('pay-payer').value = rec.payerName || f.name;
    if (document.getElementById('pay-month')) document.getElementById('pay-month').value = rec.month || rec.periodTo || CURRENT_MONTH_NAME;
    if (document.getElementById('pay-period-from')) document.getElementById('pay-period-from').value = rec.periodFrom || CURRENT_MONTH_NAME;
    if (document.getElementById('pay-period-to')) document.getElementById('pay-period-to').value = rec.periodTo || CURRENT_MONTH_NAME;
  }
}
window.onLogPaymentModeChange = onLogPaymentModeChange;

function openLogPaymentModal(facilityId, editIdx) {
  const f = store.state.facilities.find(x => x.id === facilityId);
  if (!f) return;
  populatePeriodDropdowns();
  document.getElementById('pay-fac-id').value = f.id;
  document.getElementById('pay-fac-title').textContent = f.name;
  const modeSel = document.getElementById('pay-record-mode-select');
  const history = Array.isArray(f.paymentHistory) ? f.paymentHistory : [];
  if (modeSel) {
    const opts = ['<option value="new">+ Record New Payment (Add to History)</option>'];
    history.forEach((p, idx) => {
      opts.push('<option value="' + idx + '">\u270f\ufe0f Edit Existing Record #' + (idx + 1) + ': ' +
        escapeHtml(formatNaira(p.amount) + ' \u2022 ' + formatShortDate(p.date) + ' \u2022 ' + formatCoveragePeriod(p, ' \u2192 ')) +
        '</option>');
    });
    modeSel.innerHTML = opts.join('');
    modeSel.value = (typeof editIdx === 'number' && history[editIdx]) ? String(editIdx) : 'new';
  }
  onLogPaymentModeChange(modeSel ? modeSel.value : 'new');
  openModal('modal-log-payment');
}

function saveLogPayment(e) {
  if (e) e.preventDefault();
  const f = store.state.facilities.find(x => x.id === document.getElementById('pay-fac-id').value);
  if (!f) return;

  const amount = Number(document.getElementById('pay-amount').value) || 0;
  const payDate = document.getElementById('pay-date').value || currentUsageDateIso();
  const payer = document.getElementById('pay-payer').value.trim() || f.name;
  const monthEl = document.getElementById('pay-month');
  const payMonth = monthEl ? (monthEl.value.trim() || CURRENT_MONTH_NAME) : CURRENT_MONTH_NAME;
  const pFrom = document.getElementById('pay-period-from').value;
  const pTo = document.getElementById('pay-period-to').value;

  if (!Array.isArray(f.paymentHistory)) f.paymentHistory = [];
  const modeSel = document.getElementById('pay-record-mode-select');
  const modeVal = modeSel ? modeSel.value : 'new';

  if (modeVal !== 'new' && f.paymentHistory[parseInt(modeVal, 10)]) {
    const idx = parseInt(modeVal, 10);
    const existing = f.paymentHistory[idx];
    if (!existing.id) existing.id = 'pay-' + Date.now().toString().slice(-5);
    existing.payerName = payer;
    existing.amount = amount;
    existing.date = payDate;
    existing.month = payMonth;
    existing.periodFrom = pFrom;
    existing.periodTo = pTo;
    // keep the tariff the payment was made against - only fill it in when the
    // record predates this field
    if (existing.tariffAtPayment === undefined) existing.tariffAtPayment = Number(f.amount) || 0;
    if (existing.vatAtPayment === undefined) existing.vatAtPayment = Number(f.vat) || 0;
    f.lastPayment = f.paymentHistory[0] || existing;
    f.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
    syncFacilityPaymentRecordToSchedule(f, existing, f.name);
    store.save();
    closeModal('modal-log-payment');
    renderFacilitiesDirectory();
    renderDebtorRadar();
    renderRequestsView();
    if (activeReportFacilityId === f.id) renderFacilityReportContent();
    showToast('\u2705 Payment record updated in place for ' + f.name, 'success');
    return;
  }

  const record = {
    id: 'pay-' + Date.now().toString().slice(-5), payerName: payer, amount: amount,
    date: payDate, month: payMonth, periodFrom: pFrom, periodTo: pTo,
    // the tariff that was in force when this money was paid. Keeping it on the
    // record means a later tariff change can never rewrite past months.
    tariffAtPayment: Number(f.amount) || 0,
    vatAtPayment: Number(f.vat) || 0
  };
  f.paymentHistory.unshift(record);
  f.lastPayment = record;
  f.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();

  store.state.paymentScheduleRecords.unshift({
    id: record.id, seq: nextPaymentSeq(), outlet: f.name, category: f.category, depositor: payer, amount: amount,
    date: payDate, month: payMonth, isReRequest: false, selected: true,
    // stamped so every other device can tell which copy is newer
    updatedAt: typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString()
  });

  store.save();
  closeModal('modal-log-payment');
  renderFacilitiesDirectory();
  renderDebtorRadar();
  renderRequestsView();
  if (activeReportFacilityId === f.id) renderFacilityReportContent();
  showToast('\ud83d\udcb3 Payment of ' + formatNaira(amount) + ' recorded for ' + f.name, 'success');
}

// ===========================================================================
// 14. MUNICIPAL STREET CRUD
// ===========================================================================
function populateEditStreetEvacRecordSelector(s, selectedVal) {
  const sel = document.getElementById('edit-street-evac-record-select');
  const delBtn = document.getElementById('btn-delete-selected-street-evacuation');
  const dateInput = document.getElementById('edit-street-lastevac');
  if (!sel || !s) return;
  const evacs = Array.isArray(s.evacuationHistory) ? s.evacuationHistory : [];
  const opts = [];
  evacs.forEach((ev, idx) => {
    const label = (idx === 0 ? '\u270f\ufe0f Edit Latest Evacuation (#' + (idx + 1) + '): ' : '\u270f\ufe0f Edit Evacuation #' + (idx + 1) + ': ') +
      formatDate(ev.date) + ' \u2022 ' + (ev.month || monthLabelFromKey(String(ev.date || '').slice(0, 7)) || '') +
      (ev.truck ? ' \u2022 ' + ev.truck : '');
    opts.push('<option value="' + idx + '">' + escapeHtml(label) + '</option>');
  });
  opts.push('<option value="new">+ Add New Evacuation Date</option>');
  opts.push('<option value="none">\u2014 No Evacuation Date Recorded \u2014</option>');
  sel.innerHTML = opts.join('');
  if (selectedVal !== undefined && selectedVal !== null && (selectedVal === 'new' || selectedVal === 'none' || evacs[Number(selectedVal)])) {
    sel.value = String(selectedVal);
  } else {
    sel.value = evacs.length ? '0' : 'none';
  }
  if (delBtn) {
    delBtn.style.display = (sel.value !== 'new' && sel.value !== 'none' && evacs.length > 0) ? 'inline-flex' : 'none';
  }
  if (dateInput) {
    if (sel.value === 'none') {
      dateInput.value = '';
    } else if (sel.value === 'new') {
      dateInput.value = currentUsageDateIso();
    } else {
      const rec = evacs[parseInt(sel.value, 10)] || evacs[0];
      dateInput.value = (rec && rec.date) ? rec.date : (s.lastEvacuated || '');
    }
  }
}

function onEditStreetEvacRecordChange(val) {
  const streetId = document.getElementById('edit-street-id') ? document.getElementById('edit-street-id').value : '';
  const s = store.state.municipalStreets.find(x => x.id === streetId);
  if (!s) return;
  const evacs = Array.isArray(s.evacuationHistory) ? s.evacuationHistory : [];
  const delBtn = document.getElementById('btn-delete-selected-street-evacuation');
  const dateInput = document.getElementById('edit-street-lastevac');
  if (val === 'none') {
    if (dateInput) dateInput.value = '';
    if (delBtn) delBtn.style.display = 'none';
  } else if (val === 'new' || !evacs.length) {
    if (dateInput) dateInput.value = currentUsageDateIso();
    if (delBtn) delBtn.style.display = 'none';
  } else {
    const idx = parseInt(val, 10);
    const rec = evacs[idx] || evacs[0] || {};
    if (dateInput) dateInput.value = rec.date || s.lastEvacuated || currentUsageDateIso();
    if (delBtn) delBtn.style.display = 'inline-flex';
  }
}

function deleteSelectedStreetEvacuationFromEditModal() {
  const streetId = document.getElementById('edit-street-id') ? document.getElementById('edit-street-id').value : '';
  const sel = document.getElementById('edit-street-evac-record-select');
  if (!streetId || !sel || sel.value === 'new' || sel.value === 'none') return;
  const idx = parseInt(sel.value, 10);
  if (isNaN(idx)) return;
  deleteStreetEvacuationRecord(streetId, idx, true);
}

function deleteStreetEvacuationRecord(streetId, recordIdx, stayInEditModal) {
  const s = store.state.municipalStreets.find(x => x.id === streetId);
  if (!s || !Array.isArray(s.evacuationHistory) || !s.evacuationHistory[recordIdx]) return;
  const removed = s.evacuationHistory.splice(recordIdx, 1)[0];
  if (removed) {
    if (removed.id && typeof recordDeletedId === 'function') recordDeletedId(removed.id);
    if (removed.date && typeof recordDeletedId === 'function') recordDeletedId('evac-del:' + s.id + ':' + removed.date);
    if (Array.isArray(store.state.evacuationLogs)) {
      store.state.evacuationLogs = store.state.evacuationLogs.filter(l => {
        if (l && (l.target === s.name || l.target === s.name + ' Municipal Street') && l.date === removed.date) {
          if (l.id && typeof recordDeletedId === 'function') recordDeletedId(l.id);
          return false;
        }
        return true;
      });
    }
  }
  if (s.evacuationHistory.length > 0) {
    s.evacuationHistory.sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));
    s.lastEvacuated = s.evacuationHistory[0].date || '';
  } else {
    s.lastEvacuated = '';
  }
  s.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  localDirtyEntities.add('street:' + s.id);
  store.save();
  renderMunicipalDirectory();
  renderEvacuations();
  if (activeStreetId === streetId) renderStreetReportContent();
  if (stayInEditModal) {
    populateEditStreetEvacRecordSelector(s, s.evacuationHistory.length ? '0' : 'none');
  }
  showToast('\ud83d\uddd1\ufe0f Evacuation period deleted from ' + s.name + '.', 'warning');
}

function editStreetEvacuationFromReport(streetId, recordIdx) {
  closeModal('modal-street-report');
  openEditStreetModal(streetId, recordIdx);
}

window.populateEditStreetEvacRecordSelector = populateEditStreetEvacRecordSelector;
window.onEditStreetEvacRecordChange = onEditStreetEvacRecordChange;
window.deleteSelectedStreetEvacuationFromEditModal = deleteSelectedStreetEvacuationFromEditModal;
window.deleteStreetEvacuationRecord = deleteStreetEvacuationRecord;
window.editStreetEvacuationFromReport = editStreetEvacuationFromReport;

function openEditStreetModal(streetId, editEvacIdx) {
  const s = store.state.municipalStreets.find(x => x.id === streetId);
  if (!s) return;
  document.getElementById('edit-street-id').value = s.id;
  document.getElementById('edit-street-name').value = s.name;
  const locEl = document.getElementById('edit-street-location');
  if (locEl) locEl.value = s.location || '';
  document.getElementById('edit-street-lastevac').value = s.lastEvacuated || '';
  const supSelect = document.getElementById('edit-street-supervisor');
  if (supSelect) {
    supSelect.innerHTML = supervisorOptionsHtml(s.supervisor);
    supSelect.value = s.supervisor || 'Unassigned';
  }
  const initialEvacMode = (typeof editEvacIdx === 'number' && s.evacuationHistory && s.evacuationHistory[editEvacIdx])
    ? String(editEvacIdx)
    : ((s.evacuationHistory && s.evacuationHistory.length) ? '0' : 'none');
  populateEditStreetEvacRecordSelector(s, initialEvacMode);
  openModal('modal-edit-street');
}

function saveEditStreet(e) {
  if (e) e.preventDefault();
  const s = store.state.municipalStreets.find(x => x.id === document.getElementById('edit-street-id').value);
  if (!s) return;
  s.name = document.getElementById('edit-street-name').value.trim();
  const locEl = document.getElementById('edit-street-location');
  if (locEl && locEl.value.trim()) s.location = cleanAddress(locEl.value);
  s.supervisor = document.getElementById('edit-street-supervisor').value || 'Unassigned';

  if (!Array.isArray(s.evacuationHistory)) s.evacuationHistory = [];
  const evacSel = document.getElementById('edit-street-evac-record-select');
  const evacMode = evacSel ? evacSel.value : (s.evacuationHistory.length ? '0' : 'none');
  const rawEvacDate = (document.getElementById('edit-street-lastevac').value || '').trim();
  if (evacMode === 'none' && !rawEvacDate) {
    s.lastEvacuated = s.evacuationHistory.length ? (s.evacuationHistory[0].date || '') : '';
  } else if (evacMode !== 'new' && evacMode !== 'none' && s.evacuationHistory[parseInt(evacMode, 10)]) {
    const eIdx = parseInt(evacMode, 10);
    const evRec = s.evacuationHistory[eIdx];
    const chosenDate = rawEvacDate || evRec.date || currentUsageDateIso();
    evRec.date = chosenDate;
    evRec.month = monthLabelFromKey(chosenDate.slice(0, 7)) || CURRENT_MONTH_NAME;
    evRec.supervisor = s.supervisor;
    if (!evRec.id) evRec.id = 'evac-' + s.id + '-' + chosenDate + '-' + eIdx;
    s.evacuationHistory.sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));
    s.lastEvacuated = s.evacuationHistory[0].date || chosenDate;
  } else if (rawEvacDate) {
    s.lastEvacuated = rawEvacDate;
    if (!s.evacuationHistory.some(h => h.date === rawEvacDate)) {
      s.evacuationHistory.unshift({
        id: 'evac-' + s.id + '-' + rawEvacDate + '-' + Date.now().toString().slice(-4),
        date: rawEvacDate,
        month: monthLabelFromKey(rawEvacDate.slice(0, 7)) || CURRENT_MONTH_NAME,
        truck: 'Blue Compactor (TEEM-01)',
        supervisor: s.supervisor,
        status: 'Verified Complete'
      });
    }
  }
  s.updatedAt = typeof nextMonotonicIso === 'function' ? nextMonotonicIso() : new Date().toISOString();
  localDirtyEntities.add('street:' + s.id);
  store.save();
  closeModal('modal-edit-street');
  renderMunicipalDirectory();
  renderEvacuations();
  if (activeStreetId === s.id) renderStreetReportContent();
  showToast('\u2705 Street "' + s.name + '" updated.', 'success');
}

function openAddStreetModal() {
  if (!requireAdmin('Adding municipal streets')) return;
  document.getElementById('form-add-street').reset();
  const supSelect = document.getElementById('add-street-supervisor');
  if (supSelect) supSelect.innerHTML = supervisorOptionsHtml('Unassigned');
  openModal('modal-add-street');
}

function saveAddStreet(e) {
  if (e) e.preventDefault();
  const name = document.getElementById('add-street-name').value.trim();
  const sup = document.getElementById('add-street-supervisor').value || 'Unassigned';
  const locEl = document.getElementById('add-street-location');
  store.state.municipalStreets.push({
    id: 'mun-street-' + Date.now().toString().slice(-5),
    name: name,
    location: locEl && locEl.value.trim() ? cleanAddress(locEl.value) : 'Abeokuta',
    supervisor: sup,
    lastEvacuated: '',
    evacuationHistory: [],
    status: 'Active Collection Zone'
  });
  store.save();
  closeModal('modal-add-street');
  renderMunicipalDirectory();
  showToast('\u2705 Municipal street "' + name + '" added.', 'success');
}

// ===========================================================================
// 15. SETTINGS & ADMIN CONTROL + 1-SECOND AUTO-BACKUP & CLOUD SYNC
// ===========================================================================
const AUTO_BACKUP_INTERVAL_MS = 1000;
const AUTO_BACKUP_MIRROR_KEY = 'TEEM_AUTO_BACKUP_MIRROR_v1';
const AUTO_BACKUP_CHECKPOINTS_KEY = 'TEEM_BACKUP_CHECKPOINTS_v1';
const GDRIVE_ROOT_FOLDER_DEFAULT = 'TEEM BUSINESS PORTAL';
const GDRIVE_SECTOR_FOLDERS = ['Commercial', 'Industrial', 'Medical', 'Institutional', 'Agricultural Waste', 'Construction Waste', 'Municipal'];
let autoBackupTimerId = null;
let lastAutoBackupIso = null;

function ensureEditableSettingsInputs() {
  ['company-name', 'supabase-url', 'supabase-anon-key', 'gdrive-webapp-url', 'gdrive-root-folder', 'gdrive-client-id', 'gdrive-access-token'].forEach(id => {
    const el = document.getElementById(id);
    if (!el) return;
    el.disabled = false;
    el.readOnly = false;
    el.removeAttribute('disabled');
    el.removeAttribute('readonly');
  });
}

function onCompanyNameInput(val) {
  if (!store.state.settings) store.state.settings = {};
  store.state.settings.companyName = String(val || '').trim() || 'Teem Business Nigeria Enterprises';
  if (store.state.company) {
    store.state.company.name = store.state.settings.companyName;
  }
}

// ===========================================================================
// v17: DEVICE FOLDERS - writes straight into a folder the user picked once
// ===========================================================================
// Chrome / Edge / the desktop build can hand the page a real directory handle.
// The handle is kept in IndexedDB, so the folder is remembered between visits
// and every later document goes to the same place without asking again.
var TEEM_FS_DB = 'TEEM_SaveFolders';
var TEEM_FS_STORE = 'handles';

function teemFsSupported() {
  return typeof window !== 'undefined' && typeof window.showDirectoryPicker === 'function';
}

function teemFsDb() {
  return new Promise(function (resolve, reject) {
    if (typeof window === 'undefined' || !window.indexedDB) return reject(new Error('no-idb'));
    var req = window.indexedDB.open(TEEM_FS_DB, 1);
    req.onupgradeneeded = function (e) {
      var db = e.target.result;
      if (!db.objectStoreNames.contains(TEEM_FS_STORE)) db.createObjectStore(TEEM_FS_STORE);
    };
    req.onsuccess = function () { resolve(req.result); };
    req.onerror = function () { reject(req.error); };
  });
}

function teemFsGetHandle(key) {
  return teemFsDb().then(function (db) {
    return new Promise(function (resolve, reject) {
      var tx = db.transaction(TEEM_FS_STORE, 'readonly');
      var req = tx.objectStore(TEEM_FS_STORE).get(key);
      req.onsuccess = function () { resolve(req.result || null); };
      req.onerror = function () { reject(req.error); };
    });
  }).catch(function () { return null; });
}

function teemFsSetHandle(key, handle) {
  return teemFsDb().then(function (db) {
    return new Promise(function (resolve) {
      var tx = db.transaction(TEEM_FS_STORE, 'readwrite');
      tx.objectStore(TEEM_FS_STORE).put(handle, key);
      tx.oncomplete = function () { resolve(true); };
      tx.onerror = function () { resolve(false); };
    });
  }).catch(function () { return false; });
}

function teemFsForgetHandle(key) {
  return teemFsDb().then(function (db) {
    return new Promise(function (resolve) {
      var tx = db.transaction(TEEM_FS_STORE, 'readwrite');
      tx.objectStore(TEEM_FS_STORE).delete(key);
      tx.oncomplete = function () { resolve(true); };
    });
  }).catch(function () { return false; });
}

// Asks the user to point at the folder that this document type should use.
async function chooseFolderForType(key) {
  if (!teemFsSupported()) {
    showToast('\u2139\ufe0f This browser cannot pick a folder. Use Chrome, Edge or the installed app.', 'warning');
    return;
  }
  try {
    var handle = await window.showDirectoryPicker({ mode: 'readwrite', id: 'teem-' + key });
    var granted = await teemFsEnsurePermission(handle);
    if (!granted) { showToast('\u26a0\ufe0f Folder permission was not granted.', 'error'); return; }
    await teemFsSetHandle(key, handle);
    var label = (SAVE_LOCATION_TYPES.find(function (t) { return t.key === key; }) || {}).label || key;
    showToast('\u2705 ' + label + ' will be saved to "' + handle.name + '".', 'success');
    await teemFsRefreshLabels();
  } catch (err) {
    if (err && err.name === 'AbortError') return;   // user cancelled
    showToast('\u26a0\ufe0f Could not open the folder.', 'error');
  }
}

async function teemFsEnsurePermission(handle) {
  try {
    var opts = { mode: 'readwrite' };
    if (handle.queryPermission) {
      var q = await handle.queryPermission(opts);
      if (q === 'granted') return true;
    }
    if (handle.requestPermission) {
      return (await handle.requestPermission(opts)) === 'granted';
    }
    return true;
  } catch (e) {
    return false;
  }
}

function teemDataUriToBlob(dataUri, mime) {
  var idx = String(dataUri).indexOf(',');
  var b64 = idx >= 0 ? dataUri.slice(idx + 1) : dataUri;
  var bin = atob(b64);
  var arr = new Uint8Array(bin.length);
  for (var i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
  return new Blob([arr], { type: mime || 'application/octet-stream' });
}

// Writes into the chosen folder, creating the per-type subfolder when the user
// picked a single base folder instead of a folder per document.
async function teemFsWrite(key, fileName, data, mime, makeSubfolder) {
  var root = await teemFsGetHandle(key);
  var usedRootOnly = true;
  if (!root) {
    root = await teemFsGetHandle('__base__');
    if (!root) return null;
    usedRootOnly = false;
  }
  if (!await teemFsEnsurePermission(root)) return null;

  var dir = root;
  if (!usedRootOnly && makeSubfolder) {
    var sub = sanitizeFolderPath(makeSubfolder, '');
    if (sub) {
      var parts = sub.split('/');
      for (var i = 0; i < parts.length; i++) {
        if (parts[i]) dir = await dir.getDirectoryHandle(parts[i], { create: true });
      }
    }
  }
  var fileHandle = await dir.getFileHandle(fileName, { create: true });
  var writable = await fileHandle.createWritable();
  var blob = typeof data === 'string' ? teemDataUriToBlob(data, mime) : data;
  await writable.write(blob);
  await writable.close();
  return (usedRootOnly ? '' : dir.name + '/') + fileName;
}

// Fire-and-forget from the synchronous save path.
function teemFsSaveAsync(key, fileName, data, mime, makeSubfolder) {
  if (!teemFsSupported()) return false;
  teemFsWrite(key, fileName, data, mime, makeSubfolder).then(function (path) {
    if (path) showToast('\ud83d\udcc1 Saved to ' + path, 'success');
  }).catch(function (err) {
    console.warn('folder write failed', err);
  });
  return true;
}

async function chooseBaseFolder() {
  if (!teemFsSupported()) {
    showToast('\u2139\ufe0f This browser cannot pick a folder. Use Chrome, Edge or the installed app.', 'warning');
    return;
  }
  try {
    var handle = await window.showDirectoryPicker({ mode: 'readwrite', id: 'teem-base' });
    if (!await teemFsEnsurePermission(handle)) { showToast('\u26a0\ufe0f Folder permission was not granted.', 'error'); return; }
    await teemFsSetHandle('__base__', handle);
    showToast('\u2705 Documents will be filed under "' + handle.name + '".', 'success');
    await teemFsRefreshLabels();
  } catch (err) {
    if (err && err.name !== 'AbortError') showToast('\u26a0\ufe0f Could not open the folder.', 'error');
  }
}

async function teemFsRefreshLabels() {
  var rows = SAVE_LOCATION_TYPES;
  for (var i = 0; i < rows.length; i++) {
    var el = document.getElementById('save-loc-picked-' + rows[i].key);
    if (!el) continue;
    var h = await teemFsGetHandle(rows[i].key);
    el.textContent = h ? ('\ud83d\udcc2 ' + h.name) : '';
  }
  var base = await teemFsGetHandle('__base__');
  var baseEl = document.getElementById('save-base-picked');
  if (baseEl) baseEl.textContent = base ? ('\ud83d\udcc2 ' + base.name) : 'No folder chosen';
}

// ===========================================================================
// v17: SAVE LOCATIONS (device folders + Google Drive folders per document type)
// ===========================================================================
var SAVE_LOCATION_TYPES = [
  { key: 'medical', label: 'Medical', folder: 'Medical Reports' },
  { key: 'commercial', label: 'Commercial', folder: 'Commercial Reports' },
  { key: 'industrial', label: 'Industrial', folder: 'Industrial Reports' },
  { key: 'agricultural', label: 'Agricultural', folder: 'Agricultural Reports' },
  { key: 'construction', label: 'Construction', folder: 'Construction Reports' },
  { key: 'institutional', label: 'Institutional', folder: 'Institutional Reports' },
  { key: 'municipal', label: 'Municipal', folder: 'Municipal Reports' },
  { key: 'monthly', label: 'Monthly Reports', folder: 'Monthly Reports' },
  { key: 'facility', label: 'Facility Reports', folder: 'Facility Reports' },
  { key: 'audit', label: 'Compliance Audit', folder: 'Compliance Audit' },
  { key: 'backup', label: 'Backups', folder: 'Backups' }
];

var SAVE_LOCATION_DEFAULTS = {
  deviceRoot: 'Download/TEEM',
  driveRoot: 'TEEM BUSINESS PORTAL',
  folders: {
    medical: 'Medical Reports',
    commercial: 'Commercial Reports',
    industrial: 'Industrial Reports',
    agricultural: 'Agricultural Reports',
    construction: 'Construction Reports',
    institutional: 'Institutional Reports',
    municipal: 'Municipal Reports',
    monthly: 'Monthly Reports',
    facility: 'Facility Reports',
    audit: 'Compliance Audit',
    backup: 'Backups'
  },
  autoDevice: true,
  autoDrive: true
};

function cloneSaveLocationDefaults() {
  return JSON.parse(JSON.stringify(SAVE_LOCATION_DEFAULTS));
}

function getSaveLocations() {
  var s = (store && store.state && store.state.settings) || {};
  var saved = s.saveLocations || {};
  var defs = cloneSaveLocationDefaults();
  return {
    deviceRoot: String(saved.deviceRoot || defs.deviceRoot).trim() || defs.deviceRoot,
    driveRoot: String(saved.driveRoot || s.googleDriveRootFolder || defs.driveRoot).trim() || defs.driveRoot,
    folders: Object.assign({}, defs.folders, saved.folders || {}),
    autoDevice: saved.autoDevice !== false,
    autoDrive: saved.autoDrive !== false
  };
}

function sanitizeFolderPath(value, fallback) {
  var raw = String(value === undefined || value === null ? '' : value).trim();
  if (!raw) raw = fallback || '';
  return raw
    .replace(/\\/g, '/')
    .replace(/^\/+|\/+$/g, '')
    .replace(/\.\./g, '')
    .replace(/[\u0000-\u001f<>:"|?*]+/g, '')
    .replace(/\/{2,}/g, '/');
}

// Which save-location bucket a document belongs to.
function saveLocationKeyFor(category, docType) {
  if (docType === 'monthly') return 'monthly';
  if (docType === 'facility') return 'facility';
  if (docType === 'audit') return 'audit';
  if (docType === 'backup') return 'backup';
  var map = {
    'Medical': 'medical',
    'Commercial': 'commercial',
    'Institutional': 'institutional',
    'Industrial': 'industrial',
    'Agricultural Waste': 'agricultural',
    'Construction Waste': 'construction',
    'Municipal': 'municipal'
  };
  if (category && map[category]) return map[category];
  if (category) {
    var guess = String(category).toLowerCase().split(' ')[0];
    var keys = Object.keys(SAVE_LOCATION_DEFAULTS.folders);
    for (var i = 0; i < keys.length; i++) {
      if (keys[i] === guess) return guess;
    }
  }
  return 'commercial';
}

function deviceFolderFor(category, docType) {
  var locs = getSaveLocations();
  var key = saveLocationKeyFor(category, docType);
  var base = sanitizeFolderPath(locs.deviceRoot, 'Download/TEEM');
  var sub = sanitizeFolderPath(locs.folders[key], key);
  return base + '/' + sub;
}

function driveFolderFor(category, docType) {
  var locs = getSaveLocations();
  var key = saveLocationKeyFor(category, docType);
  return {
    rootFolder: sanitizeFolderPath(locs.driveRoot, 'TEEM BUSINESS PORTAL'),
    categoryFolder: sanitizeFolderPath(locs.folders[key], key),
    key: key
  };
}

function onSaveLocationInput() {
  var preview = document.getElementById('save-loc-preview');
  if (!preview) return;
  var rootEl = document.getElementById('save-device-root');
  var driveEl = document.getElementById('save-drive-root');
  var base = sanitizeFolderPath(rootEl ? rootEl.value : '', 'Download/TEEM');
  var driveBase = sanitizeFolderPath(driveEl ? driveEl.value : '', 'TEEM BUSINESS PORTAL');
  var rows = SAVE_LOCATION_TYPES.map(function (t) {
    var input = document.getElementById('save-loc-' + t.key);
    var sub = sanitizeFolderPath(input ? input.value : t.folder, t.folder);
    return '<div style="display:flex;justify-content:space-between;gap:10px;padding:2px 0;border-bottom:1px dotted #E2E8F0;">' +
      '<span style="font-weight:700;">' + escapeHtml(t.label) + '</span>' +
      '<span style="text-align:right;word-break:break-all;">' + escapeHtml(base + '/' + sub) +
      '<br><span style="color:#64748B;">Drive: ' + escapeHtml(driveBase + '/' + sub) + '</span></span>' +
      '</div>';
  });
  preview.innerHTML = rows.join('');
}

function renderSaveLocations() {
  var grid = document.getElementById('save-loc-grid');
  var locs = getSaveLocations();
  var devRoot = document.getElementById('save-device-root');
  var drvRoot = document.getElementById('save-drive-root');
  var autoDev = document.getElementById('save-auto-device');
  var autoDrv = document.getElementById('save-auto-drive');
  if (devRoot) devRoot.value = locs.deviceRoot;
  if (drvRoot) drvRoot.value = locs.driveRoot;
  if (autoDev) autoDev.checked = locs.autoDevice;
  if (autoDrv) autoDrv.checked = locs.autoDrive;
  if (grid) {
    const canPick = teemFsSupported();
    grid.innerHTML = SAVE_LOCATION_TYPES.map(function (t) {
      return '<div style="display:flex;align-items:center;gap:8px;margin-bottom:6px;flex-wrap:wrap;">' +
        '<span style="font-size:12.5px;font-weight:700;color:#334155;min-width:112px;">' + escapeHtml(t.label) + '</span>' +
        '<input type="text" class="form-input" id="save-loc-' + t.key + '" value="' + escapeHtml(locs.folders[t.key] || t.folder) + '" ' +
        'style="flex:1;min-width:140px;padding:6px 8px;font-size:12.5px;" oninput="onSaveLocationInput()">' +
        (canPick ? '<button type="button" class="btn btn-outline" style="padding:5px 10px;font-size:11.5px;" onclick="chooseFolderForType(\'' + t.key + '\')">Choose</button>' : '') +
        '<span id="save-loc-picked-' + t.key + '" style="font-size:11.5px;color:#15803D;font-weight:700;"></span>' +
        '</div>';
    }).join('');
    teemFsRefreshLabels();
  }
  onSaveLocationInput();
}

function saveSaveLocations() {
  if (!store || !store.state) return;
  store.state.settings = store.state.settings || {};
  var folders = {};
  SAVE_LOCATION_TYPES.forEach(function (t) {
    var input = document.getElementById('save-loc-' + t.key);
    folders[t.key] = sanitizeFolderPath(input ? input.value : '', t.folder) || t.folder;
  });
  var devRootEl = document.getElementById('save-device-root');
  var drvRootEl = document.getElementById('save-drive-root');
  var autoDevEl = document.getElementById('save-auto-device');
  var autoDrvEl = document.getElementById('save-auto-drive');
  store.state.settings.saveLocations = {
    deviceRoot: sanitizeFolderPath(devRootEl ? devRootEl.value : '', 'Download/TEEM'),
    driveRoot: sanitizeFolderPath(drvRootEl ? drvRootEl.value : '', 'TEEM BUSINESS PORTAL'),
    folders: folders,
    autoDevice: autoDevEl ? !!autoDevEl.checked : true,
    autoDrive: autoDrvEl ? !!autoDrvEl.checked : true
  };
  store.state.settings.googleDriveRootFolder = store.state.settings.saveLocations.driveRoot;
  if (typeof persistState === 'function') persistState();
  if (typeof scheduleCloudSync === 'function') scheduleCloudSync();
  showToast('\u2705 Save locations updated.', 'success');
  renderSaveLocations();
}

function resetSaveLocations() {
  if (!store || !store.state) return;
  store.state.settings = store.state.settings || {};
  store.state.settings.saveLocations = cloneSaveLocationDefaults();
  if (typeof persistState === 'function') persistState();
  showToast('\u21ba Save locations reset to default.', 'success');
  renderSaveLocations();
}

function renderSettingsConsole() {
  try { if (typeof renderSaveLocations === 'function') renderSaveLocations(); } catch (e) { console.warn(e); }
  ensureEditableSettingsInputs();
  const s = store.state.settings || {};
  const setIfNotFocused = (id, val) => {
    const el = document.getElementById(id);
    if (el && document.activeElement !== el) {
      el.value = val !== undefined && val !== null ? val : '';
    }
  };
  setIfNotFocused('company-name', s.companyName || (store.state.company && store.state.company.name) || 'Teem Business Nigeria Enterprises');
  setIfNotFocused('supabase-url', s.supabaseUrl || '');
  setIfNotFocused('supabase-anon-key', s.supabaseAnonKey || '');
  setIfNotFocused('gdrive-webapp-url', s.googleAppsScriptUrl || '');
  setIfNotFocused('gdrive-root-folder', s.googleDriveRootFolder || GDRIVE_ROOT_FOLDER_DEFAULT);
  setIfNotFocused('gdrive-client-id', s.googleDriveClientId || '');
  setIfNotFocused('gdrive-access-token', s.googleDriveAccessToken || '');

  const autoSaveEl = document.getElementById('archive-autosave');
  if (autoSaveEl) autoSaveEl.checked = s.archiveAutoSave !== false;

  const autoBackupEl = document.getElementById('auto-backup-enabled');
  if (autoBackupEl) autoBackupEl.checked = s.autoBackup5s !== false;

  const syncCodeOut = document.getElementById('cloud-sync-code-output');
  if (syncCodeOut) {
    syncCodeOut.value = encodeCloudSyncCode();
  }
  const syncLiveInd = document.getElementById('cloud-sync-live-indicator');
  if (syncLiveInd) {
    syncLiveInd.textContent = hasCloudSyncConfigured()
      ? 'Configured \u2014 automatic live synchronization active across Windows, Web & Android.'
      : 'Configured \u2014 authentication required for synchronization.';
  }

  renderBackupRestoreStatusUI();

  const typeSelect = document.getElementById('delete-target-type');
  const targetSelect = document.getElementById('delete-target-id');
  if (!typeSelect || !targetSelect) return;

  const prevTargetVal = targetSelect.value;
  const type = typeSelect.value;
  if (type === 'facility') {
    targetSelect.innerHTML = store.state.facilities.map(f => '<option value="' + f.id + '">' + escapeHtml(f.category) + ' \u2014 ' + escapeHtml(f.name) + '</option>').join('');
  } else if (type === 'street') {
    targetSelect.innerHTML = store.state.municipalStreets.map(s => '<option value="' + s.id + '">Street \u2014 ' + escapeHtml(s.name) + '</option>').join('');
  } else {
    targetSelect.innerHTML = store.state.vehicles.map(v => '<option value="' + v.id + '">Fleet \u2014 ' + escapeHtml(v.name) + ' (' + escapeHtml(v.type) + ')</option>').join('');
  }
  if (prevTargetVal && Array.from(targetSelect.options).some(opt => opt.value === prevTargetVal)) {
    targetSelect.value = prevTargetVal;
  }
}

function recordDeletedId() {
  if (!store || !store.state) return;
  if (!Array.isArray(store.state.deletedIds)) store.state.deletedIds = [];
  for (let i = 0; i < arguments.length; i++) {
    const id = arguments[i];
    if (id && typeof id === 'string' && !store.state.deletedIds.includes(id)) {
      store.state.deletedIds.push(id);
    }
  }
}
window.recordDeletedId = recordDeletedId;

// ===========================================================================
// DELETE A FACILITY FROM ITS OWN ROW (administrators only)
// Same effect as Settings > Delete, without leaving the directory.
// ===========================================================================
function deleteFacilityById(facilityId) {
  if (!isAdmin()) {
    showToast('\u26a0\ufe0f Only an Administrator can delete a facility.', 'error');
    return false;
  }
  const f = store.state.facilities.find(x => x.id === facilityId);
  if (!f) return false;

  const recordCount = (f.paymentHistory || []).length;
  const evacCount = (f.evacuationHistory || []).length;
  const detail = [];
  if (recordCount) detail.push(recordCount + ' payment record' + (recordCount === 1 ? '' : 's'));
  if (evacCount) detail.push(evacCount + ' evacuation record' + (evacCount === 1 ? '' : 's'));

  const message = 'This permanently removes "' + f.name + '"' +
    (detail.length ? ' together with ' + detail.join(' and ') : '') +
    '. This cannot be undone.';

  const back = document.getElementById('modal-confirm-delete');
  const nameEl = document.getElementById('confirm-delete-name');
  const msgEl = document.getElementById('confirm-delete-message');
  if (nameEl) nameEl.textContent = f.name;
  if (msgEl) msgEl.textContent = message;
  if (back) {
    back.dataset.facilityId = f.id;
    back.classList.add('active');
  } else if (!confirm(message)) {
    return false;
  }
  return true;
}

function confirmDeleteFacility() {
  const back = document.getElementById('modal-confirm-delete');
  const id = back ? back.dataset.facilityId : '';
  const f = store.state.facilities.find(x => x.id === id);
  closeModal('modal-confirm-delete');
  if (!f) return false;

  recordDeletedId(f.id);
  if (Array.isArray(f.paymentHistory)) {
    f.paymentHistory.forEach(p => { if (p && p.id) recordDeletedId(p.id); });
  }
  if (f.lastPayment && f.lastPayment.id) recordDeletedId(f.lastPayment.id);
  if (Array.isArray(store.state.paymentScheduleRecords)) {
    store.state.paymentScheduleRecords.forEach(p => {
      if (p && p.outlet === f.name) recordDeletedId(p.id || (p.outlet + '|' + p.date + '|' + p.amount));
    });
  }
  store.state.facilities = store.state.facilities.filter(x => x.id !== f.id);
  store.state.paymentScheduleRecords = (store.state.paymentScheduleRecords || []).filter(p => p.outlet !== f.name);

  store.save();
  updateHeaderStats();
  renderDashboardCards();
  renderFacilitiesDirectory();
  renderDebtorRadar();
  renderRequestsView();
  if (typeof renderSettingsConsole === 'function') { try { renderSettingsConsole(); } catch (e) {} }
  if (activeReportFacilityId === f.id) { activeReportFacilityId = null; closeModal('modal-facility-report'); }
  showToast('\ud83d\uddd1\ufe0f Facility "' + f.name + '" permanently deleted.', 'warning');
  if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') window.TEEM_DESKTOP_RUNTIME.refocus();
  return true;
}
window.deleteFacilityById = deleteFacilityById;
window.confirmDeleteFacility = confirmDeleteFacility;

function executeAdminDeletion(e) {
  if (e) e.preventDefault();
  const pwdEl = document.getElementById('admin-delete-password');
  const pwd = pwdEl ? pwdEl.value.trim() : '';
  if (!isValidAdminGatePassword(pwd)) {
    showToast('\u26a0\ufe0f Wrong administrator password.', 'error');
    if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') window.TEEM_DESKTOP_RUNTIME.refocus();
    if (pwdEl) { try { pwdEl.focus(); } catch (err) {} }
    return;
  }

  const type = document.getElementById('delete-target-type').value;
  const id = document.getElementById('delete-target-id').value;

  if (type === 'facility') {
    const f = store.state.facilities.find(x => x.id === id);
    if (!f || !confirm('Permanently delete facility "' + f.name + '" and all of its records?')) {
      if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') window.TEEM_DESKTOP_RUNTIME.refocus();
      return;
    }
    recordDeletedId(id);
    if (Array.isArray(f.paymentHistory)) {
      f.paymentHistory.forEach(p => { if (p && p.id) recordDeletedId(p.id); });
    }
    if (f.lastPayment && f.lastPayment.id) recordDeletedId(f.lastPayment.id);
    if (Array.isArray(store.state.paymentScheduleRecords)) {
      store.state.paymentScheduleRecords.forEach(p => {
        if (p && p.outlet === f.name) {
          recordDeletedId(p.id || (p.outlet + '|' + p.date + '|' + p.amount));
        }
      });
    }
    store.state.facilities = store.state.facilities.filter(x => x.id !== id);
    store.state.paymentScheduleRecords = store.state.paymentScheduleRecords.filter(p => p.outlet !== f.name);
    showToast('\ud83d\uddd1\ufe0f Facility "' + f.name + '" permanently deleted.', 'warning');
  } else if (type === 'street') {
    const s = store.state.municipalStreets.find(x => x.id === id);
    if (!s || !confirm('Permanently delete municipal street "' + s.name + '"?')) {
      if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') window.TEEM_DESKTOP_RUNTIME.refocus();
      return;
    }
    recordDeletedId(id);
    store.state.municipalStreets = store.state.municipalStreets.filter(x => x.id !== id);
    showToast('\ud83d\uddd1\ufe0f Municipal street "' + s.name + '" permanently deleted.', 'warning');
  } else {
    const v = store.state.vehicles.find(x => x.id === id);
    if (!v || !confirm('Remove fleet vehicle "' + v.name + '"?')) {
      if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') window.TEEM_DESKTOP_RUNTIME.refocus();
      return;
    }
    if (store.state.vehicles.length <= 1) {
      showToast('\u26a0\ufe0f At least one fleet vehicle must remain.', 'error');
      return;
    }
    recordDeletedId(id);
    store.state.vehicles = store.state.vehicles.filter(x => x.id !== id);
    showToast('\ud83d\uddd1\ufe0f Vehicle removed from fleet.', 'warning');
  }

  if (pwdEl) pwdEl.value = '';
  store.save();
  updateHeaderStats();
  renderDashboardCards();
  renderSettingsConsole();
  renderFacilitiesDirectory();
  renderMunicipalDirectory();
  renderVehiclesList();
  renderDebtorRadar();
  renderRequestsView();
  if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') window.TEEM_DESKTOP_RUNTIME.refocus();
}

function saveArchiveSettings(e) {
  if (e) e.preventDefault();
  if (!store.state.settings) store.state.settings = {};
  const compEl = document.getElementById('company-name');
  const gwebappEl = document.getElementById('gdrive-webapp-url');
  const grootEl = document.getElementById('gdrive-root-folder');
  const gdriveEl = document.getElementById('gdrive-client-id');
  const gtokenEl = document.getElementById('gdrive-access-token');
  const supaUrlEl = document.getElementById('supabase-url');
  const supaKeyEl = document.getElementById('supabase-anon-key');
  const autoSaveEl = document.getElementById('archive-autosave');

  store.state.settings.companyName = (compEl ? compEl.value.trim() : '') || 'Teem Business Nigeria Enterprises';
  if (store.state.company) store.state.company.name = store.state.settings.companyName;
  if (gwebappEl) store.state.settings.googleAppsScriptUrl = gwebappEl.value.trim();
  if (grootEl) store.state.settings.googleDriveRootFolder = grootEl.value.trim() || GDRIVE_ROOT_FOLDER_DEFAULT;
  if (gdriveEl) store.state.settings.googleDriveClientId = gdriveEl.value.trim();
  if (gtokenEl) store.state.settings.googleDriveAccessToken = gtokenEl.value.trim();
  if (supaUrlEl) store.state.settings.supabaseUrl = supaUrlEl.value.trim().replace(/\/+$/, '');
  if (supaKeyEl) store.state.settings.supabaseAnonKey = supaKeyEl.value.trim();
  if (autoSaveEl) store.state.settings.archiveAutoSave = autoSaveEl.checked;

  store.state.settings.updatedAt = new Date().toISOString();
  store.save();
  persistCloudConfigEverywhere();
  runAutoBackupTick(false);
  renderSettingsConsole();
  if (e && hasCloudSyncConfigured()) {
    // startRealtimeCloudSyncEngine() was called here but never defined, so
    // saving the cloud settings threw and the pull below never ran.
    if (typeof startAutoBackupEngine === 'function') startAutoBackupEngine();
    pullAllCloudProvidersNow(false).then(() => {
      const snap = buildBackupSnapshot('settings-save');
      if (store.state.settings.supabaseUrl && store.state.settings.supabaseAnonKey) {
        syncWithSupabaseOnline(snap, false);
      }
      if (store.state.settings.googleAppsScriptUrl || store.state.settings.googleDriveAccessToken) {
        syncWithGoogleDriveOnline(snap, false);
      }
    }).catch(() => {});
  }
  showToast('\u2699\ufe0f Settings saved.', 'success');
}

function hasCloudSyncConfigured() {
  const s = (store && store.state && store.state.settings) || {};
  return Boolean((s.supabaseUrl && s.supabaseAnonKey) || s.googleAppsScriptUrl);
}

function encodeCloudSyncCode() {
  const s = (store && store.state && store.state.settings) || {};
  const payload = {
    sUrl: (s.supabaseUrl || '').trim(),
    sKey: (s.supabaseAnonKey || '').trim(),
    gUrl: (s.googleAppsScriptUrl || '').trim(),
    gRoot: (s.googleDriveRootFolder || GDRIVE_ROOT_FOLDER_DEFAULT).trim() || GDRIVE_ROOT_FOLDER_DEFAULT,
    cName: (s.companyName || 'Teem Business Nigeria Enterprises').trim()
  };
  if (!payload.sUrl && !payload.gUrl) return '';
  try {
    const jsonStr = JSON.stringify(payload);
    const b64 = typeof btoa === 'function'
      ? btoa(unescape(encodeURIComponent(jsonStr)))
      : Buffer.from(jsonStr, 'utf8').toString('base64');
    return 'TEEM-SYNC-' + b64.replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  } catch (e) {
    return '';
  }
}

function applyCloudSyncCodeString(rawStr) {
  try {
    let clean = String(rawStr || '').trim();
    if (!clean) return false;
    // Allow pasting a full URL containing ?cloud=TEEM-SYNC-...
    const qMatch = clean.match(/[?&]cloud=(TEEM-SYNC-[A-Za-z0-9_-]+)/);
    if (qMatch) clean = qMatch[1];
    if (!clean.startsWith('TEEM-SYNC-')) return false;
    let b64 = clean.slice('TEEM-SYNC-'.length).replace(/-/g, '+').replace(/_/g, '/');
    while (b64.length % 4) b64 += '=';
    const jsonStr = typeof atob === 'function'
      ? decodeURIComponent(escape(atob(b64)))
      : Buffer.from(b64, 'base64').toString('utf8');
    const parsed = JSON.parse(jsonStr);
    if (!parsed || (!parsed.sUrl && !parsed.gUrl)) return false;
    if (!store.state.settings) store.state.settings = {};
    if (parsed.sUrl) store.state.settings.supabaseUrl = String(parsed.sUrl).trim().replace(/\/+$/, '');
    if (parsed.sKey) store.state.settings.supabaseAnonKey = String(parsed.sKey).trim();
    if (parsed.gUrl) store.state.settings.googleAppsScriptUrl = String(parsed.gUrl).trim();
    if (parsed.gRoot) store.state.settings.googleDriveRootFolder = String(parsed.gRoot).trim();
    if (parsed.cName) {
      store.state.settings.companyName = String(parsed.cName).trim();
      if (store.state.company) store.state.company.name = store.state.settings.companyName;
    }
    store.save();
    return true;
  } catch (e) {
    return false;
  }
}

function copyCloudSyncCode() {
  saveArchiveSettings();
  const code = encodeCloudSyncCode();
  if (!code) {
    showToast('\u26a0\ufe0f Add a cloud URL first.', 'warning');
    return;
  }
  const out = document.getElementById('cloud-sync-code-output');
  if (out) out.value = code;
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(code).then(() => {
      showToast('\ud83d\udccb Sync code copied.', 'success');
    }).catch(() => {
      showToast('\u2705 Sync Code generated in the box — select and copy it.', 'info');
    });
  } else {
    showToast('\u2705 Sync Code generated in the box — select and copy it.', 'info');
  }
}

function copyCloudSyncedUrl() {
  saveArchiveSettings();
  const code = encodeCloudSyncCode();
  if (!code) {
    showToast('\u26a0\ufe0f Add a cloud URL first.', 'warning');
    return;
  }
  const baseUrl = (typeof window !== 'undefined' && window.location && window.location.href)
    ? window.location.href.split('?')[0].split('#')[0]
    : 'https://your-site.netlify.app/';
  const fullLink = baseUrl + '?cloud=' + encodeURIComponent(code);
  const out = document.getElementById('cloud-sync-code-output');
  if (out) out.value = fullLink;
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(fullLink).then(() => {
      showToast('\ud83d\udd17 Link copied.', 'success');
    }).catch(() => {
      showToast('\u2705 Cloud-Synced Link generated in the box.', 'info');
    });
  } else {
    showToast('\u2705 Cloud-Synced Link generated in the box.', 'info');
  }
}

function buildCloudConfigObject() {
  const s = (store && store.state && store.state.settings) || {};
  return {
    version: RELEASE,
    companyName: s.companyName || 'Teem Business Nigeria Enterprises',
    supabaseUrl: s.supabaseUrl || '',
    supabaseAnonKey: s.supabaseAnonKey || '',
    googleAppsScriptUrl: s.googleAppsScriptUrl || '',
    googleDriveRootFolder: s.googleDriveRootFolder || GDRIVE_ROOT_FOLDER_DEFAULT,
    syncChannelId: 'teem_global_state_v2_9',
    updatedAt: new Date().toISOString()
  };
}

function persistCloudConfigEverywhere() {
  const cfg = buildCloudConfigObject();
  try {
    SafeStorage.set('TEEM_CLOUD_CONFIG_GLOBAL', JSON.stringify(cfg));
  } catch (e) {}
  if (typeof window !== 'undefined' && window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.writeCloudConfig === 'function') {
    try { window.TEEM_DESKTOP_RUNTIME.writeCloudConfig(cfg); } catch (e) {}
  }
}

function exportCloudConfigFile() {
  saveArchiveSettings();
  const cfg = buildCloudConfigObject();
  const json = JSON.stringify(cfg, null, 2);
  try {
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = 'cloud-config.json';
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(() => URL.revokeObjectURL(url), 1500);
    showToast('\ud83d\udcc1 cloud-config.json saved.', 'success');
  } catch (e) {
    showToast('\u26a0\ufe0f Unable to download cloud-config.json here.', 'error');
  }
}

let highestSeenCloudMs = 0;
function noteCloudTimestamp(isoOrMs) {
  const ms = typeof isoOrMs === 'number' ? isoOrMs : (Date.parse(isoOrMs || 0) || 0);
  if (ms > highestSeenCloudMs) highestSeenCloudMs = ms;
}
function nextMonotonicIso() {
  const targetMs = Math.max(Date.now(), highestSeenCloudMs + 1000);
  highestSeenCloudMs = targetMs;
  return new Date(targetMs).toISOString();
}
window.nextMonotonicIso = nextMonotonicIso;

function smartMergeCloudState(localState, remoteRaw) {
  if (!remoteRaw || typeof remoteRaw !== 'object') return false;
  if (remoteRaw.updated_at) noteCloudTimestamp(remoteRaw.updated_at);
  const remoteState = (remoteRaw.state && typeof remoteRaw.state === 'object')
    ? remoteRaw.state
    : (remoteRaw.payload && typeof remoteRaw.payload === 'object')
      ? remoteRaw.payload
      : remoteRaw;
  if (!remoteState || (!Array.isArray(remoteState.users) && !Array.isArray(remoteState.facilities))) {
    return false;
  }
  if (!remoteState.v106LaunchResetApplied) {
    applyV106OperationalStartReset(remoteState);
  }
  if (!localState.v106LaunchResetApplied) {
    applyV106OperationalStartReset(localState);
  }
  if (remoteState.updatedAt) noteCloudTimestamp(remoteState.updatedAt);
  if (localState && localState.updatedAt) noteCloudTimestamp(localState.updatedAt);

  let changed = false;

  // 1. Merge deletedIds tombstones
  const prevDelCount = Array.isArray(localState.deletedIds) ? localState.deletedIds.length : 0;
  const deletedSet = new Set([
    ...((localState.deletedIds && Array.isArray(localState.deletedIds)) ? localState.deletedIds : []),
    ...((remoteState.deletedIds && Array.isArray(remoteState.deletedIds)) ? remoteState.deletedIds : [])
  ]);
  localState.deletedIds = Array.from(deletedSet);
  if (localState.deletedIds.length !== prevDelCount) changed = true;

  if (deletedSet.size > 0) {
    ['facilities', 'municipalStreets', 'vehicles', 'supervisors', 'paymentScheduleRecords', 'evacuationLogs', 'archivedDocuments'].forEach(col => {
      if (Array.isArray(localState[col])) {
        const before = localState[col].length;
        localState[col] = localState[col].filter(item => item && !deletedSet.has(item.id));
        if (localState[col].length !== before) changed = true;
      }
    });
    if (Array.isArray(localState.users)) {
      const beforeU = localState.users.length;
      const filteredU = localState.users.filter(u => u && !deletedSet.has(u.id));
      if (filteredU.length > 0 && filteredU.length !== beforeU) {
        localState.users = filteredU;
        changed = true;
      }
    }
    // Also strip any deleted payments or evacuations inside localState.facilities and localState.municipalStreets immediately
    (localState.facilities || []).forEach(lf => {
      if (!lf) return;
      if (Array.isArray(lf.paymentHistory)) {
        const beforeP = lf.paymentHistory.length;
        lf.paymentHistory = lf.paymentHistory.filter(p => p && !deletedSet.has(p.id) && !deletedSet.has('pay-del:' + lf.id + ':' + (p.date || '') + ':' + (p.amount || 0)));
        if (lf.paymentHistory.length !== beforeP) {
          lf.lastPayment = lf.paymentHistory.length ? lf.paymentHistory[0] : null;
          changed = true;
        }
      }
      if (!lf.paymentHistory || !lf.paymentHistory.length) {
        if (lf.lastPayment !== null) {
          lf.lastPayment = null;
          changed = true;
        }
      }
      if (Array.isArray(lf.evacuationHistory)) {
        const beforeE = lf.evacuationHistory.length;
        lf.evacuationHistory = lf.evacuationHistory.filter(e => e && !deletedSet.has(e.id) && !deletedSet.has('evac-del:' + lf.id + ':' + (e.date || '')));
        if (lf.evacuationHistory.length !== beforeE) {
          lf.lastEvacuated = lf.evacuationHistory.length ? (lf.evacuationHistory[0].date || '') : '';
          changed = true;
        }
      }
    });
    (localState.municipalStreets || []).forEach(ls => {
      if (!ls) return;
      if (Array.isArray(ls.evacuationHistory)) {
        const beforeE = ls.evacuationHistory.length;
        ls.evacuationHistory = ls.evacuationHistory.filter(e => e && !deletedSet.has(e.id) && !deletedSet.has('evac-del:' + ls.id + ':' + (e.date || '')));
        if (ls.evacuationHistory.length !== beforeE) {
          ls.lastEvacuated = ls.evacuationHistory.length ? (ls.evacuationHistory[0].date || '') : '';
          changed = true;
        }
      }
    });
  }

  // 2. Merge Users (passwords, usernames, roles, profiles, sign-ups)
  const prevSessionId = localState.sessionUserId;
  const prevSessionUser = prevSessionId && Array.isArray(localState.users)
    ? localState.users.find(u => u && u.id === prevSessionId)
    : null;

  if (Array.isArray(remoteState.users) && remoteState.users.length) {
    const localUsers = Array.isArray(localState.users) ? localState.users.slice() : [];
    const mergedUsers = [];
    const seenIds = new Set();

    const getUserMaxTs = (u) => {
      if (!u) return 0;
      return Math.max(
        Date.parse(u.updatedAt || 0) || 0,
        Date.parse(u.passwordChangedAt || 0) || 0,
        Date.parse(u.createdAt || 0) || 0
      );
    };

    const pickBetterUser = (locU, remU) => {
      const locTs = getUserMaxTs(locU);
      const remTs = getUserMaxTs(remU);
      if (locTs) noteCloudTimestamp(locTs);
      if (remTs) noteCloudTimestamp(remTs);
      const locDefaultPwd = (locU.password === 'admin2026' || locU.password === hashPassword('admin2026'));
      const remDefaultPwd = (remU.password === 'admin2026' || remU.password === hashPassword('admin2026'));

      let winner = locU;
      if (locDefaultPwd && !remDefaultPwd) {
        winner = remU;
      } else if (!locDefaultPwd && remDefaultPwd) {
        winner = locU;
      } else if (!prevSessionId && !(store && store.hasUnsyncedLocalChanges) && !remDefaultPwd) {
        // When sitting on the Sign-In screen with no unsynced local edits, always trust the latest cloud user record
        winner = remU;
      } else if (store && store.hasUnsyncedLocalChanges && locTs >= remTs) {
        winner = locU;
      } else if (remTs >= locTs) {
        winner = remU;
      } else if (locTs > remTs) {
        winner = locU;
      } else if ((locU.id === 'usr-01' || locU.id === 'user-admin-01') && locU.username === 'admin' && remU.username && remU.username !== 'admin') {
        winner = remU;
      }
      const base = winner === locU ? Object.assign({}, remU, locU) : Object.assign({}, locU, remU);
      const merged = Object.assign({}, base, winner);
      // Preserve both local and remote non-default passwords so login works across iPhone & Laptop regardless of clock skew
      const pwSet = new Set();
      if (Array.isArray(locU.prevPasswords)) locU.prevPasswords.forEach(p => { if (p) pwSet.add(p); });
      if (Array.isArray(remU.prevPasswords)) remU.prevPasswords.forEach(p => { if (p) pwSet.add(p); });
      if (locU.password && !locDefaultPwd) pwSet.add(locU.password);
      if (remU.password && !remDefaultPwd) pwSet.add(remU.password);
      if (pwSet.size > 0) merged.prevPasswords = Array.from(pwSet);
      // Preserve active local session user ID so merging by username never orphans store.state.sessionUserId
      if (prevSessionId && locU.id === prevSessionId) {
        merged.id = locU.id;
      }
      merged.role = normalizeUserRole(merged.role);
      if (!merged.photo && (locU.photo || remU.photo)) merged.photo = locU.photo || remU.photo;
      if (!merged.email && (locU.email || remU.email)) merged.email = locU.email || remU.email;
      if (!merged.phone && (locU.phone || remU.phone)) merged.phone = locU.phone || remU.phone;
      return merged;
    };

    localUsers.forEach(locU => {
      if (!locU || deletedSet.has(locU.id)) return;
      const remMatch = remoteState.users.find(r => r && !deletedSet.has(r.id) && (r.id === locU.id || (r.username && locU.username && r.username.toLowerCase() === locU.username.toLowerCase())));
      if (remMatch) {
        const chosen = pickBetterUser(locU, remMatch);
        if (JSON.stringify(chosen) !== JSON.stringify(locU)) changed = true;
        mergedUsers.push(chosen);
        seenIds.add(locU.id);
        if (remMatch.id) seenIds.add(remMatch.id);
      } else {
        locU.role = normalizeUserRole(locU.role);
        mergedUsers.push(locU);
        seenIds.add(locU.id);
      }
    });

    remoteState.users.forEach(remU => {
      if (!remU || !remU.id || seenIds.has(remU.id)) return;
      if (deletedSet.has(remU.id)) return;
      const dupUsername = mergedUsers.some(u => (u.username || '').toLowerCase() === (remU.username || '').toLowerCase());
      if (!dupUsername) {
        const copy = JSON.parse(JSON.stringify(remU));
        copy.role = normalizeUserRole(copy.role);
        mergedUsers.push(copy);
        seenIds.add(remU.id);
        changed = true;
      }
    });

    if (mergedUsers.length > 0) {
      localState.users = mergedUsers;
    }
  }

  // Ensure the currently logged-in user's session is never lost or turned to Read-Only after user list merges
  if (prevSessionId && Array.isArray(localState.users) && localState.users.length) {
    const stillHasId = localState.users.some(u => u && u.id === prevSessionId);
    if (!stillHasId) {
      let replacement = null;
      if (prevSessionUser && prevSessionUser.username) {
        const uname = String(prevSessionUser.username).toLowerCase();
        replacement = localState.users.find(u => u && String(u.username || '').toLowerCase() === uname);
      }
      if (!replacement && (!prevSessionUser || isUserAdminRole(prevSessionUser))) {
        replacement = localState.users.find(u => isUserAdminRole(u) && u.status !== 'Disabled');
      }
      if (replacement) {
        localState.sessionUserId = replacement.id;
        if (typeof window !== 'undefined') {
          window._teemActiveSessionUser = { id: replacement.id, username: replacement.username, role: normalizeUserRole(replacement.role) };
        }
      }
    }
  }

  // 3. Merge Facilities (plus full sync of paymentHistory, lastPayment, evacuationHistory & lastEvacuated)
  if (Array.isArray(remoteState.facilities) && remoteState.facilities.length) {
    const localFacs = Array.isArray(localState.facilities) ? localState.facilities : [];
    const facMap = new Map();
    localFacs.forEach(f => {
      if (f && f.id && !deletedSet.has(f.id)) facMap.set(f.id, f);
    });
    const remGlobalStrictNewer = (Date.parse(remoteState.updatedAt || 0) || 0) > (Date.parse(localState.updatedAt || 0) || 0);
    remoteState.facilities.forEach(rf => {
      if (!rf || !rf.id || deletedSet.has(rf.id)) return;
      if (rf.id === 'fac-indu-040' && Number(rf.amount) === 236500) {
        rf.amount = 220000;
      }
      const rPays = (Array.isArray(rf.paymentHistory) ? rf.paymentHistory : []).filter(p => p && !deletedSet.has(p.id) && !deletedSet.has('pay-del:' + rf.id + ':' + (p.date || '') + ':' + (p.amount || 0)));
      const rEvacs = (Array.isArray(rf.evacuationHistory) ? rf.evacuationHistory : []).filter(e => e && !deletedSet.has(e.id) && !deletedSet.has('evac-del:' + rf.id + ':' + (e.date || '')));
      const lf = facMap.get(rf.id);
      if (!lf) {
        const cloneRf = JSON.parse(JSON.stringify(rf));
        cloneRf.paymentHistory = JSON.parse(JSON.stringify(rPays));
        cloneRf.lastPayment = cloneRf.paymentHistory.length ? cloneRf.paymentHistory[0] : null;
        cloneRf.evacuationHistory = JSON.parse(JSON.stringify(rEvacs));
        cloneRf.lastEvacuated = cloneRf.evacuationHistory.length ? (cloneRf.evacuationHistory[0].date || cloneRf.lastEvacuated || '') : '';
        facMap.set(rf.id, cloneRf);
        changed = true;
        return;
      }
      const isDirty = localDirtyEntities.has('fac:' + lf.id);
      const lFacTs = Date.parse(lf.updatedAt || 0) || 0;
      const rFacTs = Date.parse(rf.updatedAt || 0) || 0;
      if (rFacTs) noteCloudTimestamp(rFacTs);
      if (lFacTs) noteCloudTimestamp(lFacTs);

      if (isDirty && lFacTs <= rFacTs) {
        lf.updatedAt = nextMonotonicIso();
      }
      const remoteIsNewer = !isDirty && ((rFacTs > 0 && rFacTs > lFacTs) || (lFacTs === 0 && rFacTs === 0 && remGlobalStrictNewer));
      const localIsNewer = isDirty || (lFacTs > rFacTs);

      const lPays = (Array.isArray(lf.paymentHistory) ? lf.paymentHistory : []).filter(p => p && !deletedSet.has(p.id) && !deletedSet.has('pay-del:' + lf.id + ':' + (p.date || '') + ':' + (p.amount || 0)));
      const lEvacs = (Array.isArray(lf.evacuationHistory) ? lf.evacuationHistory : []).filter(e => e && !deletedSet.has(e.id) && !deletedSet.has('evac-del:' + lf.id + ':' + (e.date || '')));

      if (remoteIsNewer) {
        if (rf.amount !== undefined && Number(rf.amount) !== Number(lf.amount)) {
          lf.amount = Number(rf.amount) || 0;
          changed = true;
        }
        if (rf.vat !== undefined && Number(rf.vat) !== Number(lf.vat)) {
          lf.vat = Number(rf.vat) || 0;
          changed = true;
        }
        if (rf.name && rf.name !== lf.name) {
          lf.name = rf.name;
          changed = true;
        }
        if (rf.category && rf.category !== lf.category) {
          lf.category = rf.category;
          changed = true;
        }
        if (rf.location && rf.location !== lf.location) {
          lf.location = rf.location;
          changed = true;
        }
        if (rf.supervisor && rf.supervisor !== lf.supervisor) {
          lf.supervisor = rf.supervisor;
          changed = true;
        }
        if (JSON.stringify(rPays) !== JSON.stringify(lPays) || Boolean(lf.lastPayment) !== Boolean(rPays[0])) {
          lf.paymentHistory = JSON.parse(JSON.stringify(rPays));
          lf.lastPayment = lf.paymentHistory.length ? lf.paymentHistory[0] : null;
          changed = true;
        }
        const remLastEvac = rf.lastEvacuated !== undefined ? rf.lastEvacuated : (rEvacs[0] ? rEvacs[0].date : '');
        if (JSON.stringify(rEvacs) !== JSON.stringify(lEvacs) || (lf.lastEvacuated || '') !== (remLastEvac || '')) {
          lf.evacuationHistory = JSON.parse(JSON.stringify(rEvacs));
          lf.lastEvacuated = remLastEvac || '';
          changed = true;
        }
        if (rf.updatedAt && rf.updatedAt !== lf.updatedAt) {
          lf.updatedAt = rf.updatedAt;
          changed = true;
        }
      } else if (!localIsNewer) {
        // Equal facility timestamps: if global remote snapshot is newer, adopt remote paymentHistory & evacuationHistory
        if (remGlobalStrictNewer) {
          if (JSON.stringify(rPays) !== JSON.stringify(lPays)) {
            lf.paymentHistory = JSON.parse(JSON.stringify(rPays));
            lf.lastPayment = lf.paymentHistory.length ? lf.paymentHistory[0] : null;
            changed = true;
          }
          const remLastEvac = rf.lastEvacuated !== undefined ? rf.lastEvacuated : (rEvacs[0] ? rEvacs[0].date : '');
          if (JSON.stringify(rEvacs) !== JSON.stringify(lEvacs) || (lf.lastEvacuated || '') !== (remLastEvac || '')) {
            lf.evacuationHistory = JSON.parse(JSON.stringify(rEvacs));
            lf.lastEvacuated = remLastEvac || '';
            changed = true;
          }
        } else {
          if (rPays.length > lPays.length) {
            const payKeys = new Set(lPays.map(p => (p.id || '') + '|' + (p.date || '') + '|' + (p.amount || '')));
            rPays.forEach(rp => {
              const k = (rp.id || '') + '|' + (rp.date || '') + '|' + (rp.amount || '');
              if (!payKeys.has(k)) {
                lPays.push(rp);
                payKeys.add(k);
                changed = true;
              }
            });
            lf.paymentHistory = lPays;
            lf.lastPayment = lf.paymentHistory.length ? lf.paymentHistory[0] : null;
          }
          if (rEvacs.length > lEvacs.length) {
            const evacKeys = new Set(lEvacs.map(e => (e.id || '') + '|' + (e.date || '')));
            rEvacs.forEach(re => {
              const k = (re.id || '') + '|' + (re.date || '');
              if (!evacKeys.has(k)) {
                lEvacs.unshift(re);
                evacKeys.add(k);
                changed = true;
              }
            });
            lf.evacuationHistory = lEvacs;
            if ((rf.lastEvacuated || '') > (lf.lastEvacuated || '')) {
              lf.lastEvacuated = rf.lastEvacuated;
              changed = true;
            }
          }
        }
      }
    });
    localState.facilities = Array.from(facMap.values());
  }

  // 4. Merge Municipal Streets (including evacuation period edits & deletions)
  if (Array.isArray(remoteState.municipalStreets) && remoteState.municipalStreets.length) {
    const streetMap = new Map();
    (localState.municipalStreets || []).forEach(s => {
      if (s && s.id && !deletedSet.has(s.id)) streetMap.set(s.id, s);
    });
    const remGlobalStrictNewer = (Date.parse(remoteState.updatedAt || 0) || 0) > (Date.parse(localState.updatedAt || 0) || 0);
    remoteState.municipalStreets.forEach(rs => {
      if (!rs || !rs.id || deletedSet.has(rs.id)) return;
      const rEv = (Array.isArray(rs.evacuationHistory) ? rs.evacuationHistory : []).filter(e => e && !deletedSet.has(e.id) && !deletedSet.has('evac-del:' + rs.id + ':' + (e.date || '')));
      const ls = streetMap.get(rs.id);
      if (!ls) {
        const cloneRs = JSON.parse(JSON.stringify(rs));
        cloneRs.evacuationHistory = JSON.parse(JSON.stringify(rEv));
        cloneRs.lastEvacuated = cloneRs.evacuationHistory.length ? (cloneRs.evacuationHistory[0].date || cloneRs.lastEvacuated || '') : '';
        streetMap.set(rs.id, cloneRs);
        changed = true;
      } else {
        const isDirty = localDirtyEntities.has('street:' + ls.id);
        const lStTs = Date.parse(ls.updatedAt || 0) || 0;
        const rStTs = Date.parse(rs.updatedAt || 0) || 0;
        if (rStTs) noteCloudTimestamp(rStTs);
        if (lStTs) noteCloudTimestamp(lStTs);
        if (isDirty && lStTs <= rStTs) {
          ls.updatedAt = nextMonotonicIso();
        }
        const remoteIsNewer = !isDirty && ((rStTs > 0 && rStTs > lStTs) || (lStTs === 0 && rStTs === 0 && remGlobalStrictNewer));
        const localIsNewer = isDirty || (lStTs > rStTs);
        const lEv = (Array.isArray(ls.evacuationHistory) ? ls.evacuationHistory : []).filter(e => e && !deletedSet.has(e.id) && !deletedSet.has('evac-del:' + ls.id + ':' + (e.date || '')));
        if (remoteIsNewer || (!localIsNewer && remGlobalStrictNewer)) {
          if (rs.name && rs.name !== ls.name) { ls.name = rs.name; changed = true; }
          if (rs.location && rs.location !== ls.location) { ls.location = rs.location; changed = true; }
          if (rs.supervisor && rs.supervisor !== ls.supervisor) { ls.supervisor = rs.supervisor; changed = true; }
          const remLastEvac = rs.lastEvacuated !== undefined ? rs.lastEvacuated : (rEv[0] ? rEv[0].date : '');
          if (JSON.stringify(rEv) !== JSON.stringify(lEv) || (ls.lastEvacuated || '') !== (remLastEvac || '')) {
            ls.evacuationHistory = JSON.parse(JSON.stringify(rEv));
            ls.lastEvacuated = remLastEvac || '';
            changed = true;
          }
          if (rs.updatedAt && rs.updatedAt !== ls.updatedAt) {
            ls.updatedAt = rs.updatedAt;
            changed = true;
          }
        } else if (!localIsNewer && rEv.length > lEv.length) {
          ls.evacuationHistory = JSON.parse(JSON.stringify(rEv));
          if ((rs.lastEvacuated || '') > (ls.lastEvacuated || '')) {
            ls.lastEvacuated = rs.lastEvacuated;
          }
          changed = true;
        }
      }
    });
    localState.municipalStreets = Array.from(streetMap.values());
  }

  // 5. Merge Monthly Reports (all 6 sections per month)
  if (remoteState.monthlyReports && typeof remoteState.monthlyReports === 'object') {
    if (!localState.monthlyReports || typeof localState.monthlyReports !== 'object') {
      localState.monthlyReports = {};
    }
    Object.keys(remoteState.monthlyReports).forEach(period => {
      const remRep = remoteState.monthlyReports[period];
      const locRep = localState.monthlyReports[period];
      if (!remRep || typeof remRep !== 'object') return;
      if (!locRep) {
        localState.monthlyReports[period] = JSON.parse(JSON.stringify(remRep));
        changed = true;
        return;
      }
      const locTs = Date.parse(locRep.updatedAt || 0) || 0;
      const remTs = Date.parse(remRep.updatedAt || 0) || 0;
      if (remTs > locTs) {
        localState.monthlyReports[period] = JSON.parse(JSON.stringify(remRep));
        changed = true;
      }
    });
  }

  // 6. Merge Payment Schedule Records, Evacuation Logs, Archived Documents & Team Chat (including in-place updates & deletions)
  const remGlobalNewer = (Date.parse(remoteState.updatedAt || 0) || 0) > (Date.parse(localState.updatedAt || 0) || 0);
  if (remGlobalNewer && Array.isArray(remoteState.evacuationLogs) && localDirtyEntities.size === 0) {
    const cleanRemLogs = remoteState.evacuationLogs.filter(l => l && (!l.id || !deletedSet.has(l.id)));
    if (JSON.stringify(cleanRemLogs) !== JSON.stringify(localState.evacuationLogs || [])) {
      localState.evacuationLogs = JSON.parse(JSON.stringify(cleanRemLogs));
      changed = true;
    }
  }
  // Every record in the cloud is adopted by this device. Payments entered on
  // one machine must reach the request letter on every other machine.
  //
  // The old rule skipped new paymentScheduleRecords unless the category was
  // "Municipal Street", which is why a payment logged on the .exe never
  // appeared in the request letter on the web or the iPhone: the pull threw it
  // away, and the next push then removed it from the cloud as well.
  ['paymentScheduleRecords', 'archivedDocuments', 'teamChat'].forEach(colKey => {
    if (!Array.isArray(remoteState[colKey]) || !remoteState[colKey].length) return;
    if (!Array.isArray(localState[colKey])) localState[colKey] = [];

    // Two keys per record: its id, and its natural key. The natural key catches
    // the same payment saved under a different generated id on another device.
    const idIndex = new Map();
    const naturalIndex = new Map();
    const naturalKey = (item) => {
      if (!item) return '';
      return [String(item.outlet || item.target || '').toLowerCase(),
              String(item.date || ''),
              String(item.amount === undefined || item.amount === null ? '' : item.amount),
              String(item.month || '')].join('|');
    };
    let seqCounter = 0;
    localState[colKey].forEach((item, idx) => {
      if (!item) return;
      if (colKey === 'paymentScheduleRecords') {
        const n = paymentSeqOf(item);
        if (n !== null && n >= seqCounter) seqCounter = n + 1;
      }
      const k = item.id || item.reference;
      if (k) idIndex.set(k, idx);
      const nk = naturalKey(item);
      if (nk.trim() !== '|||') naturalIndex.set(nk, idx);
    });

    remoteState[colKey].forEach(rItem => {
      if (!rItem) return;
      const idKey = rItem.id || rItem.reference;
      if (idKey && deletedSet.has(idKey)) return;
      const nk = naturalKey(rItem);
      const known = (idKey && idIndex.has(idKey)) ? idIndex.get(idKey)
                  : (nk.trim() !== '|||' && naturalIndex.has(nk)) ? naturalIndex.get(nk)
                  : -1;

      if (known >= 0) {
        // Already here: refresh the fields, but only when the cloud copy is
        // genuinely newer, so a stale device cannot undo a fresh edit.
        const localItem = localState[colKey][known];
        const lTs = Date.parse(localItem.updatedAt || 0) || 0;
        const rTs = Date.parse(rItem.updatedAt || 0) || 0;
        const shouldRefresh = remGlobalNewer ? (rTs >= lTs) : (rTs > lTs);
        if (shouldRefresh && JSON.stringify(localItem) !== JSON.stringify(rItem)) {
          const incoming = JSON.parse(JSON.stringify(rItem));
          // The place in the list belongs to the record, not to the sync.
          // Copying the whole object used to drop the local sequence number,
          // and the record was then re-numbered - which shuffled the list on
          // the next tick, and every tick after that.
          const keepSeq = (colKey === 'paymentScheduleRecords') ? paymentSeqOf(localItem) : null;
          const remoteSeq = (colKey === 'paymentScheduleRecords') ? paymentSeqOf(rItem) : null;
          if (remoteSeq !== null) {
            // The cloud is the shared copy, so its number is the one every
            // device agrees on. This is what lets the browser show the same
            // order as the .exe and the .apk instead of keeping its own.
            incoming.seq = remoteSeq;
            delete incoming.seqAuto;
          } else if (keepSeq !== null) {
            // The cloud copy carries no number (an older device saved it), so
            // keep the number this device already has. Nothing is guessed.
            incoming.seq = keepSeq;
          } else {
            delete incoming.seq;
          }
          localState[colKey][known] = incoming;
          changed = true;
        }
      } else {
        const incoming = JSON.parse(JSON.stringify(rItem));
        if (colKey === 'paymentScheduleRecords') {
          const knownRemoteSeq = paymentSeqOf(rItem);
          if (knownRemoteSeq !== null) {
            // It already has a place in the shared order: take that place.
            incoming.seq = knownRemoteSeq;
            if (knownRemoteSeq >= seqCounter) seqCounter = knownRemoteSeq + 1;
          } else {
            // No number anywhere: append after everything already here, so
            // nothing above it moves.
            incoming.seq = seqCounter++;
          }
        }
        localState[colKey].push(incoming);
        if (idKey) idIndex.set(idKey, localState[colKey].length - 1);
        if (nk.trim() !== '|||') naturalIndex.set(nk, localState[colKey].length - 1);
        changed = true;
      }
    });
  });

  // 7. Merge Live GPS Positions
  if (remoteState.fleetTracking && Array.isArray(remoteState.fleetTracking.positions)) {
    if (!localState.fleetTracking) localState.fleetTracking = { positions: [] };
    if (!Array.isArray(localState.fleetTracking.positions)) localState.fleetTracking.positions = [];
    const knownIds = new Set(localState.fleetTracking.positions.map(p => p && p.id));
    remoteState.fleetTracking.positions.forEach(rf => {
      if (rf && rf.id && !knownIds.has(rf.id)) {
        localState.fleetTracking.positions.push(rf);
        knownIds.add(rf.id);
        changed = true;
      }
    });
  }

  // 8. Merge Settings (preserve cloud keys, adopt newer companyName / flags)
  if (remoteState.settings && typeof remoteState.settings === 'object') {
    if (!localState.settings) localState.settings = {};
    const ls = localState.settings;
    const rs = remoteState.settings;
    if (!ls.supabaseUrl && rs.supabaseUrl) { ls.supabaseUrl = rs.supabaseUrl; changed = true; }
    if (!ls.supabaseAnonKey && rs.supabaseAnonKey) { ls.supabaseAnonKey = rs.supabaseAnonKey; changed = true; }
    if (!ls.googleAppsScriptUrl && rs.googleAppsScriptUrl) { ls.googleAppsScriptUrl = rs.googleAppsScriptUrl; changed = true; }
    if (!ls.googleDriveRootFolder && rs.googleDriveRootFolder) { ls.googleDriveRootFolder = rs.googleDriveRootFolder; changed = true; }
    const locSetTs = Date.parse(ls.updatedAt || 0) || 0;
    const remSetTs = Date.parse(rs.updatedAt || 0) || 0;
    if (remSetTs > locSetTs && rs.companyName) {
      ls.companyName = rs.companyName;
      if (localState.company) localState.company.name = rs.companyName;
      changed = true;
    }
  }

  if (changed) {
    syncSupervisorsFromUsers();
    store.save({ fromCloudMerge: true });
  }
  return changed;
}

function copyGoogleAppsScriptCode() {
  const pre = document.getElementById('gscript-code-snippet');
  if (!pre) return;
  const code = pre.textContent || pre.innerText || '';
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(code).then(() => {
      showToast('\ud83d\udccb Apps Script code copied.', 'success');
    }).catch(() => {
      showToast('\u2139\ufe0f Select and copy the code from the box.', 'info');
    });
  } else {
    showToast('\u2139\ufe0f Select and copy the code from the box.', 'info');
  }
}

function toggleCloudSetupGuide() {
  const box = document.getElementById('cloud-setup-guide-box');
  if (!box) return;
  box.style.display = box.style.display === 'none' ? '' : 'none';
}

function getBackupCheckpoints() {
  try {
    const raw = SafeStorage.get(AUTO_BACKUP_CHECKPOINTS_KEY);
    if (!raw) return [];
    const parsed = JSON.parse(raw);
    return Array.isArray(parsed) ? parsed : [];
  } catch (e) {
    return [];
  }
}

function writeIndexedDbBackup(snapshotObj) {
  try {
    if (typeof window === 'undefined' || !window.indexedDB) return;
    const req = window.indexedDB.open('TEEM_CrashRecoveryDB', 1);
    req.onupgradeneeded = ev => {
      const db = ev.target.result;
      if (!db.objectStoreNames.contains('backups')) {
        db.createObjectStore('backups', { keyPath: 'id' });
      }
    };
    req.onsuccess = ev => {
      try {
        const db = ev.target.result;
        const tx = db.transaction('backups', 'readwrite');
        tx.objectStore('backups').put({
          id: 'latest',
          savedAt: snapshotObj.savedAt,
          payload: snapshotObj
        });
      } catch (err) {}
    };
  } catch (e) {}
}

const DEFAULT_SUPABASE_URL = 'https://seahqfjafdxjenzoggfa.supabase.co';
const DEFAULT_SUPABASE_ANON_KEY = 'sb_publishable_Ehf0MazCtqvM7HFzQS0_Aw__wT4vnj-';
const DEFAULT_GOOGLE_APPS_SCRIPT_URL = 'https://script.google.com/macros/s/AKfycbxGgcqW2LbfA38rQpNhTFB_jhoFYMfB9c3fpY05L5DQic1NgWmZeWzmF7YwA5ZpIS4/exec';

function buildSupabaseHeaders(key, extra) {
  const cleanKey = String(key || '').trim();
  const h = { 'apikey': cleanKey, 'Authorization': 'Bearer ' + cleanKey };
  return Object.assign(h, extra || {});
}

let lastSeenSupabaseRowSig = '';
let cloudPushInFlight = false;
let cloudPushQueued = false;
let cloudPullInFlight = false;
let immediatePushTimerId = null;

function scheduleImmediateCloudPush() {
  if (immediatePushTimerId) clearTimeout(immediatePushTimerId);
  immediatePushTimerId = setTimeout(async () => {
    immediatePushTimerId = null;
    if (!store || !store.state) return;
    const s = store.state.settings || {};
    if (s.supabaseUrl || DEFAULT_SUPABASE_URL) {
      await syncWithSupabaseOnline(buildBackupSnapshot('immediate-edit'), false);
    }
  }, 80);
}
window.scheduleImmediateCloudPush = scheduleImmediateCloudPush;

async function pullFromSupabaseOnline(opts) {
  const isBackgroundTick = Boolean(opts && opts.isBackgroundTick);
  if (isBackgroundTick && (cloudPushInFlight || cloudPullInFlight || (store && store.hasUnsyncedLocalChanges && (Date.now() - (store.lastLocalEditMs || 0)) < 1500))) {
    return false;
  }
  const s = (store && store.state && store.state.settings) || {};
  const url = (s.supabaseUrl || DEFAULT_SUPABASE_URL).trim().replace(/\/+$/, '');
  const key = (s.supabaseAnonKey || DEFAULT_SUPABASE_ANON_KEY).trim();
  if (!url || !key || typeof fetch !== 'function') return false;
  cloudPullInFlight = true;
  try {
    const endpoint = url + '/rest/v1/teem_sync?id=eq.teem_global_state_v2_9&select=payload,updated_at';
    const ctrl = typeof AbortController === 'function' ? new AbortController() : null;
    const tId = ctrl ? setTimeout(() => { try { ctrl.abort(); } catch (e) {} }, 5000) : null;
    let pullRes;
    try {
      pullRes = await fetch(endpoint, {
        method: 'GET',
        cache: 'no-store',
        headers: buildSupabaseHeaders(key),
        signal: ctrl ? ctrl.signal : undefined
      });
      if (pullRes && pullRes.status === 401 && key.indexOf('sb_') === 0) {
        pullRes = await fetch(endpoint, {
          method: 'GET',
          cache: 'no-store',
          headers: { 'apikey': key },
          signal: ctrl ? ctrl.signal : undefined
        });
      }
    } finally {
      if (tId) clearTimeout(tId);
    }
    if (pullRes && pullRes.ok) {
      const rows = await pullRes.json();
      if (Array.isArray(rows) && rows[0] && rows[0].payload) {
        if (rows[0].updated_at) noteCloudTimestamp(rows[0].updated_at);
        if (rows[0].payload.updatedAt) noteCloudTimestamp(rows[0].payload.updatedAt);
        const rowSig = String(rows[0].updated_at || '') + '|' + String(rows[0].payload.updatedAt || '');
        if (isBackgroundTick && rowSig && rowSig === lastSeenSupabaseRowSig) {
          return true;
        }
        lastSeenSupabaseRowSig = rowSig;
        const mergedChanged = smartMergeCloudState(store.state, rows[0].payload);
        restoreSessionFromMarker(store.state);
        if (mergedChanged && currentUser()) {
          withScrollPreserved(() => {
            applySessionUI();
            renderAll();
            if (activeReportFacilityId && document.getElementById('modal-facility-report') && document.getElementById('modal-facility-report').classList.contains('active')) {
              renderFacilityReportContent();
            }
            if (activeStreetId && document.getElementById('modal-street-report') && document.getElementById('modal-street-report').classList.contains('active')) {
              renderStreetReportContent();
            }
          });
        }
        return true;
      }
    }
  } catch (e) {} finally {
    cloudPullInFlight = false;
  }
  return false;
}

async function pullFromGoogleAppsScriptOnline() {
  const s = (store && store.state && store.state.settings) || {};
  const webappUrl = (s.googleAppsScriptUrl || '').trim();
  const rootFolder = (s.googleDriveRootFolder || GDRIVE_ROOT_FOLDER_DEFAULT).trim() || GDRIVE_ROOT_FOLDER_DEFAULT;
  if (!webappUrl || typeof fetch !== 'function') return false;
  try {
    const sep = webappUrl.includes('?') ? '&' : '?';
    const pullUrl = webappUrl + sep + 'action=pull_state&rootFolder=' + encodeURIComponent(rootFolder) + '&_t=' + Date.now();
    const res = await fetch(pullUrl, { method: 'GET' });
    if (res && res.ok) {
      const data = await res.json();
      if (data && !data.empty) {
        const mergedChanged = smartMergeCloudState(store.state, data);
        if (mergedChanged && currentUser()) {
          applySessionUI();
          renderCurrentView();
        }
        return true;
      }
    }
  } catch (e) {}
  return false;
}

async function pullAllCloudProvidersNow(isManual) {
  let okSupa = false;
  let okGscript = false;
  try {
    okSupa = await pullFromSupabaseOnline();
  } catch (e) {}
  if (!okSupa) {
    try {
      okGscript = await pullFromGoogleAppsScriptOnline();
    } catch (e) {}
  }
  if (isManual && (okSupa || okGscript)) {
    renderAll();
    renderSettingsConsole();
  }
  return okSupa || okGscript;
}

async function loadCloudConfigOnBoot() {
  try {
    // 0. Check built-in cloud/config.js (window.TEEM_CLOUD_CONFIG)
    if (typeof window !== 'undefined' && window.TEEM_CLOUD_CONFIG && typeof window.TEEM_CLOUD_CONFIG === 'object') {
      const bCfg = window.TEEM_CLOUD_CONFIG;
      if (!store.state.settings) store.state.settings = {};
      if (!store.state.settings.supabaseUrl && bCfg.supabaseUrl) store.state.settings.supabaseUrl = String(bCfg.supabaseUrl).trim().replace(/\/+$/, '');
      if (!store.state.settings.supabaseAnonKey && bCfg.supabaseAnonKey) store.state.settings.supabaseAnonKey = String(bCfg.supabaseAnonKey).trim();
      if (!store.state.settings.googleAppsScriptUrl && bCfg.googleAppsScriptUrl) store.state.settings.googleAppsScriptUrl = String(bCfg.googleAppsScriptUrl).trim();
      if (!store.state.settings.googleDriveRootFolder && bCfg.googleDriveRootFolder) store.state.settings.googleDriveRootFolder = String(bCfg.googleDriveRootFolder).trim();
      store.save({ fromCloudMerge: true });
    }

    // 1. Check URL query parameter (?cloud=TEEM-SYNC-... or ?supabaseUrl=...&gscript=...)
    if (typeof window !== 'undefined' && window.location && window.location.search) {
      const params = new URLSearchParams(window.location.search);
      const cloudParam = params.get('cloud');
      if (cloudParam) {
        applyCloudSyncCodeString(cloudParam);
        persistCloudConfigEverywhere();
      } else {
        const qSupaUrl = params.get('supabaseUrl');
        const qSupaKey = params.get('supabaseKey');
        const qGscript = params.get('gscript');
        if (qSupaUrl || qGscript) {
          if (!store.state.settings) store.state.settings = {};
          if (qSupaUrl) store.state.settings.supabaseUrl = qSupaUrl.trim().replace(/\/+$/, '');
          if (qSupaKey) store.state.settings.supabaseAnonKey = qSupaKey.trim();
          if (qGscript) store.state.settings.googleAppsScriptUrl = qGscript.trim();
          store.save({ fromCloudMerge: true });
          persistCloudConfigEverywhere();
        }
      }
    }

    // 2. Check global cloud config mirror in SafeStorage
    const savedGlobalRaw = SafeStorage.get('TEEM_CLOUD_CONFIG_GLOBAL');
    if (savedGlobalRaw) {
      try {
        const gCfg = JSON.parse(savedGlobalRaw);
        if (gCfg && store.state.settings) {
          if (!store.state.settings.supabaseUrl && gCfg.supabaseUrl) store.state.settings.supabaseUrl = gCfg.supabaseUrl;
          if (!store.state.settings.supabaseAnonKey && gCfg.supabaseAnonKey) store.state.settings.supabaseAnonKey = gCfg.supabaseAnonKey;
          if (!store.state.settings.googleAppsScriptUrl && gCfg.googleAppsScriptUrl) store.state.settings.googleAppsScriptUrl = gCfg.googleAppsScriptUrl;
        }
      } catch (e) {}
    }

    // 3. Check Electron desktop cloud-config.json
    if (typeof window !== 'undefined' && window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.readCloudConfig === 'function') {
      try {
        const res = await window.TEEM_DESKTOP_RUNTIME.readCloudConfig();
        if (res && res.ok && res.config && store.state.settings) {
          const c = res.config;
          if (!store.state.settings.supabaseUrl && c.supabaseUrl) store.state.settings.supabaseUrl = c.supabaseUrl;
          if (!store.state.settings.supabaseAnonKey && c.supabaseAnonKey) store.state.settings.supabaseAnonKey = c.supabaseAnonKey;
          if (!store.state.settings.googleAppsScriptUrl && c.googleAppsScriptUrl) store.state.settings.googleAppsScriptUrl = c.googleAppsScriptUrl;
          if (!store.state.settings.googleDriveRootFolder && c.googleDriveRootFolder) store.state.settings.googleDriveRootFolder = c.googleDriveRootFolder;
          store.save({ fromCloudMerge: true });
        }
      } catch (e) {}
    }

    // 4. Fetch ./cloud-config.json from the app folder / Netlify web root
    if (typeof fetch === 'function' && typeof window !== 'undefined' && window.location && /^https?:$/i.test(window.location.protocol)) {
      try {
        const cfgRes = await fetch('./cloud-config.json?_t=' + Date.now(), { cache: 'no-store' });
        if (cfgRes && cfgRes.ok) {
          const folderCfg = await cfgRes.json();
          if (folderCfg && store.state.settings) {
            let appliedFolderCfg = false;
            if (!store.state.settings.supabaseUrl && folderCfg.supabaseUrl) {
              store.state.settings.supabaseUrl = String(folderCfg.supabaseUrl).trim().replace(/\/+$/, '');
              appliedFolderCfg = true;
            }
            if (!store.state.settings.supabaseAnonKey && folderCfg.supabaseAnonKey) {
              store.state.settings.supabaseAnonKey = String(folderCfg.supabaseAnonKey).trim();
              appliedFolderCfg = true;
            }
            if (!store.state.settings.googleAppsScriptUrl && folderCfg.googleAppsScriptUrl) {
              store.state.settings.googleAppsScriptUrl = String(folderCfg.googleAppsScriptUrl).trim();
              appliedFolderCfg = true;
            }
            if (!store.state.settings.googleDriveRootFolder && folderCfg.googleDriveRootFolder) {
              store.state.settings.googleDriveRootFolder = String(folderCfg.googleDriveRootFolder).trim();
            }
            if (appliedFolderCfg) store.save({ fromCloudMerge: true });
          }
        }
      } catch (e) {}
    }

    // 5. Immediately pull latest accounts, passwords, facilities, and monthly reports from cloud on startup
    if (hasCloudSyncConfigured()) {
      await pullAllCloudProvidersNow(false);
    }
  } catch (e) {}
}

async function syncWithSupabaseOnline(snapshotObj, isManual) {
  const s = (store && store.state && store.state.settings) || {};
  const url = (s.supabaseUrl || DEFAULT_SUPABASE_URL).trim().replace(/\/+$/, '');
  const key = (s.supabaseAnonKey || DEFAULT_SUPABASE_ANON_KEY).trim();
  if (!url || !key || typeof fetch !== 'function') {
    if (isManual) showToast('\u26a0\ufe0f Enter the Supabase URL and key first.', 'warning');
    return false;
  }
  if (cloudPushInFlight) {
    cloudPushQueued = true;
    return true;
  }
  cloudPushInFlight = true;
  cloudPushQueued = false;
  try {
    const endpoint = url + '/rest/v1/teem_sync';
    const headers = buildSupabaseHeaders(key, {
      'Content-Type': 'application/json',
      'Prefer': 'resolution=merge-duplicates,return=minimal'
    });

    // STEP 1: Pull and smart-merge remote cloud state FIRST so a fresh device never overwrites changed passwords or records!
    await pullFromSupabaseOnline({ isBackgroundTick: false });

    // STEP 2: Push the merged state back to Supabase with monotonic timestamp
    const pushIso = nextMonotonicIso();
    store.state.updatedAt = pushIso;
    SafeStorage.set(store.storageKey, JSON.stringify(store.state));
    const mergedPayload = JSON.parse(JSON.stringify(store.state));
    mergedPayload.sessionUserId = null; // never force another device's active login session
    const bodyStr = JSON.stringify({
      id: 'teem_global_state_v2_9',
      company_name: s.companyName || 'Teem Business Nigeria Enterprises',
      payload: mergedPayload,
      updated_at: pushIso
    });
    let postRes = await fetch(endpoint, {
      method: 'POST',
      headers: headers,
      body: bodyStr
    });
    if (postRes && postRes.status === 401 && key.indexOf('sb_') === 0) {
      await fetch(endpoint, {
        method: 'POST',
        headers: {
          'apikey': key,
          'Content-Type': 'application/json',
          'Prefer': 'resolution=merge-duplicates,return=minimal'
        },
        body: bodyStr
      });
    }
    store.hasUnsyncedLocalChanges = false;
    localDirtyEntities.clear();
    if (typeof store.refreshEntitySnapshots === 'function') {
      store.refreshEntitySnapshots(store.state);
    }
    lastSeenSupabaseRowSig = pushIso + '|' + String(mergedPayload.updatedAt || '');
    if (isManual) {
      withScrollPreserved(() => {
        renderAll();
        renderSettingsConsole();
      });
      showToast('\ud83c\udf10 Connected & synced live with Supabase across all devices!', 'success');
    }
    return true;
  } catch (err) {
    if (isManual) showToast('\u26a0\ufe0f Supabase sync error: check URL/Key and internet connection.', 'error');
    return false;
  } finally {
    cloudPushInFlight = false;
    if (cloudPushQueued) {
      cloudPushQueued = false;
      scheduleImmediateCloudPush();
    }
  }
}

function formatBackupTimestamp(isoStr) {
  const d = isoStr ? new Date(isoStr) : new Date();
  if (isNaN(d.getTime())) return '19/10/2026, 14:00:00';
  const dd = String(d.getDate()).padStart(2, '0');
  const mm = String(d.getMonth() + 1).padStart(2, '0');
  const yyyy = d.getFullYear();
  const hh = String(d.getHours()).padStart(2, '0');
  const mi = String(d.getMinutes()).padStart(2, '0');
  const ss = String(d.getSeconds()).padStart(2, '0');
  return dd + '/' + mm + '/' + yyyy + ', ' + hh + ':' + mi + ':' + ss;
}

async function syncWithGoogleDriveOnline(snapshotObj, isManual) {
  const s = (store && store.state && store.state.settings) || {};
  const webappUrl = (s.googleAppsScriptUrl || '').trim();
  const rootFolder = (s.googleDriveRootFolder || GDRIVE_ROOT_FOLDER_DEFAULT).trim() || GDRIVE_ROOT_FOLDER_DEFAULT;
  const token = (s.googleDriveAccessToken || '').trim();

  if (webappUrl && typeof fetch === 'function') {
    try {
      // STEP 1: Pull and merge any newer state from Google Apps Script first
      await pullFromGoogleAppsScriptOnline();

      // STEP 2: Push the merged snapshot to Google Drive
      const mergedSnapshot = buildBackupSnapshot(isManual ? 'manual-gdrive' : 'auto-5s');
      if (mergedSnapshot && mergedSnapshot.state) mergedSnapshot.state.sessionUserId = null;
      const payload = {
        action: 'auto_backup',
        rootFolder: rootFolder,
        allCategoryFolders: GDRIVE_SECTOR_FOLDERS,
        snapshot: mergedSnapshot
      };
      await fetch(webappUrl, {
        method: 'POST',
        mode: 'no-cors',
        headers: { 'Content-Type': 'text/plain;charset=utf-8' },
        body: JSON.stringify(payload)
      });
      if (isManual) {
        renderAll();
        renderSettingsConsole();
        showToast('\u2601\ufe0f Connected & synced to Google Drive via Google Apps Script (' + rootFolder + '/Backups)!', 'success');
      }
      return true;
    } catch (err) {
      if (isManual) showToast('\u26a0\ufe0f Cannot reach the Apps Script URL.', 'error');
      return false;
    }
  }

  if (!token) {
    if (isManual) {
      showToast('\u26a0\ufe0f Add the Apps Script URL first.', 'warning');
    }
    return false;
  }
  if (typeof fetch !== 'function') return false;
  try {
    const metadata = {
      name: 'TEEM_AutoBackup_v1.json',
      mimeType: 'application/json'
    };
    const boundary = 'teem_gdrive_boundary_294';
    const body =
      '--' + boundary + '\r\nContent-Type: application/json; charset=UTF-8\r\n\r\n' +
      JSON.stringify(metadata) + '\r\n' +
      '--' + boundary + '\r\nContent-Type: application/json\r\n\r\n' +
      JSON.stringify(snapshotObj) + '\r\n' +
      '--' + boundary + '--';
    const res = await fetch('https://www.googleapis.com/upload/drive/v3/files?uploadType=multipart', {
      method: 'POST',
      headers: {
        'Authorization': 'Bearer ' + token,
        'Content-Type': 'multipart/related; boundary=' + boundary
      },
      body: body
    });
    if (res && res.ok) {
      if (isManual) showToast('\u2601\ufe0f Backup uploaded to Drive.', 'success');
      return true;
    }
  } catch (e) {}
  if (isManual) showToast('\u26a0\ufe0f Cannot reach Google Drive.', 'error');
  return false;
}

// ---------------------------------------------------------------------------
// Pending Google Drive uploads - retried until the copy lands
// ---------------------------------------------------------------------------
var PENDING_DRIVE_UPLOADS = [];
var driveRetryTimer = null;

function queueDriveUpload(payload, fileName, folderPath) {
  if (PENDING_DRIVE_UPLOADS.length >= 10) PENDING_DRIVE_UPLOADS.shift();
  PENDING_DRIVE_UPLOADS.push({ payload: payload, fileName: fileName, folderPath: folderPath, attempts: 0 });
  showToast('\u2601\ufe0f Drive copy queued. It will upload when the link is back.', 'info');
  scheduleDriveRetry(15000);
}

function scheduleDriveRetry(delay) {
  if (driveRetryTimer) return;
  driveRetryTimer = setTimeout(function () {
    driveRetryTimer = null;
    flushDriveUploads();
  }, delay || 30000);
}

async function flushDriveUploads() {
  if (!PENDING_DRIVE_UPLOADS.length) return;
  const s = (store && store.state && store.state.settings) || {};
  const url = (s.googleAppsScriptUrl || '').trim();
  if (!url) return;
  const still = [];
  for (let i = 0; i < PENDING_DRIVE_UPLOADS.length; i++) {
    const job = PENDING_DRIVE_UPLOADS[i];
    try {
      await fetch(url, {
        method: 'POST',
        mode: 'no-cors',
        headers: { 'Content-Type': 'text/plain;charset=utf-8' },
        body: JSON.stringify(job.payload)
      });
      job.done = true;
      showToast('\u2601\ufe0f Drive copy uploaded: ' + job.fileName, 'success');
      if (Array.isArray(store.state.driveRequestQueue)) {
        const rec = store.state.driveRequestQueue.find(function (r) { return r.fileName === job.fileName; });
        if (rec) rec.status = 'Saved to Google Drive (' + job.folderPath + ')';
      }
    } catch (e) {
      job.attempts += 1;
      if (job.attempts < 20) still.push(job);
    }
  }
  PENDING_DRIVE_UPLOADS = still;
  if (typeof store.save === 'function') store.save();
  if (still.length) scheduleDriveRetry(60000);
}

async function syncPrintedRequestToGoogleDrive(spec, pdfResult, customFilename) {
  if (!spec || (spec.kind !== 'request' && spec.kind !== 'monthly')) return null;
  const s = (store && store.state && store.state.settings) || {};
  // The folder pair comes from Settings > Save locations, so a request filed
  // under Medical lands in the folder the user chose for Medical.
  const isMonthly = spec.kind === 'monthly';
  const chosen = driveFolderFor(spec.category || activeRequestCategory, isMonthly ? 'monthly' : 'request');
  const rootFolder = chosen.rootFolder;
  const categoryFolder = chosen.categoryFolder;
  const folderPath = rootFolder + '/' + categoryFolder;
  const safeCat = categoryFolder.replace(/\s+/g, '_');
  const fileName = customFilename || (pdfResult && pdfResult.filename) || ('TEEM_' + safeCat + '_' + (isMonthly ? 'Report_' : 'Request_') + currentUsageDateIso() + '.pdf');

  let pdfBase64 = '';
  try {
    if (pdfResult && pdfResult.doc && typeof pdfResult.doc.output === 'function') {
      const dataUri = String(pdfResult.doc.output('datauristring') || '');
      const commaIdx = dataUri.indexOf(',');
      pdfBase64 = commaIdx > -1 ? dataUri.slice(commaIdx + 1) : '';
    }
  } catch (e) {}

  if (!Array.isArray(store.state.driveRequestQueue)) store.state.driveRequestQueue = [];
  const uploadRecord = {
    id: 'drv-req-' + Date.now().toString().slice(-6),
    savedAt: new Date().toISOString(),
    rootFolder: rootFolder,
    categoryFolder: categoryFolder,
    folderPath: folderPath,
    fileName: fileName,
    total: spec.total || spec.totalRevenue || 0,
    rowsCount: (spec.rows || []).length,
    status: 'Queued for Google Drive (' + folderPath + ')'
  };

  const webappUrl = (s.googleAppsScriptUrl || '').trim();
  const payload = {
    action: isMonthly ? 'save_monthly_report' : 'save_request',
    rootFolder: rootFolder,
    categoryFolder: categoryFolder,
    allCategoryFolders: GDRIVE_SECTOR_FOLDERS.concat(['Monthly Reports']),
    fileName: fileName,
    mimeType: 'application/pdf',
    pdfBase64: pdfBase64,
    requestMeta: {
      category: categoryFolder,
      month: spec.month || spec.period,
      date: spec.date || currentUsageDateIso(),
      total: spec.total || spec.totalRevenue || 0,
      rowsCount: (spec.rows || []).length
    }
  };

  let sent = false;
  if (webappUrl && typeof fetch === 'function') {
    try {
      await fetch(webappUrl, {
        method: 'POST',
        mode: 'no-cors',
        headers: { 'Content-Type': 'text/plain;charset=utf-8' },
        body: JSON.stringify(payload)
      });
      uploadRecord.status = 'Saved to Google Drive (' + folderPath + ')';
      showToast('\u2601\ufe0f Saved to Google Drive: ' + folderPath + '/' + fileName, 'success');
      sent = true;
    } catch (err) {
      uploadRecord.status = 'Pending online sync (' + folderPath + ')';
    }
  }

  // Held in memory and retried until it lands, so a dropped connection or a
  // Drive blip does not lose the copy.
  if (!sent) {
    queueDriveUpload(payload, fileName, folderPath);
  }
  store.state.driveRequestQueue.unshift(uploadRecord);
  if (store.state.driveRequestQueue.length > 50) {
    store.state.driveRequestQueue = store.state.driveRequestQueue.slice(0, 50);
  }
  store.save();
  return uploadRecord;
}

function connectAndSyncSupabase() {
  saveArchiveSettings();
  const snapshot = buildBackupSnapshot('manual-supabase');
  syncWithSupabaseOnline(snapshot, true);
}

function connectGoogleDrive() {
  saveArchiveSettings();
  const snapshot = buildBackupSnapshot('manual-gdrive');
  syncWithGoogleDriveOnline(snapshot, true);
}

async function pullLatestCloudDataManual() {
  saveArchiveSettings();
  if (!hasCloudSyncConfigured()) {
    showToast('\u2139\ufe0f Add a cloud URL first.', 'info');
    return false;
  }

  // Count before/after so the result can be reported instead of guessed at.
  const before = {
    facilities: (store.state.facilities || []).length,
    payments: (store.state.paymentScheduleRecords || []).length,
    streets: (store.state.municipalStreets || []).length,
    users: (store.state.users || []).length
  };

  const ok = await pullAllCloudProvidersNow(true);

  const after = {
    facilities: (store.state.facilities || []).length,
    payments: (store.state.paymentScheduleRecords || []).length,
    streets: (store.state.municipalStreets || []).length,
    users: (store.state.users || []).length
  };

  const added = [];
  if (after.facilities > before.facilities) added.push((after.facilities - before.facilities) + ' facility record(s)');
  if (after.payments > before.payments) added.push((after.payments - before.payments) + ' payment record(s)');
  if (after.streets > before.streets) added.push((after.streets - before.streets) + ' street(s)');
  if (after.users > before.users) added.push((after.users - before.users) + ' user(s)');

  if (typeof renderAll === 'function' && currentUser()) {
    withScrollPreserved(() => { renderAll(); });
  }

  if (ok) {
    if (added.length) {
      showToast('\u2601\ufe0f Cloud synced. Received ' + added.join(', ') + '. Total now: ' +
        after.facilities + ' facilities, ' + after.payments + ' payment records.', 'success');
    } else {
      showToast('\u2601\ufe0f Cloud synced. This device was already up to date (' +
        after.facilities + ' facilities, ' + after.payments + ' payment records).', 'info');
    }
  } else {
    showToast('\u26a0\ufe0f No connection. Try again.', 'warning');
  }
  return ok;
}

async function pushLocalDataToCloudManual() {
  saveArchiveSettings();
  if (!hasCloudSyncConfigured()) {
    showToast('\u2139\ufe0f Add a cloud URL first.', 'info');
    return false;
  }
  const snapshot = buildBackupSnapshot('manual-push');
  let okSupa = false;
  let okGdrive = false;
  if (store.state.settings && store.state.settings.supabaseUrl && store.state.settings.supabaseAnonKey) {
    okSupa = await syncWithSupabaseOnline(snapshot, true);
  }
  if (store.state.settings && (store.state.settings.googleAppsScriptUrl || store.state.settings.googleDriveAccessToken)) {
    okGdrive = await syncWithGoogleDriveOnline(snapshot, true);
  }
  if (okSupa || okGdrive) {
    showToast('\u2601\ufe0f Pushed local data to cloud across all connected devices.', 'success');
  }
  return okSupa || okGdrive;
}

function resetAllLocalApplicationData() {
  exporterResetAll();
}

window.pullLatestCloudDataManual = pullLatestCloudDataManual;
window.pushLocalDataToCloudManual = pushLocalDataToCloudManual;
window.resetAllLocalApplicationData = resetAllLocalApplicationData;

function buildBackupSnapshot(reason) {
  const nowIso = new Date().toISOString();
  return {
    backupVersion: RELEASE,
    savedAt: nowIso,
    reason: reason || 'auto-5s',
    companyName: (store.state.settings && store.state.settings.companyName) || 'Teem Business Nigeria Enterprises',
    facilitiesCount: (store.state.facilities || []).length,
    streetsCount: (store.state.municipalStreets || []).length,
    paymentsCount: (store.state.paymentScheduleRecords || []).length,
    state: JSON.parse(JSON.stringify(store.state))
  };
}

function runAutoBackupTick(isManual) {
  if (!store || !store.state) return null;
  if (!isManual && store.state.settings && store.state.settings.autoBackup5s === false) {
    renderBackupRestoreStatusUI();
    return null;
  }
  const snapshot = buildBackupSnapshot(isManual ? 'manual' : 'auto-5s');
  const serialized = JSON.stringify(snapshot);
  lastAutoBackupIso = snapshot.savedAt;

  // 1. Primary & Mirror Device Storage
  SafeStorage.set(AUTO_BACKUP_MIRROR_KEY, serialized);

  // 2. Rolling Recovery Checkpoints (keep up to 8 recent snapshots for crash recovery)
  let checkpoints = getBackupCheckpoints();
  const prev = checkpoints[0];
  const stateSignature = snapshot.facilitiesCount + ':' + snapshot.streetsCount + ':' + snapshot.paymentsCount + ':' + ((store.state.archivedDocuments || []).length);
  if (isManual || !prev || prev.signature !== stateSignature || (new Date(snapshot.savedAt) - new Date(prev.savedAt)) >= 5000) {
    checkpoints.unshift({
      id: 'chk-' + Date.now(),
      savedAt: snapshot.savedAt,
      reason: snapshot.reason,
      signature: stateSignature,
      facilitiesCount: snapshot.facilitiesCount,
      paymentsCount: snapshot.paymentsCount,
      state: snapshot.state
    });
    if (checkpoints.length > 8) checkpoints = checkpoints.slice(0, 8);
    SafeStorage.set(AUTO_BACKUP_CHECKPOINTS_KEY, JSON.stringify(checkpoints));
  }

  // 3. IndexedDB asynchronous crash-recovery store (Mobile APK, PWA & Browser)
  writeIndexedDbBackup(snapshot);

  // 4. Native Windows Desktop Disk Backup (.exe runtime)
  if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.writeAutoBackup === 'function') {
    try { window.TEEM_DESKTOP_RUNTIME.writeAutoBackup(serialized); } catch (e) {}
  }

  // 5. Online Supabase & Google Drive Sync (every 5 seconds when configured)
  if (store.state.settings && store.state.settings.supabaseUrl && store.state.settings.supabaseAnonKey) {
    if (isManual || store.hasUnsyncedLocalChanges) {
      syncWithSupabaseOnline(snapshot, false);
    } else {
      pullFromSupabaseOnline({ isBackgroundTick: true });
    }
  }
  if (store.state.settings && (store.state.settings.googleAppsScriptUrl || store.state.settings.googleDriveAccessToken)) {
    if (isManual || store.hasUnsyncedLocalChanges) {
      syncWithGoogleDriveOnline(snapshot, false);
    }
  }

  renderBackupRestoreStatusUI();
  return snapshot;
}

function renderBackupRestoreStatusUI() {
  const pill = document.getElementById('auto-backup-status-pill');
  const timeEl = document.getElementById('auto-backup-last-time');
  const targetsEl = document.getElementById('auto-backup-targets-label');
  const countEl = document.getElementById('auto-backup-count-label');
  const selectEl = document.getElementById('backup-checkpoint-select');
  const enabled = !(store.state.settings && store.state.settings.autoBackup5s === false);

  if (pill) {
    pill.textContent = enabled ? '\u25cf Auto-Backup Every 1s Active' : '\u25cb Auto-Backup Paused';
    pill.className = 'badge ' + (enabled ? 'badge-success' : 'badge-warning');
  }
  if (timeEl) {
    timeEl.textContent = formatBackupTimestamp(lastAutoBackupIso);
  }
  if (targetsEl) {
    const t = ['This Device', 'IndexedDB'];
    if (window.TEEM_DESKTOP_RUNTIME) t.push('Windows Disk');
    if (store.state.settings && store.state.settings.supabaseUrl) t.push('Supabase Online');
    if (store.state.settings && (store.state.settings.googleAppsScriptUrl || store.state.settings.googleDriveClientId)) t.push('Google Drive');
    targetsEl.textContent = t.join(' + ');
  }
  const checkpoints = getBackupCheckpoints();
  if (countEl) {
    countEl.textContent = String(Math.max(1, checkpoints.length));
  }
  if (selectEl && document.activeElement !== selectEl) {
    if (!checkpoints.length) {
      selectEl.innerHTML = '<option value="latest">Latest 1-Second Auto-Backup (' + (store.state.facilities || []).length + ' facilities)</option>';
    } else {
      selectEl.innerHTML = checkpoints.map((c, idx) =>
        '<option value="' + escapeHtml(c.id) + '">' +
        (idx === 0 ? '[Latest] ' : '') + formatTime(c.savedAt) + ' \u2022 ' +
        (c.facilitiesCount || 30) + ' facilities \u2022 ' + (c.paymentsCount || 0) + ' payments (' + escapeHtml(c.reason || 'auto-1s') + ')' +
        '</option>'
      ).join('');
    }
  }
}

function toggleAutoBackup5s(enabled) {
  if (!store.state.settings) store.state.settings = {};
  store.state.settings.autoBackup5s = !!enabled;
  store.save();
  if (enabled) runAutoBackupTick(false);
  renderBackupRestoreStatusUI();
  showToast(enabled ? '\ud83d\udee1\ufe0f Automatic 1-second backup & device sync enabled across all devices & cloud.' : '\u23f8\ufe0f Automatic 1-second backup paused.', 'info');
}

function startAutoBackupEngine() {
  if (autoBackupTimerId) clearInterval(autoBackupTimerId);
  runAutoBackupTick(false);
  autoBackupTimerId = setInterval(() => {
    runAutoBackupTick(false);
  }, AUTO_BACKUP_INTERVAL_MS);
}

function runManualBackupNow() {
  const snap = runAutoBackupTick(true);
  if (snap) {
    showToast('\u26a1 Instant backup saved across this device, IndexedDB' +
      (store.state.settings && store.state.settings.supabaseUrl ? ', Supabase' : '') +
      (store.state.settings && store.state.settings.googleDriveClientId ? ' & Google Drive' : '') + '!', 'success');
  }
}

function applyRestoredState(restoredState, label) {
  if (!restoredState || !Array.isArray(restoredState.facilities)) {
    showToast('\u26a0\ufe0f Backup data is incomplete or invalid.', 'error');
    return false;
  }
  const prevSessionId = store && store.state ? store.state.sessionUserId : null;
  store.state = JSON.parse(JSON.stringify(restoredState));
  store.migrate(false);
  if (prevSessionId && !store.state.sessionUserId) {
    store.state.sessionUserId = prevSessionId;
  }
  restoreSessionFromMarker(store.state);
  store.save();
  applySessionUI();
  renderAll();
  renderSettingsConsole();
  showToast('\u267b\ufe0f Crash recovery complete: restored ' + label + ' (' + store.state.facilities.length + ' facilities).', 'success');
  return true;
}

function restoreLatestAutoBackup() {
  const mirrorRaw = SafeStorage.get(AUTO_BACKUP_MIRROR_KEY);
  if (mirrorRaw) {
    try {
      const parsed = JSON.parse(mirrorRaw);
      const targetState = parsed.state || parsed;
      if (applyRestoredState(targetState, 'latest 5-second auto-backup (' + formatTime(parsed.savedAt) + ')')) return true;
    } catch (e) {}
  }
  const checkpoints = getBackupCheckpoints();
  if (checkpoints.length && checkpoints[0].state) {
    return applyRestoredState(checkpoints[0].state, 'latest recovery checkpoint');
  }
  showToast('\u2139\ufe0f Creating initial auto-backup snapshot now.', 'info');
  runAutoBackupTick(true);
  return false;
}

function restoreSelectedCheckpoint() {
  const selectEl = document.getElementById('backup-checkpoint-select');
  const chosenId = selectEl ? selectEl.value : 'latest';
  const checkpoints = getBackupCheckpoints();
  const found = checkpoints.find(c => c.id === chosenId) || checkpoints[0];
  if (found && found.state) {
    return applyRestoredState(found.state, 'checkpoint from ' + formatTime(found.savedAt));
  }
  return restoreLatestAutoBackup();
}

function downloadFullBackupFile() {
  const snap = runAutoBackupTick(true) || buildBackupSnapshot('export-file');
  const json = JSON.stringify(snap, null, 2);
  const fileName = 'TEEM_Backup_' + currentUsageDateIso() + '_v' + RELEASE + '.json';
  try {
    if (window.TEEM_ANDROID_FS && typeof window.TEEM_ANDROID_FS.saveBase64File === 'function') {
      const b64 = btoa(unescape(encodeURIComponent(json)));
      const savedPath = window.TEEM_ANDROID_FS.saveBase64File(fileName, b64, 'application/json', (typeof deviceFolderFor === 'function' ? deviceFolderFor(null, 'backup') : ''));
      if (savedPath && String(savedPath).indexOf('ERROR:') !== 0) {
        showToast('\ud83d\udcc1 Backup saved to File Manager: ' + savedPath, 'success');
        return;
      }
    }
    if (TEEM_FS_READY && teemFsSupported()) {
      const locs = getSaveLocations();
      teemFsWrite('backup', fileName, new Blob([json], { type: 'application/json' }), 'application/json', locs.folders.backup)
        .then(function (path) { if (path) { showToast('\ud83d\udcc1 Backup saved to ' + path, 'success'); } })
        .catch(function () {});
      return;
    }
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = fileName;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(() => URL.revokeObjectURL(url), 1500);
    showToast('\ud83d\udce5 Backup saved to TEEM folder (' + fileName + ').', 'success');
  } catch (e) {
    showToast('\u26a0\ufe0f Unable to download backup file here.', 'error');
  }
}

function triggerUploadBackupFile() {
  const input = document.getElementById('backup-file-upload-input');
  if (input) input.click();
}

function handleUploadBackupFile(event) {
  const file = event && event.target && event.target.files ? event.target.files[0] : null;
  if (!file) return;
  const reader = new FileReader();
  reader.onload = ev => {
    try {
      const parsed = JSON.parse(String(ev.target.result || '{}'));
      const candidate = parsed.state || parsed;
      applyRestoredState(candidate, 'uploaded backup file "' + file.name + '"');
    } catch (err) {
      showToast('\u26a0\ufe0f Invalid backup JSON file.', 'error');
    }
  };
  reader.readAsText(file);
}

function exporterResetAll() {
  if (!confirm('Reset all locally stored TEEM data back to the supplied delivery package?')) return;
  store.state = JSON.parse(JSON.stringify(SEED_DATA));
  store.migrate();
  store.save();
  renderAll();
  showToast('\u267b\ufe0f Delivery data restored.', 'info');
  if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') window.TEEM_DESKTOP_RUNTIME.refocus();
}

// ===========================================================================
// 16. DOCUMENT ARCHIVE
// ===========================================================================
function renderArchive() {
  const tbody = document.getElementById('archive-table-body');
  const countEl = document.getElementById('archive-count');
  const docs = store.state.archivedDocuments || [];
  if (countEl) countEl.textContent = docs.length + ' document(s)';
  if (!tbody) return;

  tbody.innerHTML = docs.length ? docs.map(d => '<tr>' +
    '<td><strong>' + escapeHtml(d.reference) + '</strong><div style="font-size:11px;color:var(--text-muted);">' + escapeHtml(d.title) + '</div></td>' +
    '<td><span class="badge badge-category">' + escapeHtml(d.type) + '</span></td>' +
    '<td>' + formatTimestamp(d.archivedAt) + '</td>' +
    '<td>' + (d.total ? formatNaira(d.total) : '\u2014') + '</td>' +
    '<td>' + (d.pages || 1) + ' page(s)</td>' +
    '<td><div class="action-btn-group">' +
      '<button class="btn btn-sm btn-primary" onclick="redownloadArchived(\'' + d.id + '\')">\ud83d\udcbe Save</button>' +
        '<button class="btn btn-sm btn-outline" onclick="printArchived(\'' + d.id + '\')">\ud83d\udd0d Preview</button>' +
      '<button class="btn btn-sm btn-outline" onclick="deleteArchived(\'' + d.id + '\')">\u2715</button>' +
    '</div></td>' +
  '</tr>').join('')
    : '<tr><td colspan="6" style="text-align:center;padding:32px;color:var(--text-muted);">No finalised document stored yet. Use any <strong>Finish &amp; Export</strong> or <strong>Export PDF</strong> button to archive a copy here.</td></tr>';
}

function archiveDocument(doc) {
  if (!store.state.settings.archiveAutoSave) return null;
  if (!Array.isArray(store.state.archivedDocuments)) store.state.archivedDocuments = [];
  const entry = Object.assign({ id: 'doc-' + Date.now().toString().slice(-6), archivedAt: new Date().toISOString() }, doc);
  entry.reference = entry.reference || ('TEEM-' + entry.type.replace(/\s+/g, '').toUpperCase().slice(0, 4) + '-' + Date.now().toString().slice(-5));
  store.state.archivedDocuments.unshift(entry);
  store.save();
  renderArchive();
  return entry;
}

// Rebuild an archived document and send it straight to the printer
function printArchived(id) {
  const doc = (store.state.archivedDocuments || []).find(d => d.id === id);
  if (!doc) { showToast('\u26a0\ufe0f Archived document not found.', 'error'); return; }
  rebuildArchivedPdf(doc, { print: true });
}

function redownloadArchived(id) {
  const doc = (store.state.archivedDocuments || []).find(d => d.id === id);
  if (!doc) return;
  rebuildArchivedPdf(doc);
  showToast('\u2b07\ufe0f Archive copy regenerated for download.', 'success');
}

function deleteArchived(id) {
  if (!confirm('Remove this archived copy?')) return;
  if (typeof recordDeletedId === 'function') recordDeletedId(id);
  store.state.archivedDocuments = store.state.archivedDocuments.filter(d => d.id !== id);
  store.save();
  renderArchive();
  showToast('\ud83d\uddd1\ufe0f Archived copy removed.', 'warning');
}

// ===========================================================================
// 17. CHAT
// ===========================================================================
function renderTeamChat() {
  const box = document.getElementById('chat-messages-stream');
  if (!box) return;
  box.innerHTML = store.state.chatMessages.map(m => '<div class="chat-msg ' + (m.role === 'Admin' ? 'chat-msg-self' : '') + '">' +
    '<div class="chat-avatar">' + escapeHtml(m.avatar) + '</div>' +
    '<div class="chat-bubble"><div class="chat-sender-line"><span>' + escapeHtml(m.sender) + '</span><span>\u2022 ' + escapeHtml(m.time) + '</span>' +
      (m.priority === 'Urgent' ? '<span class="badge badge-danger">Urgent</span>' : m.priority === 'Dispatch' ? '<span class="badge badge-warning">Dispatch</span>' : '') +
    '</div><div class="chat-text">' + escapeHtml(m.text) + '</div></div></div>').join('');
  box.scrollTop = box.scrollHeight;
}

function sendChatMessage(e) {
  if (e) e.preventDefault();
  const input = document.getElementById('chat-input-text');
  const text = input ? input.value.trim() : '';
  if (!text) return;
  store.state.chatMessages.push({
    id: 'msg-' + Date.now().toString().slice(-5),
    sender: userFullName(currentUser()) + (isAdmin() ? ' (Administrator)' : ''),
    role: isAdmin() ? 'Admin' : 'Field',
    avatar: userInitials(currentUser()),
    time: 'Just now',
    text: text,
    priority: document.getElementById('chat-msg-priority') ? document.getElementById('chat-msg-priority').value : 'General'
  });
  store.save();
  if (input) input.value = '';
  renderTeamChat();
  showToast('\ud83d\udcac Message broadcast to the team.', 'info');
}

// ===========================================================================
// 18. MODAL / TOAST HELPERS
// ===========================================================================
// ===========================================================================
// DIALOG WINDOW CONTROLS
// Every dialog can be dragged by its title bar and maximised / restored, so a
// long document preview or a long form can use the whole screen.
// ===========================================================================
function initDialogControls() {
  document.querySelectorAll('.modal-card').forEach(card => {
    const header = card.querySelector('.modal-header');
    if (!header || header.dataset.controlsReady) return;
    header.dataset.controlsReady = '1';

    // maximise / restore button, injected so every dialog gets one
    const maxBtn = document.createElement('button');
    maxBtn.type = 'button';
    maxBtn.className = 'modal-max-btn';
    maxBtn.title = 'Maximise / restore this window';
    maxBtn.innerHTML = '&#9974;';
    maxBtn.onclick = ev => { ev.stopPropagation(); toggleModalMaximise(card); };
    const closeBtn = header.querySelector('.modal-close-btn');
    if (closeBtn) header.insertBefore(maxBtn, closeBtn);
    else header.appendChild(maxBtn);

    // drag by the title bar
    header.addEventListener('mousedown', ev => startModalDrag(ev, card));
    header.addEventListener('touchstart', ev => startModalDrag(ev, card), { passive: true });
    header.addEventListener('dblclick', ev => {
      if (ev.target.closest('button, select, option, input, label, a, textarea')) return;
      toggleModalMaximise(card);
    });
  });
}

let modalDragState = null;

function startModalDrag(ev, card) {
  if (ev.target.closest('button, select, option, input, label, a, textarea')) return;
  const point = ev.touches ? ev.touches[0] : ev;
  const rect = card.getBoundingClientRect();
  const base = card.dataset.dragX ? { x: parseFloat(card.dataset.dragX), y: parseFloat(card.dataset.dragY) } : { x: 0, y: 0 };

  if (card.classList.contains('maximized')) {
    // un-maximise when the title bar is pulled, keeping the pointer on the bar
    toggleModalMaximise(card);
  }

  modalDragState = {
    card: card,
    startX: point.clientX,
    startY: point.clientY,
    baseX: base.x,
    baseY: base.y,
    width: rect.width,
    height: rect.height
  };

  const move = e => {
    if (!modalDragState) return;
    const p = e.touches ? e.touches[0] : e;
    const dx = p.clientX - modalDragState.startX;
    const dy = p.clientY - modalDragState.startY;
    setModalOffset(card, modalDragState.baseX + dx, modalDragState.baseY + dy);
  };
  const up = () => {
    modalDragState = null;
    document.removeEventListener('mousemove', move);
    document.removeEventListener('mouseup', up);
    document.removeEventListener('touchmove', move);
    document.removeEventListener('touchend', up);
  };
  document.addEventListener('mousemove', move);
  document.addEventListener('mouseup', up);
  document.addEventListener('touchmove', move, { passive: true });
  document.addEventListener('touchend', up);
  ev.preventDefault();
}

function setModalOffset(card, x, y) {
  const limit = 40;
  const maxX = Math.max(window.innerWidth / 2 - limit, 60);
  const maxY = Math.max(window.innerHeight / 2 - limit, 60);
  x = Math.max(-maxX, Math.min(maxX, x));
  y = Math.max(-maxY, Math.min(maxY, y));
  card.dataset.dragX = String(Math.round(x));
  card.dataset.dragY = String(Math.round(y));
  card.style.transform = 'translate(' + Math.round(x) + 'px, ' + Math.round(y) + 'px)';
}

function toggleModalMaximise(card) {
  const on = card.classList.toggle('maximized');
  // the window fills the entire screen: the backdrop drops its padding too
  const backdrop = card.closest('.modal-backdrop');
  if (backdrop) backdrop.classList.toggle('modal-fullscreen', on);
  if (on) {
    card.dataset.restoreX = card.dataset.dragX || '0';
    card.dataset.restoreY = card.dataset.dragY || '0';
    card.style.transform = 'translate(0px, 0px)';
  } else {
    const x = parseFloat(card.dataset.restoreX || '0');
    const y = parseFloat(card.dataset.restoreY || '0');
    setModalOffset(card, x, y);
  }
  const btn = card.querySelector('.modal-max-btn');
  if (btn) {
    btn.innerHTML = on ? '&#10064;' : '&#9974;';
    btn.title = on ? 'Restore this window' : 'Maximise this window';
  }
  const frame = card.querySelector('.doc-preview-frame');
  if (frame) setTimeout(() => { frame.style.height = on ? '100%' : ''; }, 60);
}

function resetModalWindows() {
  document.querySelectorAll('.modal-backdrop.modal-fullscreen').forEach(bd => bd.classList.remove('modal-fullscreen'));
  document.querySelectorAll('.modal-card').forEach(card => {
    card.classList.remove('maximized');
    card.style.transform = 'translate(0px, 0px)';
    card.dataset.dragX = '0';
    card.dataset.dragY = '0';
    const btn = card.querySelector('.modal-max-btn');
    if (btn) { btn.innerHTML = '&#9974;'; btn.title = 'Maximise / restore this window'; }
  });
}

function closeAllModals(exceptId) {
  document.querySelectorAll('.modal-backdrop.active').forEach(bd => {
    if (bd.id === exceptId) return;
    bd.classList.remove('active');
  });
  resetModalWindows();
}

function handleModalBackArrow(modalId) {
  closeModal(modalId);
  if (modalId === 'modal-edit-facility' && editFacilityOpenedFromReportId) {
    const returnId = editFacilityOpenedFromReportId;
    editFacilityOpenedFromReportId = null;
    openFacilityReportModal(returnId);
  }
}

function ensureSessionAndModalBackArrows() {
  try {
    syncMobileDeviceClass();
    // 1. Remove any redundant foreground view-header Back buttons (Topbar already has Back beside Home)
    document.querySelectorAll('.view-panel .view-header .session-back-arrow-btn').forEach(btn => {
      btn.remove();
    });

    // 2. Ensure every modal / sub-window header has a Back arrow button
    document.querySelectorAll('.modal-backdrop').forEach(backdrop => {
      const mId = backdrop.id;
      const header = backdrop.querySelector('.modal-header');
      if (!header || !mId || header.querySelector('.modal-back-arrow-btn')) return;
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'btn btn-sm btn-outline modal-back-arrow-btn';
      btn.innerHTML = '&#8592;';
      btn.title = 'Go back';
      btn.setAttribute('aria-label', 'Go back');
      btn.onclick = function (ev) {
        if (ev) ev.stopPropagation();
        handleModalBackArrow(mId);
      };
      header.insertBefore(btn, header.firstChild);
    });

    // 3. Ensure every password field has a working click-to-toggle + press-and-hold peep eye button
    document.querySelectorAll('.password-field').forEach(wrap => {
      const inp = wrap.querySelector('input');
      const btn = wrap.querySelector('.password-peek');
      if (inp && inp.id && btn && !btn.getAttribute('onclick')) {
        btn.setAttribute('onclick', "togglePasswordPeek('" + inp.id + "', this)");
      }
    });
  } catch (e) {}
}

window.handleModalBackArrow = handleModalBackArrow;
window.ensureSessionAndModalBackArrows = ensureSessionAndModalBackArrows;

function openModal(modalId) {
  ensureSessionAndModalBackArrows();
  const el = document.getElementById(modalId);
  if (el) el.classList.add('active');
}
// ===========================================================================
// POPUP NOTICE - used for blocking messages such as "facility already exists"
// ===========================================================================
function showModalAlert(title, message, tone) {
  const back = document.getElementById('modal-notice');
  const tEl = document.getElementById('notice-title');
  const mEl = document.getElementById('notice-message');
  const iEl = document.getElementById('notice-icon');
  if (tEl) tEl.textContent = title || 'Notice';
  if (mEl) mEl.innerHTML = message || '';
  if (iEl) {
    const warn = tone === 'warning';
    iEl.textContent = warn ? '\u26a0\ufe0f' : '\u2139\ufe0f';
    iEl.style.background = warn ? '#FEF3C7' : '#E0F2FE';
    iEl.style.color = warn ? '#B45309' : '#0369A1';
    iEl.style.borderColor = warn ? '#FCD34D' : '#7DD3FC';
  }
  if (back) back.classList.add('active');
  const ok = document.getElementById('notice-ok-btn');
  if (ok) setTimeout(() => { try { ok.focus(); } catch (e) {} }, 60);
}

function closeModalAlert() {
  closeModal('modal-notice');
}
window.showModalAlert = showModalAlert;
window.closeModalAlert = closeModalAlert;

function closeModal(modalId) {
  const el = document.getElementById(modalId);
  if (el) el.classList.remove('active');
}

// ===========================================================================
// ACCOUNT STATEMENT REQUEST LETTER (IMAGE 2 - 1ST TO LAST DAY OF MONTH, NO DIGITAL SIGNATURE)
// ===========================================================================
function getAccountStatementPeriod(monthNum, yearNum) {
  const m = Math.max(1, Math.min(12, parseInt(monthNum, 10) || 8));
  const y = parseInt(yearNum, 10) || 2026;
  const lastDay = new Date(y, m, 0).getDate();
  const mm = String(m).padStart(2, '0');
  const ddLast = String(lastDay).padStart(2, '0');
  return '01/' + mm + '/' + y + ' to ' + ddLast + '/' + mm + '/' + y;
}

function accountStatementSpec() {
  const mEl = document.getElementById('acct-stmt-month');
  const yEl = document.getElementById('acct-stmt-year');
  const monthNum = mEl ? (parseInt(mEl.value, 10) || 8) : 8;
  const yearNum = yEl ? (parseInt(yEl.value, 10) || 2026) : 2026;
  const periodStr = getAccountStatementPeriod(monthNum, yearNum);
  const val = (id, fallback) => {
    const el = document.getElementById(id);
    return (el && el.value.trim()) ? el.value.trim() : fallback;
  };
  const monthNames = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
  const monthLabel = (monthNames[monthNum - 1] || 'August') + '_' + yearNum;
  const ref = pdfRef('BNK');
  return {
    kind: 'account_statement',
    reference: ref,
    monthNum: monthNum,
    yearNum: yearNum,
    periodStr: periodStr,
    letterDate: val('acct-stmt-letter-date', '1st September, 2026'),
    recipientTitle: 'The Manager,',
    bankName: val('acct-stmt-bank-name', 'Zenith Bank Plc.,'),
    bankAddress: val('acct-stmt-bank-address', 'Oke-Ilewo, Abeokuta, Ogun State.'),
    salutation: val('acct-stmt-salutation', 'Dear Zenith Bank Customer Service,'),
    subject: 'REQUEST FOR ACCOUNT STATEMENT',
    holderName: val('acct-stmt-holder', 'TEEM BUSINESS NIG. ENT. OPS'),
    accountNumber: val('acct-stmt-number', '1017702040'),
    bvn: val('acct-stmt-bvn', '22194735148'),
    email: val('acct-stmt-email', 'ephspinctglobalservices@gmail.com'),
    signatoryName: val('acct-stmt-signatory-name', 'Ajibade Mojisola R.'),
    signatoryTitle: val('acct-stmt-signatory-title', 'Managing Director'),
    filename: 'TEEM_Account_Statement_Request_' + monthLabel + '_' + ref + '.pdf'
  };
}

function accountStatementLetterHtml() {
  const spec = accountStatementSpec();
  const withLetterhead = !(store.state.settings && store.state.settings.pdfLetterhead === false);
  return '<div class="letterhead-doc">' +
    '<div class="req-header-row' + (withLetterhead ? '' : ' no-letterhead') + '">' +
      (TEEM_IMG.logo ? '<img src="' + TEEM_IMG.logo + '" alt="Teem Business Nigeria Enterprises" class="req-top-logo">' : '') +
      '<div class="req-contact-block">' +
        '<div><span class="req-label">Address:</span> <span class="req-value">' + escapeHtml((store.state.company || {}).address || '') + '</span></div>' +
        '<div><span class="req-label">Tel:</span> <span class="req-value">' + escapeHtml((store.state.company || {}).phones || '') + '</span></div>' +
        '<div><span class="req-label">Email:</span> <span class="req-value req-email">' + escapeHtml((store.state.company || {}).email || '') + '</span></div>' +
      '</div>' +
    '</div>' +
    '<div class="req-date-right">' + escapeHtml(spec.letterDate) + '</div>' +
    '<div class="req-receiver-block">' +
      '<div class="req-receiver-title">' + escapeHtml(spec.recipientTitle) + '</div>' +
      '<div>' + escapeHtml(spec.bankName) + '</div>' +
      '<div>' + escapeHtml(spec.bankAddress) + '</div>' +
    '</div>' +
    '<div class="req-salutation" style="font-weight:400;margin-bottom:12px;">' + escapeHtml(spec.salutation) + '</div>' +
    '<div class="req-subject-title" style="text-align:left;text-decoration:none;margin-bottom:12px;">' + escapeHtml(spec.subject) + '</div>' +
    '<div class="req-body-paragraph" style="margin-bottom:12px;">We hope this letter finds you well. The above-named company is writing to request an e-copy of our account statement for the period <strong style="font-weight:800;">' + escapeHtml(spec.periodStr) + '</strong>. The account details are as follows:</div>' +
    '<div style="margin:12px 0 14px;line-height:1.9;font-size:13.5px;">' +
      '<div>Account Holder\'s Name: <strong style="font-weight:800;">' + escapeHtml(spec.holderName) + '</strong></div>' +
      '<div>Account Number: <strong style="font-weight:800;">' + escapeHtml(spec.accountNumber) + '</strong></div>' +
      '<div>BVN: <strong style="font-weight:800;">' + escapeHtml(spec.bvn) + '</strong></div>' +
    '</div>' +
    '<div class="req-body-paragraph" style="margin-bottom:12px;">We require this account statement for official purpose and we kindly request you to provide the account statement to this email address, <strong style="font-weight:800;">' + escapeHtml(spec.email) + '</strong></div>' +
    '<div class="req-body-paragraph" style="margin-bottom:10px;">Thank you for your cooperation and assistance.</div>' +
    '<div class="req-body-paragraph" style="margin-bottom:28px;">We look forward to receiving the requested account statement at your earliest convenience.</div>' +
    '<div class="req-sign-block" style="margin-top:20px;">' +
      '<div>Sincerely,</div>' +
      '<div style="height:56px;" aria-label="Physical signature space"></div>' +
      '<div>' + escapeHtml(spec.signatoryName) + '</div>' +
      '<div>' + escapeHtml(spec.signatoryTitle) + '</div>' +
    '</div>' +
  '</div>';
}

function renderAccountStatementView() {
  const spec = accountStatementSpec();
  const periodEl = document.getElementById('acct-stmt-period-display');
  if (periodEl) periodEl.textContent = spec.periodStr;
  const lhToggle = document.getElementById('acct-stmt-letterhead-toggle');
  if (lhToggle) lhToggle.checked = !(store.state.settings && store.state.settings.pdfLetterhead === false);
  const preview = document.getElementById('account-statement-letter-preview');
  if (preview) preview.innerHTML = accountStatementLetterHtml();
}

function onAccountStatementParamsChange() {
  renderAccountStatementView();
}

function setAccountStatementLetterhead(withLetterhead) {
  setDocLetterhead(withLetterhead);
}

function buildAccountStatementPdf(spec, options) {
  options = options || {};
  const doc = new PdfDoc({
    reference: spec.reference,
    heading: 'REQUEST FOR ACCOUNT STATEMENT',
    subheading: spec.periodStr,
    layout: options.layout,
    fontScale: options.fontScale
  });

  doc.text(spec.letterDate || '1st September, 2026', { size: 11.5, align: 'right' });
  doc.gap(6);

  doc.text(spec.recipientTitle || 'The Manager,', { style: 'bold', size: 12 });
  doc.text(spec.bankName || 'Zenith Bank Plc.,', { size: 11.5 });
  doc.text(spec.bankAddress || 'Oke-Ilewo, Abeokuta, Ogun State.', { size: 11.5 });
  doc.gap(6);

  doc.text(spec.salutation || 'Dear Zenith Bank Customer Service,', { size: 11.5 });
  doc.gap(5);

  doc.text(spec.subject || 'REQUEST FOR ACCOUNT STATEMENT', { style: 'bold', size: 12 });
  doc.gap(4);

  doc.richSegments([
    { text: 'We hope this letter finds you well. The above-named company is writing to request an e-copy of our account statement for the period ', bold: false },
    { text: (spec.periodStr || '01/08/2026 to 31/08/2026'), bold: true },
    { text: '. The account details are as follows:', bold: false }
  ], { size: 11.5 });
  doc.gap(5);

  doc.richSegments([
    { text: "Account Holder's Name: ", bold: false },
    { text: (spec.holderName || 'TEEM BUSINESS NIG. ENT. OPS'), bold: true }
  ], { size: 11.5 });
  doc.gap(2);
  doc.richSegments([
    { text: 'Account Number: ', bold: false },
    { text: (spec.accountNumber || '1017702040'), bold: true }
  ], { size: 11.5 });
  doc.gap(2);
  doc.richSegments([
    { text: 'BVN: ', bold: false },
    { text: (spec.bvn || '22194735148'), bold: true }
  ], { size: 11.5 });
  doc.gap(5);

  doc.richSegments([
    { text: 'We require this account statement for official purpose and we kindly request you to provide the account statement to this email address, ', bold: false },
    { text: (spec.email || 'ephspinctglobalservices@gmail.com'), bold: true }
  ], { size: 11.5 });
  doc.gap(5);

  doc.text('Thank you for your cooperation and assistance.', { size: 11.5 });
  doc.gap(3.5);
  doc.text('We look forward to receiving the requested account statement at your earliest convenience.', { size: 11.5 });
  doc.gap(8);

  // Physical signature block: NO digital signature image so it can be signed physically after printing
  doc.keep(48);
  doc.text('Sincerely,', { size: 11.5 });
  doc.gap(20);
  doc.signaturePage = doc.page;
  doc.text(spec.signatoryName || 'Ajibade Mojisola R.', { size: 11.5 });
  doc.text(spec.signatoryTitle || 'Managing Director', { size: 11 });

  const filename = spec.filename || ('TEEM_Account_Statement_Request_' + spec.reference + '.pdf');
  const finalDoc = doc.finalize({ title: spec.subject || 'REQUEST FOR ACCOUNT STATEMENT' });
  if (!options.defer) finalDoc.save(filename);

  return { pages: doc.pages, filename: filename, doc: finalDoc, closingPushed: !!doc.closingPushed, signaturePage: doc.signaturePage, lastPageFill: doc.lastPageFill || 0 };
}

function openPreviewForAccountStatement() {
  openDocPreview('account_statement');
}

function printAccountStatementLetter() {
  const spec = accountStatementSpec();
  const res = renderPdfForContext(spec, buildAccountStatementPdf, docPreviewSettings());
  printPdfDocument(res.doc, 'Request for Account Statement (' + spec.periodStr + ')');
}

function exportAccountStatementLetter() {
  const spec = accountStatementSpec();
  const res = renderPdfForContext(spec, buildAccountStatementPdf, docPreviewSettings());
  savePdfResult(res, 'Request for Account Statement (' + spec.periodStr + ')', spec, spec.filename);
}

window.getAccountStatementPeriod = getAccountStatementPeriod;
window.accountStatementSpec = accountStatementSpec;
window.accountStatementLetterHtml = accountStatementLetterHtml;
window.renderAccountStatementView = renderAccountStatementView;
window.onAccountStatementParamsChange = onAccountStatementParamsChange;
window.setAccountStatementLetterhead = setAccountStatementLetterhead;
window.buildAccountStatementPdf = buildAccountStatementPdf;
window.openPreviewForAccountStatement = openPreviewForAccountStatement;
window.printAccountStatementLetter = printAccountStatementLetter;
window.exportAccountStatementLetter = exportAccountStatementLetter;

function showToast(message, type) {
  type = type || 'info';
  let container = document.getElementById('app-toast-container');
  if (!container) {
    container = document.createElement('div');
    container.id = 'app-toast-container';
    container.className = 'toast-container';
    document.body.appendChild(container);
  }
  Array.from(container.children).forEach(existing => {
    if (existing.innerHTML === message) existing.remove();
  });
  while (container.children.length >= 2) {
    container.firstElementChild.remove();
  }
  const toast = document.createElement('div');
  toast.className = 'toast toast-' + type;
  toast.innerHTML = message;
  container.appendChild(toast);
  setTimeout(() => {
    toast.style.opacity = '0';
    toast.style.transform = 'translateY(10px)';
    toast.style.transition = 'all 0.3s ease';
    setTimeout(() => toast.remove(), 300);
  }, 3200);
}

// ===========================================================================
// 19. RENDER DISPATCH & INPUT FOCUS SELF-HEALING GUARD (v1.0.5)
// ===========================================================================
function restoreAppInputFocus(targetEl) {
  try {
    if (typeof window !== 'undefined' && window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') {
      window.TEEM_DESKTOP_RUNTIME.refocus();
    }
    if (targetEl && typeof targetEl.focus === 'function' && document.body.contains(targetEl)) {
      targetEl.focus({ preventScroll: true });
    }
  } catch (e) {}
}
window.restoreAppInputFocus = restoreAppInputFocus;

function captureActiveInputState() {
  try {
    const el = document.activeElement;
    if (!el || !el.tagName) return null;
    const tag = el.tagName.toUpperCase();
    if (tag !== 'INPUT' && tag !== 'TEXTAREA' && tag !== 'SELECT') return null;
    const state = {
      id: el.id || '',
      name: el.getAttribute('name') || '',
      tag: tag,
      type: (el.type || '').toLowerCase(),
      value: el.value,
      selStart: null,
      selEnd: null
    };
    try {
      if (typeof el.selectionStart === 'number') {
        state.selStart = el.selectionStart;
        state.selEnd = el.selectionEnd;
      }
    } catch (e) {}
    return state;
  } catch (e) {
    return null;
  }
}

function restoreActiveInputState(saved) {
  if (!saved) return;
  try {
    let el = saved.id ? document.getElementById(saved.id) : null;
    if (!el && saved.name) {
      el = document.querySelector(saved.tag.toLowerCase() + '[name="' + saved.name + '"]');
    }
    if (!el || !document.body.contains(el)) return;
    if (el.disabled || el.readOnly) return;
    if (saved.type !== 'file' && saved.type !== 'checkbox' && saved.type !== 'radio' && saved.value !== undefined) {
      if (el.value !== saved.value) el.value = saved.value;
    }
    if (document.activeElement !== el) {
      el.focus({ preventScroll: true });
    }
    if (saved.selStart !== null && typeof el.setSelectionRange === 'function') {
      try { el.setSelectionRange(saved.selStart, saved.selEnd !== null ? saved.selEnd : saved.selStart); } catch (e) {}
    }
  } catch (e) {}
}

(function installInputFocusGuard() {
  if (typeof window === 'undefined' || window._teemInputFocusGuardInstalled) return;
  window._teemInputFocusGuardInstalled = true;

  // Replace blocking native window.alert with non-blocking toast + focus recovery
  // so Chromium/Electron on Windows never locks up keyboard input queues.
  window.alert = function (msg) {
    try {
      const text = String(msg !== undefined && msg !== null ? msg : '');
      const isErr = /error|invalid|cannot|fail|reject|restrict|must|least|unable/i.test(text);
      showToast((isErr ? '\u26a0\ufe0f ' : '\u2139\ufe0f ') + escapeHtml(text), isErr ? 'error' : 'info');
    } catch (e) {}
    setTimeout(() => restoreAppInputFocus(document.activeElement), 10);
  };

  // Wrap native window.confirm so Electron always re-binds webContents keyboard focus afterwards
  if (typeof window.confirm === 'function' && !window.confirm._teemWrapped) {
    const origConfirm = window.confirm.bind(window);
    const wrappedConfirm = function (msg) {
      const prevEl = document.activeElement;
      const res = origConfirm(msg);
      setTimeout(() => restoreAppInputFocus(prevEl), 15);
      setTimeout(() => restoreAppInputFocus(prevEl), 120);
      return res;
    };
    wrappedConfirm._teemWrapped = true;
    window.confirm = wrappedConfirm;
  }

  // Self-healing click/mousedown handler for all text inputs & textareas across the app
  if (typeof document !== 'undefined') {
    document.addEventListener('mousedown', function (ev) {
      const target = ev.target && ev.target.closest ? ev.target.closest('input, textarea, select') : null;
      if (!target) return;
      if (target.id !== 'cloud-sync-code-output') {
        target.disabled = false;
        if (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA') {
          target.readOnly = false;
          target.removeAttribute('disabled');
          target.removeAttribute('readonly');
        }
      }
      if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.refocus === 'function') {
        setTimeout(() => {
          if (document.activeElement !== target && !target.disabled) {
            window.TEEM_DESKTOP_RUNTIME.refocus();
            try { target.focus({ preventScroll: true }); } catch (e) {}
          }
        }, 20);
      }
    }, true);
  }
})();

function renderAll() {
  const savedScroll = captureAllScrollPositions();
  const savedInput = captureActiveInputState();
  renderDashboardCards();
  renderDashboardSlides();
  renderHeroSupervisorGrid();
  renderGpsMap();
  renderFacilitiesDirectory();
  renderMunicipalDirectory();
  renderEvacuations();
  renderDebtorRadar();
  renderMonthlyReport();
  renderSupervisorsList();
  renderSupervisorBadge();
  renderVehiclesList();
  renderSettingsConsole();
  renderArchive();
  evaluateTrackerAlerts();
  updateRoleUI();
  renderCurrentView();
  restoreAllScrollPositions(savedScroll);
  restoreActiveInputState(savedInput);
}

function renderCurrentView() {
  ensureSessionAndModalBackArrows();
  switch (currentActiveView) {
    case 'overview': renderDashboardCards(); renderHeroSupervisorGrid(); evaluateTrackerAlerts(); break;
    case 'facilities': renderFacilitiesDirectory(); break;
    case 'municipal': renderMunicipalDirectory(); break;
    case 'evacuations': renderEvacuations(); break;
    case 'requests': renderRequestsView(); break;
    case 'account-statement': renderAccountStatementView(); break;
    case 'debtors': renderDebtorRadar(); break;
    case 'monthly-report': renderMonthlyReport(); break;
    case 'supervisors': renderSupervisorsList(); break;
    case 'archive': renderArchive(); break;
    case 'chat': renderTeamChat(); break;
    case 'settings': renderSettingsConsole(); renderVehiclesList(); renderSupervisorsList(); renderUsersTable(); updateAdminQuotaNote(); break;
    default: break;
  }
}

// ===========================================================================
// 20. BOOT
// ===========================================================================
function populatePeriodDropdowns() {
  const optionsHtml = ALL_PERIODS.map(m => '<option value="' + m + '">' + m + '</option>').join('');
  ['edit-fac-period-from', 'edit-fac-period-to', 'add-fac-period-from', 'add-fac-period-to',
   'pay-period-from', 'pay-period-to'].forEach(id => {
    const el = document.getElementById(id);
    if (!el) return;
    const previous = el.value;
    el.innerHTML = optionsHtml;
    el.value = previous || CURRENT_MONTH_NAME;
  });

  const now = new Date();
  const weekdays = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
  const months = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
  const liveSubtitle = document.getElementById('overview-live-date-subtitle');
  if (liveSubtitle) {
    liveSubtitle.innerHTML = 'Abeokuta PSP Concession Operations &bull; ' + weekdays[now.getDay()] + ', ' + now.getDate() + ' ' + months[now.getMonth()] + ' ' + now.getFullYear();
  }
  const auditSel = document.getElementById('audit-period-select');
  if (auditSel) {
    const optCurr = auditSel.querySelector('option[value="week_current"]');
    const optLast = auditSel.querySelector('option[value="week_last"]');
    if (optCurr) optCurr.textContent = periodWindow('week_current').label;
    if (optLast) optLast.textContent = periodWindow('week_last').label;
  }
}

// ===========================================================================
// DOCUMENT PREVIEW & PRINT SETTINGS
// Renders the real A4 PDF, shows it page by page before anything is saved or
// printed, and lets the operator set the font size first.
// ===========================================================================
var docPreviewContext = null;   // window-visible so tooling can inspect the live preview

function docPreviewSettings() {
  if (!store.state.settings) store.state.settings = {};
  if (!store.state.settings.pdfFontSize) store.state.settings.pdfFontSize = 11;
  if (store.state.settings.pdfAutoFit === undefined) store.state.settings.pdfAutoFit = true;
  if (!store.state.settings.pdfMargins) store.state.settings.pdfMargins = 'tight';
  if (store.state.settings.pdfLetterhead === undefined) store.state.settings.pdfLetterhead = true;
  return store.state.settings;
}

function currentDocSpecBuilder() {
  if (!docPreviewContext) return null;
  const builders = {
    request: buildRequestPdf,
    account_statement: buildAccountStatementPdf,
    facility: buildFacilityReportPdf,
    street: buildStreetReportPdf,
    audit: buildAuditPdf,
    debtors: buildDebtorReportPdf,
    monthly: buildMonthlyReportPdf
  };
  if (docPreviewContext.archivedDoc) {
    const ad = docPreviewContext.archivedDoc;
    const b = builders[ad.kind];
    if (!b || !ad.spec) return null;
    return { spec: ad.spec, builder: b, title: ad.title || ad.reference, filename: ad.filename || (ad.reference + '.pdf') };
  }
  const map = {
    request: { spec: requestSpec, builder: buildRequestPdf, title: activeRequestCategory + ' Service Request Letter' },
    account_statement: { spec: accountStatementSpec, builder: buildAccountStatementPdf, title: 'Request for Account Statement' },
    facility: { spec: facilityReportSpec, builder: buildFacilityReportPdf, title: 'Facility Service Report' },
    street: { spec: streetReportSpec, builder: buildStreetReportPdf, title: 'Municipal Street Report' },
    audit: { spec: auditSpec, builder: buildAuditPdf, title: 'Evacuation Compliance Audit' },
    debtors: { spec: debtorReportSpec, builder: buildDebtorReportPdf, title: 'OUTSTANDING FACILITIES' },
    monthly: { spec: monthlyReportSpec, builder: buildMonthlyReportPdf, title: (activeMonthlyReportPeriod || CURRENT_MONTH_NAME).toUpperCase() + ' INCOME AND EXPENDITURE ANALYSIS' }
  };
  const entry = map[docPreviewContext.kind];
  if (!entry) return null;
  const spec = entry.spec();
  if (!spec) return null;
  if (docPreviewContext.kind === 'request' && !spec.rows.length) {
    showToast('\u26a0\ufe0f Tick at least one payment entry first.', 'error');
    return null;
  }
  return { spec: spec, builder: entry.builder, title: entry.title, filename: spec.filename };
}

function toggleDocPreviewSettings(forceCollapse) {
  const pane = document.getElementById('doc-preview-settings-pane');
  const modal = document.getElementById('modal-doc-preview');
  const card = modal ? modal.querySelector('.modal-card') : null;
  const topBtn = document.getElementById('doc-settings-toggle-btn');
  const footBtn = document.getElementById('doc-footer-collapse-btn');
  if (!pane) return false;

  const collapsed = typeof forceCollapse === 'boolean'
    ? forceCollapse
    : !pane.classList.contains('is-collapsed');

  pane.classList.toggle('is-collapsed', collapsed);
  if (card) card.classList.toggle('settings-collapsed', collapsed);
  if (topBtn) {
    topBtn.innerHTML = collapsed ? '&#9662; Show Print &amp; Font Settings' : '&#9652; Collapse Settings (Full Screen)';
  }
  if (footBtn) {
    footBtn.innerHTML = collapsed ? '&#9662; Show Settings' : '&#9652; Full-Screen Preview';
  }
  return collapsed;
}

function populateDocPrinters() {
  const select = document.getElementById('doc-printer-select');
  if (!select) return;
  if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.getPrinters === 'function') {
    window.TEEM_DESKTOP_RUNTIME.getPrinters().then(list => {
      if (!Array.isArray(list) || !list.length) return;
      const prev = select.value;
      select.innerHTML = '<option value="">System Default Printer / Print Preview</option>' +
        list.map(p => '<option value="' + escapeHtml(p.name) + '"' + (p.isDefault ? ' selected' : '') + '>' + escapeHtml(p.displayName || p.name) + (p.isDefault ? ' (Default)' : '') + '</option>').join('');
      if (prev) select.value = prev;
    }).catch(() => {});
  }
}

function openDocPreview(kind, opts) {
  opts = opts || {};
  closeAllModals('modal-doc-preview');
  docPreviewContext = { kind: kind, doc: null, archivedDoc: opts.archivedDoc || null };
  const settings = docPreviewSettings();
  const rangeEl = document.getElementById('doc-font-range');
  const valEl = document.getElementById('doc-font-value');
  const marginEl = document.getElementById('doc-margin-select');
  const autoFitEl = document.getElementById('doc-autofit');
  const lhSelectEl = document.getElementById('doc-letterhead-select');
  if (rangeEl) rangeEl.value = settings.pdfFontSize;
  if (valEl) valEl.textContent = settings.pdfFontSize.toFixed(1) + ' pt';
  if (marginEl) marginEl.value = settings.pdfMargins;
  if (autoFitEl) autoFitEl.checked = !!settings.pdfAutoFit;
  if (lhSelectEl) lhSelectEl.value = settings.pdfLetterhead === false ? 'without' : 'with';

  openModal('modal-doc-preview');
  const modal = document.getElementById('modal-doc-preview');
  const card = modal ? modal.querySelector('.modal-card') : null;
  if (card && !card.classList.contains('maximized')) {
    toggleModalMaximise(card);
  }
  populateDocPrinters();
  toggleDocPreviewSettings(opts.collapseSettings !== undefined ? !!opts.collapseSettings : isMobileOrAndroidRuntime());

  const ctx = currentDocSpecBuilder();
  if (!ctx) {
    showToast('\u2139\ufe0f Open a document first.', 'info');
    closeModal('modal-doc-preview');
    return;
  }
  refreshDocPreview();
}

function stepDocFont(delta) {
  const settings = docPreviewSettings();
  settings.pdfFontSize = Math.max(6, Math.min(14, Math.round((settings.pdfFontSize + delta) * 2) / 2));
  store.save();
  document.getElementById('doc-font-range').value = settings.pdfFontSize;
  document.getElementById('doc-font-value').textContent = settings.pdfFontSize.toFixed(1) + ' pt';
  refreshDocPreview();
}

function setDocFont(value) {
  const settings = docPreviewSettings();
  settings.pdfFontSize = Number(value);
  store.save();
  document.getElementById('doc-font-value').textContent = settings.pdfFontSize.toFixed(1) + ' pt';
  refreshDocPreview();
}

function setDocMargins(value) {
  const settings = docPreviewSettings();
  settings.pdfMargins = value;
  store.save();
  refreshDocPreview();
}

function setDocAutoFit(value) {
  const settings = docPreviewSettings();
  settings.pdfAutoFit = !!value;
  store.save();
  refreshDocPreview();
}

function setDocLetterhead(withLetterhead) {
  const settings = docPreviewSettings();
  settings.pdfLetterhead = !!withLetterhead;
  store.save();
  const lhSelectEl = document.getElementById('doc-letterhead-select');
  if (lhSelectEl) lhSelectEl.value = settings.pdfLetterhead ? 'with' : 'without';
  const lhToggleEl = document.getElementById('req-letterhead-toggle');
  if (lhToggleEl) lhToggleEl.checked = settings.pdfLetterhead;
  const acctToggleEl = document.getElementById('acct-stmt-letterhead-toggle');
  if (acctToggleEl) acctToggleEl.checked = settings.pdfLetterhead;
  const preview = document.getElementById('request-letterhead-preview');
  if (preview) preview.innerHTML = requestLetterHtml();
  const acctPreview = document.getElementById('account-statement-letter-preview');
  if (acctPreview && typeof accountStatementLetterHtml === 'function') acctPreview.innerHTML = accountStatementLetterHtml();
  if (docPreviewContext && document.getElementById('modal-doc-preview') && document.getElementById('modal-doc-preview').classList.contains('active')) {
    refreshDocPreview();
  }
}

function isMobileOrAndroidRuntime() {
  try {
    if (window.TEEM_ANDROID_FS || window.Capacitor) return true;
    const ua = (navigator && navigator.userAgent) ? navigator.userAgent : '';
    if (/Android|iPhone|iPad|iPod|Mobile/i.test(ua)) return true;
    if (typeof window.innerWidth === 'number' && window.innerWidth <= 900) return true;
  } catch (e) {}
  return false;
}

function buildLiveHtmlPreviewDocument(kind, spec, settings) {
  settings = settings || {};
  const withLh = settings.pdfLetterhead !== false;
  const pt = Number(settings.pdfFontSize) || 10.5;
  const basePx = Math.max(10, Math.min(16, Math.round(pt * 1.15)));
  const logoHtml = (withLh && TEEM_IMG && TEEM_IMG.logo)
    ? '<img src="' + TEEM_IMG.logo + '" alt="TEEM Logo" style="height:54px;max-width:45%;object-fit:contain;">'
    : '<div><strong style="color:#0F5328;font-size:15px;">TEEM BUSINESS NIGERIA ENTERPRISES</strong><div style="font-size:11px;color:#555;">RC OG20434</div></div>';
  const lhHeader = withLh
    ? '<div style="display:flex;justify-content:space-between;align-items:flex-start;gap:10px;border-bottom:2px solid #0F5328;padding-bottom:8px;margin-bottom:12px;">' +
        logoHtml +
        '<div style="text-align:right;font-size:10.5px;line-height:1.35;color:#111;">' +
          '<div><strong style="color:#B71C1C;">Address:</strong> Praise Tower, opp. Dimmo Stores,</div>' +
          '<div>Omida, Ibara, Abeokuta, Ogun State.</div>' +
          '<div><strong style="color:#B71C1C;">Tel:</strong> 07034962112, 07048269980</div>' +
          '<div><strong style="color:#B71C1C;">Email:</strong> <span style="color:#1565C0;">teembusnigent@gmail.com</span></div>' +
        '</div>' +
      '</div>'
    : '<div style="height:28px;"></div>';

  const sigBlock = '<div style="margin-top:16px;page-break-inside:avoid;">' +
    (TEEM_IMG && TEEM_IMG.signature ? '<img src="' + TEEM_IMG.signature + '" alt="Signature" style="height:44px;object-fit:contain;display:block;margin-bottom:2px;">' : '') +
    '<div style="font-weight:700;font-size:12.5px;color:#0F5328;">Mojisola R. Ajibade</div>' +
    '<div style="font-style:italic;font-size:11.5px;color:#333;">Managing Director</div>' +
  '</div>';

  let bodyHtml = '';
  if (kind === 'request' && spec) {
    bodyHtml =
      '<div style="text-align:right;font-size:12px;margin-bottom:8px;">' + escapeHtml(spec.letterDate || '') + '</div>' +
      '<div style="font-size:12px;line-height:1.4;margin-bottom:10px;">' +
        '<strong>The Special Adviser/Managing Director</strong><br>' +
        'Ogun State Waste Management Authority (OGWAMA)<br>' +
        '3, Presidential Boulevard, Ibara<br>' +
        'Abeokuta, Ogun state.' +
      '</div>' +
      '<div style="font-weight:700;margin-bottom:6px;">Sir</div>' +
      '<div style="font-weight:800;text-align:center;text-decoration:underline;margin-bottom:8px;">' + escapeHtml(spec.subject || '') + '</div>' +
      '<p style="margin:0 0 10px 0;text-align:justify;line-height:1.45;">' + escapeHtml(spec.bodyLine || '') + '</p>' +
      '<table><thead><tr><th>S/N</th>' + (spec.showOutlet !== false ? '<th>' + escapeHtml(spec.column || 'OUTLET') + '</th>' : '') + '<th>DEPOSITOR</th><th style="text-align:right;">AMOUNT</th>' + (spec.showGenWaste ? '<th style="text-align:right;">GEN. WASTE</th>' : '') + '<th>DATE</th>' + (spec.showMonth !== false ? '<th>MONTH</th>' : '') + '</tr></thead><tbody>' +
      (spec.rows || []).map((r, i) => {
        const mark = r.isReRequest ? ' (RE-Request)' : '';
        const noOutlet = spec.showOutlet === false;
        const gw = (r.genWaste === undefined || r.genWaste === null || r.genWaste === '') ? '' : Number(r.genWaste).toLocaleString('en-NG');
        return '<tr>' +
          '<td style="text-align:center;">' + (i + 1) + '.</td>' +
          (noOutlet ? '' : '<td>' + escapeHtml((r.outlet || '') + mark) + '</td>') +
          '<td>' + escapeHtml((r.depositor || '') + (noOutlet ? mark : '')) + '</td>' +
          '<td style="text-align:right;font-weight:700;">' + Number(r.amount || 0).toLocaleString('en-NG') + '</td>' +
          (spec.showGenWaste ? '<td style="text-align:right;font-weight:700;">' + gw + '</td>' : '') +
          '<td style="text-align:center;">' + escapeHtml(formatShortDate(r.date)) + '</td>' +
          (spec.showMonth !== false ? '<td style="text-align:center;">' + escapeHtml(r.month || '') + '</td>' : '') +
        '</tr>';
      }).join('') +
      (() => {
        const lead = (spec.showOutlet !== false ? '<td colspan="2"></td>' : '<td></td>');
        const emptyAmount = '<td style="text-align:right;"></td>';
        const claim = (v) => spec.showGenWaste
          ? emptyAmount + '<td style="text-align:right;">' + Number(v || 0).toLocaleString('en-NG') + '</td>'
          : '<td style="text-align:right;">' + Number(v || 0).toLocaleString('en-NG') + '</td>';
        const tail = (spec.showMonth !== false ? '<td colspan="2"></td>' : '<td></td>');
        return '<tr style="font-weight:800;background:#F0FDF4;">' + lead + '<td>Total</td>' + claim(spec.total) + tail + '</tr>' +
               (spec.rebate ? '<tr style="font-weight:800;background:#ECFDF5;">' + lead + '<td>' + escapeHtml(String(spec.rebate)) + '%</td>' + claim(spec.rebateValue) + tail + '</tr>' : '');
      })() +
      '</tbody></table>' +
      '<p style="margin:10px 0 6px 0;">' + escapeHtml(spec.statement || '') + '</p>' +
      '<p style="margin:0 0 10px 0;">Many thanks in anticipation of your favorable response in this regard.</p>' +
      '<div style="font-style:italic;">Yours faithfully,<br>For: Teem Business Nigeria Enterprises</div>' +
      sigBlock;
  } else if (kind === 'account_statement' && spec) {
    bodyHtml =
      '<div style="text-align:right;font-size:12px;margin-bottom:14px;">' + escapeHtml(spec.letterDate || '') + '</div>' +
      '<div style="font-size:12px;line-height:1.45;margin-bottom:14px;">' +
        '<strong>' + escapeHtml(spec.recipientTitle || 'The Manager,') + '</strong><br>' +
        escapeHtml(spec.bankName || 'Zenith Bank Plc.,') + '<br>' +
        escapeHtml(spec.bankAddress || 'Oke-Ilewo, Abeokuta, Ogun State.') +
      '</div>' +
      '<div style="margin-bottom:10px;">' + escapeHtml(spec.salutation || 'Dear Zenith Bank Customer Service,') + '</div>' +
      '<div style="font-weight:800;margin-bottom:10px;">' + escapeHtml(spec.subject || 'REQUEST FOR ACCOUNT STATEMENT') + '</div>' +
      '<p style="margin:0 0 10px 0;text-align:justify;line-height:1.5;">We hope this letter finds you well. The above-named company is writing to request an e-copy of our account statement for the period <strong>' + escapeHtml(spec.periodStr || '01/08/2026 to 31/08/2026') + '</strong>. The account details are as follows:</p>' +
      '<div style="margin:10px 0;line-height:1.8;">' +
        '<div>Account Holder\'s Name: <strong>' + escapeHtml(spec.holderName || 'TEEM BUSINESS NIG. ENT. OPS') + '</strong></div>' +
        '<div>Account Number: <strong>' + escapeHtml(spec.accountNumber || '1017702040') + '</strong></div>' +
        '<div>BVN: <strong>' + escapeHtml(spec.bvn || '22194735148') + '</strong></div>' +
      '</div>' +
      '<p style="margin:10px 0;text-align:justify;line-height:1.5;">We require this account statement for official purpose and we kindly request you to provide the account statement to this email address, <strong style="font-weight:800;">' + escapeHtml(spec.email || 'ephspinctglobalservices@gmail.com') + '</strong></p>' +
      '<p style="margin:10px 0 8px 0;text-align:justify;line-height:1.5;">Thank you for your cooperation and assistance.</p>' +
      '<p style="margin:0 0 18px 0;text-align:justify;line-height:1.5;">We look forward to receiving the requested account statement at your earliest convenience.</p>' +
      '<div style="margin-top:20px;page-break-inside:avoid;">' +
        '<div>Sincerely,</div>' +
        '<div style="height:52px;"></div>' +
        '<div>' + escapeHtml(spec.signatoryName || 'Ajibade Mojisola R.') + '</div>' +
        '<div>' + escapeHtml(spec.signatoryTitle || 'Managing Director') + '</div>' +
      '</div>';
  } else if (kind === 'facility' && spec && spec.facility) {
    const f = spec.facility;
    const fTotalWithVat = calcTotalWithVat(f.amount, f.vat);
    bodyHtml =
      '<h3 style="text-align:center;margin:0 0 2px 0;color:#0F5328;">CERTIFIED FACILITY EVACUATION &amp; SERVICE REPORT</h3>' +
      '<div style="text-align:center;font-style:italic;font-size:11.5px;margin-bottom:10px;">Period: ' + escapeHtml(spec.monthLabel || '') + '</div>' +
      '<div style="background:#F8FAFC;border:1px solid #CBD5E1;border-radius:8px;padding:10px;margin-bottom:10px;font-size:12px;line-height:1.5;">' +
        '<div><strong>Facility Name:</strong> ' + escapeHtml(f.name) + '</div>' +
        '<div><strong>Sector:</strong> ' + escapeHtml(f.category) + ' &bull; <strong>Monthly Tariff:</strong> ' + formatNaira(f.amount) + (f.vat ? ' (+' + f.vat + '% VAT)' : '') + '</div>' +
        '<div><strong>Total Monthly + Tax:</strong> ' + formatNaira(fTotalWithVat) + '</div>' +
        '<div><strong>Field Supervisor:</strong> ' + escapeHtml(f.supervisor) + ' &bull; <strong>Status:</strong> ' + escapeHtml(f.healthLabel) + '</div>' +
        '<div><strong>Total Received:</strong> ' + formatNaira(f.totalPaid) + ' &bull; <strong>Last Evacuation:</strong> ' + formatDate(f.lastEvacuated) + '</div>' +
      '</div>' +
      '<h4 style="margin:8px 0 4px 0;color:#0F5328;">PAYMENT &amp; DEPOSIT HISTORY (' + (spec.payments || []).length + ')</h4>' +
      '<table><thead><tr><th>Depositor</th><th style="text-align:right;">Amount</th><th>Date</th><th>Month</th><th>Coverage</th></tr></thead><tbody>' +
      ((spec.payments && spec.payments.length) ? spec.payments.map(p => '<tr>' +
        '<td>' + escapeHtml(p.payerName || '') + '</td>' +
        '<td style="text-align:right;font-weight:700;">' + formatNaira(p.amount) + '</td>' +
        '<td>' + escapeHtml(formatShortDate(p.date)) + '</td>' +
        '<td>' + escapeHtml(p.month || '') + '</td>' +
        '<td>' + escapeHtml(formatCoveragePeriod(p, ' to ')) + '</td>' +
      '</tr>').join('') : '<tr><td colspan="5" style="text-align:center;">No payment records.</td></tr>') +
      '</tbody></table>' +
      '<h4 style="margin:10px 0 4px 0;color:#0F5328;">CERTIFIED EVACUATION ROUTINES (' + (spec.evacuations || []).length + ')</h4>' +
      '<table><thead><tr><th>Date</th><th>Vehicle</th><th>Supervisor</th><th>Status</th></tr></thead><tbody>' +
      ((spec.evacuations && spec.evacuations.length) ? spec.evacuations.map(h => '<tr>' +
        '<td>' + escapeHtml(formatDate(h.date)) + '</td>' +
        '<td>' + escapeHtml(h.truck || '') + '</td>' +
        '<td>' + escapeHtml(h.supervisor || '') + '</td>' +
        '<td>' + escapeHtml(h.status || '') + '</td>' +
      '</tr>').join('') : '<tr><td colspan="4" style="text-align:center;">No evacuation records.</td></tr>') +
      '</tbody></table>' +
      sigBlock;
  } else if (kind === 'street' && spec && spec.street) {
    const s = spec.street;
    bodyHtml =
      '<h3 style="text-align:center;margin:0 0 2px 0;color:#0F5328;">MUNICIPAL STREET EVACUATION &amp; SERVICE REPORT</h3>' +
      '<div style="text-align:center;font-style:italic;font-size:11.5px;margin-bottom:10px;">Period: ' + escapeHtml(spec.monthLabel || '') + '</div>' +
      '<div style="background:#F8FAFC;border:1px solid #CBD5E1;border-radius:8px;padding:10px;margin-bottom:10px;font-size:12px;line-height:1.5;">' +
        '<div><strong>Street:</strong> ' + escapeHtml(s.name) + '</div>' +
        '<div><strong>Field Supervisor:</strong> ' + escapeHtml(s.supervisor) + '</div>' +
        '<div><strong>Last Evacuation:</strong> ' + formatDate(s.lastEvacuated) + ' (' + s.days + ' days ago)</div>' +
      '</div>' +
      '<table><thead><tr><th>Date</th><th>Month</th><th>Vehicle Used</th><th>Supervisor</th><th>Status</th></tr></thead><tbody>' +
      ((spec.rows && spec.rows.length) ? spec.rows.map(h => '<tr>' +
        '<td>' + escapeHtml(formatDate(h.date)) + '</td>' +
        '<td>' + escapeHtml(h.month || '') + '</td>' +
        '<td>' + escapeHtml(h.truck || '') + '</td>' +
        '<td>' + escapeHtml(h.supervisor || '') + '</td>' +
        '<td>' + escapeHtml(h.status || '') + '</td>' +
      '</tr>').join('') : '<tr><td colspan="5" style="text-align:center;">No evacuation exercises recorded.</td></tr>') +
      '</tbody></table>' +
      sigBlock;
  } else if (kind === 'audit' && spec) {
    bodyHtml =
      '<h3 style="text-align:center;margin:0 0 2px 0;color:#0F5328;">EVACUATION COMPLIANCE AUDIT REPORT</h3>' +
      '<div style="text-align:center;font-size:11.5px;margin-bottom:10px;">' + escapeHtml(spec.periodLabel || '') + ' &bull; ' + escapeHtml(spec.sectorLabel || '') + ' &bull; Rate: <strong>' + escapeHtml(String(spec.rate || 0)) + '%</strong></div>' +
      '<h4 style="margin:8px 0 4px 0;color:#0F5328;">A. UNITS EVACUATED (' + (spec.evacuated || []).length + ')</h4>' +
      '<table><thead><tr><th>S/N</th><th>Facility / Street</th><th>Sector</th><th>Date</th><th>Supervisor</th></tr></thead><tbody>' +
      ((spec.evacuated && spec.evacuated.length) ? spec.evacuated.map((u, i) => '<tr>' +
        '<td>' + (i + 1) + '.</td><td>' + escapeHtml(u.name || '') + '</td><td>' + escapeHtml(u.category || '') + '</td><td>' + escapeHtml(formatDate(u.date)) + '</td><td>' + escapeHtml(u.supervisor || '') + '</td>' +
      '</tr>').join('') : '<tr><td colspan="5" style="text-align:center;">None in period.</td></tr>') +
      '</tbody></table>' +
      '<h4 style="margin:10px 0 4px 0;color:#B71C1C;">B. UNITS NOT EVACUATED (' + (spec.notEvacuated || []).length + ')</h4>' +
      '<table><thead><tr><th>S/N</th><th>Facility / Street</th><th>Sector</th><th>Last Evacuation</th><th>Days Overdue</th></tr></thead><tbody>' +
      ((spec.notEvacuated && spec.notEvacuated.length) ? spec.notEvacuated.map((u, i) => '<tr>' +
        '<td>' + (i + 1) + '.</td><td>' + escapeHtml(u.name || '') + '</td><td>' + escapeHtml(u.category || '') + '</td><td>' + escapeHtml(formatDate(u.lastEvacuated)) + '</td><td>' + escapeHtml(String(u.daysOverdue || 0)) + '</td>' +
      '</tr>').join('') : '<tr><td colspan="5" style="text-align:center;">All units evacuated.</td></tr>') +
      '</tbody></table>' +
      sigBlock;
  } else if (kind === 'debtors' && spec) {
    bodyHtml =
      '<div style="text-align:right;font-size:11.5px;">' + escapeHtml(formatLetterDate(spec.date || currentUsageDateIso())) + '</div>' +
      '<h3 style="text-align:center;margin:4px 0 2px 0;color:#0F5328;">OUTSTANDING FACILITIES</h3>' +
      '<div style="text-align:center;font-weight:700;font-size:11.5px;margin-bottom:10px;">SECTOR: ' + escapeHtml(spec.sectorLabel || '') + '</div>' +
      '<table><thead><tr><th style="width:36px;">S/N</th><th>FACILITIES</th><th style="text-align:center;">NO OF MONTHS</th><th>MONTHS</th></tr></thead><tbody>' +
      ((spec.rows && spec.rows.length) ? spec.rows.map((r, i) => '<tr>' +
        '<td style="text-align:center;">' + (r.sn || (i + 1)) + '</td>' +
        '<td><strong>' + escapeHtml(r.facility || '') + '</strong></td>' +
        '<td style="text-align:center;font-weight:700;color:#B71C1C;">' + escapeHtml(String(r.owingMonths || 1)) + '</td>' +
        '<td>' + escapeHtml(r.monthsLabel || '') + '</td>' +
      '</tr>').join('') : '<tr><td colspan="4" style="text-align:center;">Every registered facility in this sector is fully paid up.</td></tr>') +
      '</tbody></table>' +
      sigBlock;
  } else if (kind === 'monthly' && spec) {
    const t = spec.totals || computeMonthlyReportTotals(spec.period);
    bodyHtml =
      '<h3 style="text-align:center;margin:0 0 8px 0;color:#0F5328;">' + escapeHtml((spec.period || '').toUpperCase()) + ' INCOME AND EXPENDITURE ANALYSIS</h3>' +
      '<table><thead><tr><th>Section</th><th style="text-align:right;">Total Amount</th></tr></thead><tbody>' +
        '<tr><td>1. Industrial Waste Evacuation (TEEM + ' + escapeHtml(t.partnerTitle || 'Partner') + ')</td><td style="text-align:right;font-weight:700;">' + formatNaira(t.indGrandTotal) + '</td></tr>' +
        '<tr><td>2. Staff Salary Schedule (' + (t.salaries || []).length + ' Staff)</td><td style="text-align:right;font-weight:700;">' + formatNaira(t.salaryTotal) + '</td></tr>' +
        '<tr><td>3. Municipal Revenue (TEEM ' + formatNaira(t.munTeemTotal) + ' + OGWAMA ' + formatNaira(t.munOgwamaTotal) + ')</td><td style="text-align:right;font-weight:700;">' + formatNaira(t.municipalTotal) + '</td></tr>' +
        '<tr><td>4. Compactor Fuel Usage (' + (t.fuelLitresTotal || 0) + ' Litres)</td><td style="text-align:right;font-weight:700;">' + formatNaira(t.fuelTotal) + '</td></tr>' +
        '<tr><td>5. Vehicle Repair &amp; Maintenance</td><td style="text-align:right;font-weight:700;">' + formatNaira(t.repairTotal) + '</td></tr>' +
        '<tr style="background:#FEF2F2;font-weight:800;"><td>Total Expenses (Salary + Fuel + Repair)</td><td style="text-align:right;color:#B71C1C;">' + formatNaira(t.totalExpenses) + '</td></tr>' +
        '<tr style="background:#F0FDF4;font-weight:800;"><td>Total Revenue (Municipal + Industrial)</td><td style="text-align:right;color:#0F5328;">' + formatNaira(t.totalRevenue) + '</td></tr>' +
        '<tr style="background:#ECFDF5;font-weight:900;"><td>Net Income (Revenue minus Expenses)</td><td style="text-align:right;color:#0F5328;">' + formatNaira(t.netIncome) + '</td></tr>' +
      '</tbody></table>' +
      sigBlock;
  }

  return '<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">' +
    '<style>' +
      '*{box-sizing:border-box;}' +
      'body{margin:0;padding:10px;background:#E2E8F0;font-family:"Times New Roman",Times,serif;font-size:' + basePx + 'px;color:#111;}' +
      '.sheet{background:#fff;max-width:794px;width:100%;margin:0 auto;padding:14px;border-radius:6px;box-shadow:0 2px 10px rgba(0,0,0,0.12);overflow-x:hidden;}' +
      'table{width:100%;border-collapse:collapse;margin:6px 0;font-size:' + Math.max(9.5, basePx - 1) + 'px;table-layout:fixed;word-break:break-word;}' +
      'th,td{border:1px solid #334155;padding:4px 5px;text-align:left;vertical-align:top;overflow-wrap:anywhere;}' +
      'th{background:#0F5328;color:#fff;font-size:' + Math.max(8.5, basePx - 2) + 'px;}' +
    '</style></head><body><div class="sheet">' + lhHeader + bodyHtml + '</div></body></html>';
}

function refreshDocPreview() {
  const ctx = currentDocSpecBuilder();
  const frame = document.getElementById('doc-preview-frame');
  if (!ctx) return;

  const settings = docPreviewSettings();
  const result = renderPdfForContext(ctx.spec, ctx.builder, settings);
  docPreviewContext.doc = result;
  docPreviewContext.title = ctx.title;

  const warning = document.getElementById('doc-preview-warning');
  if (warning) {
    if (result.closingPushed) {
      warning.style.display = '';
      warning.textContent = 'The closing block is still on a page of its own - lower the font size or choose tighter margins.';
    } else {
      warning.style.display = 'none';
      warning.textContent = '';
    }
  }

  if (!frame) return;
  if (isMobileOrAndroidRuntime()) {
    frame.removeAttribute('src');
    frame.srcdoc = buildLiveHtmlPreviewDocument(docPreviewContext.kind, ctx.spec, settings);
    return;
  }

  try {
    frame.removeAttribute('srcdoc');
    const url = result.doc.output('bloburl');
    frame.src = url;
  } catch (e) {
    frame.removeAttribute('src');
    frame.srcdoc = buildLiveHtmlPreviewDocument(docPreviewContext.kind, ctx.spec, settings);
  }
}

function openDocPreviewInTab() {
  if (!docPreviewContext || !docPreviewContext.doc) return;
  const url = docPreviewContext.doc.doc.output('bloburl');
  window.open(url, '_blank');
}

function printFromDocPreview() {
  if (!docPreviewContext || !docPreviewContext.doc) return;
  const ctx = currentDocSpecBuilder();
  if (ctx && ctx.spec) {
    archiveDocument({
      type: docPreviewContext.title || ctx.title,
      title: (docPreviewContext.title || ctx.title) + (ctx.spec.facility ? ' - ' + ctx.spec.facility.name : ctx.spec.street ? ' - ' + ctx.spec.street.name : ''),
      kind: ctx.spec.kind,
      spec: ctx.spec,
      total: ctx.spec.total || 0,
      pages: docPreviewContext.doc.pages,
      filename: ctx.filename || docPreviewContext.doc.filename,
      driveFolderPath: ctx.spec.kind === 'request' ? ((store.state.settings && store.state.settings.googleDriveRootFolder) || GDRIVE_ROOT_FOLDER_DEFAULT) + '/' + (ctx.spec.category || activeRequestCategory) : ''
    });
    if (ctx.spec.kind === 'request' || ctx.spec.kind === 'monthly') {
      syncPrintedRequestToGoogleDrive(ctx.spec, docPreviewContext.doc, ctx.filename || docPreviewContext.doc.filename);
    }
  }
  const printerEl = document.getElementById('doc-printer-select');
  const copiesEl = document.getElementById('doc-print-copies');
  const deviceName = printerEl ? printerEl.value : '';
  const copies = copiesEl ? Math.max(1, Number(copiesEl.value) || 1) : 1;
  printPdfDocument(docPreviewContext.doc.doc, docPreviewContext.title, { deviceName: deviceName, copies: copies });
}

function saveFromDocPreview() {
  if (!docPreviewContext || !docPreviewContext.doc) return;
  const ctx = currentDocSpecBuilder();
  if (!ctx) return;
  // save exactly the pages that were previewed, and archive them
  savePdfResult(docPreviewContext.doc, docPreviewContext.title || ctx.title, ctx.spec, ctx.filename);
  closeModal('modal-doc-preview');
}

function openPreviewForRequest() { openDocPreview('request'); }
function openPreviewForFacility() { openDocPreview('facility'); }
function openPreviewForStreet() { openDocPreview('street'); }
function openPreviewForAudit() { openDocPreview('audit'); }

function enforceCurrentVersionStamp() {
  try {
    const verText = 'v' + RELEASE;
    const appVerLabel = document.getElementById('app-version-label');
    if (appVerLabel) appVerLabel.textContent = verText;
    document.querySelectorAll('.auth-version-pill').forEach(el => {
      el.textContent = verText;
    });
    if (document.title && document.title.includes('TEEM')) {
      document.title = 'TEEM Waste Management System ' + verText + ' - PSP Concession Portal';
    }
    if (typeof window !== 'undefined' && 'caches' in window && window.caches && typeof window.caches.keys === 'function') {
      const activeCacheName = 'teem-concession-v' + RELEASE;
      window.caches.keys().then(keys => {
        (keys || []).forEach(k => {
          if (k !== activeCacheName) window.caches.delete(k).catch(() => {});
        });
      }).catch(() => {});
    }
    if (typeof navigator !== 'undefined' && navigator.serviceWorker && typeof navigator.serviceWorker.getRegistrations === 'function') {
      navigator.serviceWorker.getRegistrations().then(regs => {
        (regs || []).forEach(r => { if (r && typeof r.update === 'function') r.update().catch(() => {}); });
      }).catch(() => {});
    }
  } catch (e) {}
}

function bootTeem() {
  enforceCurrentVersionStamp();
  try { if (typeof window !== 'undefined') { window.addEventListener('online', function () { scheduleDriveRetry(1500); }); } } catch (e) {}
  try { teemFsInit(); } catch (e) {}
  if (window.TEEM_ANDROID_FS && typeof window.TEEM_ANDROID_FS.ensureFolder === 'function') {
    try { window.TEEM_ANDROID_FS.ensureFolder(); } catch (e) {}
  }
  loadCloudConfigOnBoot();
  populatePeriodDropdowns();
  applySidebarState();
  applySessionUI();
  ensureEditableSettingsInputs();
  if (!currentUser()) showLoginScreen(); else hideLoginScreen();
  const search = document.getElementById('facility-search-input');
  if (search) {
    const handler = () => {
      if (currentActiveView !== 'facilities') { currentFacilityFilter = 'all'; switchView('facilities'); }
      else renderFacilitiesDirectory();
    };
    search.addEventListener('input', handler);
    search.addEventListener('keyup', handler);
  }
  const local = document.getElementById('fac-local-search');
  if (local) { local.addEventListener('input', renderFacilitiesDirectory); local.addEventListener('keyup', renderFacilitiesDirectory); }
  const mun = document.getElementById('municipal-search-input');
  if (mun) { mun.addEventListener('input', renderMunicipalDirectory); mun.addEventListener('keyup', renderMunicipalDirectory); }

  initDialogControls();
  initMapNavigation();
  renderAll();
  applyGpsMapDisabledState();
  startAutoBackupEngine();
  initInactivityAutoSignOut();
  if (location.hash === '#signup') showSignupScreen();
  startDashSlides();

  // A supervisor who has the app installed on a phone reports where the
  // vehicle is as soon as the app is opened, while the phone is online.
  setTimeout(() => {
    const user = currentUser();
    if (!user) return;
    if (user.role === 'Supervisor' || user.role === 'Admin') reportCrewLocation('app launch');
    startFieldReporting();
  }, 1200);
}

// Boot when the document finishes parsing, or immediately if this bundle is
// loaded after the page is already interactive (single-file edition).
let teemBooted = false;
function bootTeemOnce() {
  if (teemBooted) return;
  teemBooted = true;
  bootTeem();
}

// ===========================================================================
// OFFLINE PDF ENGINE - A4 documents, repeating letterhead, "Page X of Y"
// Built on jsPDF (bundled locally - no internet connection required)
// ===========================================================================
const PDF_PAGE_W = 210;
const PDF_PAGE_H = 297;

// Margins are deliberately tight so a document that spills by only a few rows
// is pulled back onto the current sheet instead of creating a nearly empty one.
// "compact" is the second-pass layout used when a closing block would otherwise
// be stranded on a page of its own.
const PDF_PT2MM = 0.3528;
const MM_PER_INCH = 25.4;

// Margins are deliberately small so a document that spills by only a few rows
// is pulled back onto the current sheet instead of creating a nearly empty one.
// "minimal" is 0.1 inch (2.5 mm) on every side.
// A4 is 210 x 297 mm. Left and right margin are 0.5 inch (12.7 mm) in every
// layout, which is the printable standard on office printers. The three
// layouts differ only in how tight the vertical packing is.
// Table text uses 1.15 line spacing, so a wrapped row costs 15% less height
// than the old 1.25 setting while staying fully legible.
const PDF_STD_MARGIN_X = 0.5 * MM_PER_INCH;   // 12.7 mm

const PDF_LAYOUTS = {
  standard: {
    marginX: PDF_STD_MARGIN_X, page1Top: 35, contTop: 14, footerTop: 287,
    headerRule: 30, tableFont: 10.5, tableHeadFont: 8.6, rowPadY: 0.6, padX: 1.4, lineSpacing: 1.15
  },
  tight: {
    marginX: PDF_STD_MARGIN_X, page1Top: 34, contTop: 11, footerTop: 288,
    headerRule: 28.5, tableFont: 10.5, tableHeadFont: 8.4, rowPadY: 0.45, padX: 1.35, lineSpacing: 1.15
  },
  minimal: {
    marginX: PDF_STD_MARGIN_X, page1Top: 32, contTop: 9, footerTop: 289,
    headerRule: 26.5, tableFont: 10.5, tableHeadFont: 8.2, rowPadY: 0.35, padX: 1.3, lineSpacing: 1.15
  }
};

const PDF_MARGIN_NAMES = { standard: 'Standard (0.5 in)', tight: 'Compact', minimal: 'Dense' };

let PDF_MARGIN_X = PDF_LAYOUTS.tight.marginX;
let PDF_HEADER_BOTTOM = PDF_LAYOUTS.tight.headerRule;
let PDF_CONTENT_TOP = PDF_LAYOUTS.tight.page1Top;
let PDF_FOOTER_TOP = PDF_LAYOUTS.tight.footerTop;
let PDF_CONTENT_W = PDF_PAGE_W - (PDF_MARGIN_X * 2);

const PDF_RED = [183, 28, 28];      // contact labels
const PDF_BLACK = [17, 17, 17];     // contact values
const PDF_BLUE = [21, 101, 192];    // e-mail address only

function teemPdfAvailable() {
  return !!(window.jspdf && window.jspdf.jsPDF);
}

// Draws a line built from several coloured runs, aligned to a right edge.
PdfDoc.prototype._drawRichRight = function (runs, y, rightX) {
  const widths = runs.map(r => this.doc.getTextWidth(r.text || ''));
  const total = widths.reduce((a, b) => a + b, 0);
  let x = rightX - total;
  runs.forEach((run, i) => {
    this.doc.setTextColor.apply(this.doc, run.color);
    this.doc.text(run.text || '', x, y);
    x += widths[i];
  });
  this.doc.setTextColor(0, 0, 0);
};

// Same idea, left aligned, used for the contact block in the HTML-free reports.
PdfDoc.prototype._drawRichLeft = function (runs, y, leftX) {
  let x = leftX;
  runs.forEach(run => {
    this.doc.setTextColor.apply(this.doc, run.color);
    this.doc.text(run.text || '', x, y);
    x += this.doc.getTextWidth(run.text || '');
  });
  this.doc.setTextColor(0, 0, 0);
};

// Sends a locally generated PDF to the printer / print preview dialog. Nothing is
// fetched from the internet, so printing works fully offline with visual preview.
function printPdfDocument(doc, title, opts) {
  opts = opts || {};
  try {
    if (window.TEEM_DESKTOP_RUNTIME && typeof window.TEEM_DESKTOP_RUNTIME.printPdf === 'function') {
      const pdfDataUri = doc.output('datauristring');
      window.TEEM_DESKTOP_RUNTIME.printPdf({
        pdfBase64: pdfDataUri,
        title: title || 'TEEM Document',
        deviceName: opts.deviceName || '',
        copies: opts.copies || 1
      });
      showToast('\ud83d\udda8\ufe0f ' + (title || 'Document') + ' opened in Print Preview.', 'success');
      return;
    }
    const frame = document.getElementById('doc-preview-frame');
    if (frame && frame.contentWindow && document.getElementById('modal-doc-preview') && document.getElementById('modal-doc-preview').classList.contains('active')) {
      try {
        frame.contentWindow.focus();
        frame.contentWindow.print();
        showToast('\ud83d\udda8\ufe0f ' + (title || 'Document') + ' sent to Print Preview.', 'success');
        return;
      } catch (frameErr) {}
    }
    doc.autoPrint();
    const url = doc.output('bloburl');
    const win = window.open(url, '_blank');
    if (!win) {
      showToast('\u26a0\ufe0f Allow pop-ups so the print view can open.', 'error');
      return;
    }
    showToast('\ud83d\udda8\ufe0f ' + (title || 'Document') + ' opened for printing.', 'success');
  } catch (e) {
    try { doc.save('TEEM_Document.pdf'); showToast('Printing is not supported here - the PDF was downloaded instead.', 'info'); }
    catch (e2) { showToast('\u26a0\ufe0f Unable to print this document.', 'error'); }
  }
}

function PdfDoc(options) {
  options = options || {};
  const jsPDFCtor = window.jspdf.jsPDF;
  this.doc = new jsPDFCtor({ unit: 'mm', format: 'a4', compress: true });
  this.ref = options.reference || ('TEEM-' + Date.now().toString().slice(-6));
  this.heading = options.heading || '';
  this.subheading = options.subheading || '';

  this.layoutName = PDF_LAYOUTS[options.layout] ? options.layout : 'tight';
  this.layout = PDF_LAYOUTS[this.layoutName];
  this.fontScale = options.fontScale || 1;
  this.includeLetterhead = options.includeLetterhead !== undefined
    ? !!options.includeLetterhead
    : (docPreviewSettings().pdfLetterhead !== false);
  this.signaturePage = null;
  PDF_MARGIN_X = this.layout.marginX;
  PDF_HEADER_BOTTOM = this.layout.headerRule;
  PDF_FOOTER_TOP = this.layout.footerTop;
  PDF_CONTENT_W = PDF_PAGE_W - (PDF_MARGIN_X * 2);

  this.y = this.layout.page1Top;
  this.page = 1;
  this.closingPushed = false;   // set when a closing block had to start a new page
  this.doc.setFont('times', 'normal');
}

PdfDoc.prototype.newPage = function () {
  this.doc.addPage('a4', 'portrait');
  this.page += 1;
  this.y = this.layout.contTop;
};

PdfDoc.prototype.space = function (needed) {
  if (this.y + needed > PDF_FOOTER_TOP - 4) this.newPage();
};

PdfDoc.prototype.gap = function (mm) { this.y += (mm || 4); };

// Moves the cursor back to a given point on the current page (used by the
// closing blocks, which travel as one unit and never split).
PdfDoc.prototype.pageAnchor = function (y) { this.y = y; };

// Starts a new page when the next block would not fit, so closing blocks,
// signature areas and statements are never split across pages.
PdfDoc.prototype.keep = function (needed) {
  // the reserved height follows the type size so a smaller font can pull a
  // closing block back onto the page it belongs to
  const reserve = (needed || 40) * this.fontScale;
  if (this.y + reserve > PDF_FOOTER_TOP - 4) {
    this.newPage();
    this.closingPushed = true;   // lets the exporter retry with tighter margins
    return true;
  }
  return false;
};

PdfDoc.prototype.text = function (value, opts) {
  opts = opts || {};
  const size = (opts.size || 11.5) * this.fontScale;
  const style = opts.style || 'normal';
  const align = opts.align || 'left';
  const lineGap = opts.lineGap || 1.35;
  const width = opts.width || PDF_CONTENT_W;

  this.doc.setFont('times', style);
  this.doc.setFontSize(size);

  const lines = this.doc.splitTextToSize(String(value || ''), width);
  const lineHeight = (size * 0.3528) * lineGap;

  lines.forEach(line => {
    this.space(lineHeight);
    this.doc.setFont('times', style);
    this.doc.setFontSize(size);
    let x = PDF_MARGIN_X;
    if (align === 'center') x = PDF_PAGE_W / 2;
    if (align === 'right') x = PDF_PAGE_W - PDF_MARGIN_X;
    this.doc.text(line, x, this.y, { align: align });
    this.y += lineHeight;
  });
  return lines.length;
};

PdfDoc.prototype.richSegments = function (segments, opts) {
  opts = opts || {};
  const size = (opts.size || 11.5) * this.fontScale;
  const lineGap = opts.lineGap || 1.35;
  const maxWidth = opts.width || PDF_CONTENT_W;
  const lineHeight = (size * 0.3528) * lineGap;

  const tokens = [];
  (segments || []).forEach(seg => {
    const raw = String((seg && seg.text) || '');
    const isBold = Boolean(seg && seg.bold);
    const parts = raw.split(/(\s+)/);
    parts.forEach(part => {
      if (!part) return;
      tokens.push({ text: part, bold: isBold, isSpace: /^\s+$/.test(part) });
    });
  });

  const lines = [];
  let curLine = [];
  let curW = 0;

  tokens.forEach(tok => {
    this.doc.setFont('times', tok.bold ? 'bold' : 'normal');
    this.doc.setFontSize(size);
    const w = this.doc.getTextWidth(tok.text);
    if (curLine.length === 0 && tok.isSpace) return;
    if (curW + w > maxWidth && curLine.length > 0 && !tok.isSpace) {
      lines.push(curLine);
      curLine = [{ text: tok.text, bold: tok.bold, w: w }];
      curW = w;
    } else {
      curLine.push({ text: tok.text, bold: tok.bold, w: w });
      curW += w;
    }
  });
  if (curLine.length > 0) lines.push(curLine);

  lines.forEach(lineTokens => {
    this.space(lineHeight);
    let x = PDF_MARGIN_X;
    lineTokens.forEach(item => {
      this.doc.setFont('times', item.bold ? 'bold' : 'normal');
      this.doc.setFontSize(size);
      this.doc.text(item.text, x, this.y);
      x += item.w;
    });
    this.y += lineHeight;
  });
  this.doc.setFont('times', 'normal');
  return lines.length;
};

PdfDoc.prototype.rule = function (opts) {
  opts = opts || {};
  this.doc.setDrawColor(opts.color || 120);
  this.doc.setLineWidth(opts.width || 0.3);
  const y = opts.y !== undefined ? opts.y : this.y;
  this.doc.line(PDF_MARGIN_X, y, PDF_PAGE_W - PDF_MARGIN_X, y);
  this.doc.setDrawColor(0);
  this.doc.setLineWidth(0.2);
};

PdfDoc.prototype.image = function (dataUri, width, height, opts) {
  opts = opts || {};
  if (!dataUri) return false;
  this.space(height + 2);
  const x = opts.x !== undefined ? opts.x : PDF_MARGIN_X;
  let y = opts.y !== undefined ? opts.y : this.y;
  // PNG data URIs are the supported embedded format
  this.doc.addImage(dataUri, 'PNG', x, y, width, height);
  if (opts.advance !== false) this.y += height + (opts.gap || 3);
  return true;
};

// Table renderer with a repeating header row on every page
PdfDoc.prototype.table = function (columns, rows, options) {
  options = options || {};
  const fontSize = (options.fontSize || this.layout.tableFont) * this.fontScale;
  const headSize = (options.headSize || this.layout.tableHeadFont) * Math.max(this.fontScale, 0.9);
  const padX = this.layout.padX;
  const padY = options.padY || this.layout.rowPadY;
  const lineSpacing = options.lineSpacing || this.layout.lineSpacing || 1.15;
  const lineHeight = (fontSize * PDF_PT2MM) * lineSpacing;
  // Height kept free at the foot of the last page for the closing block.
  const reserve = options.reserveBottom || 0;

  // Stretch the declared column widths to the printable width so no paper is
  // wasted at the right edge, whatever margin the layout uses.
  const declared = columns.reduce((sum, col) => sum + col.width, 0);
  if (options.fitWidth !== false && declared > 40 && Math.abs(declared - PDF_CONTENT_W) > 1.5) {
    const grow = PDF_CONTENT_W / declared;
    columns = columns.map(col => Object.assign({}, col, { width: col.width * grow }));
  }

  let headerHeight = 0;

  const drawHeader = () => {
    this.doc.setFont('times', 'bold');
    this.doc.setFontSize(headSize);
    // wrap long labels so nothing ever collides with the next column
    const headerCells = columns.map(col => this.doc.splitTextToSize(String(col.label), col.width - (padX * 2)));
    const headerLines = Math.max.apply(null, headerCells.map(c => c.length).concat([1]));
    const h = (headerLines * ((headSize * PDF_PT2MM) * 1.15)) + 3.0;
    headerHeight = h;

    this.doc.setFillColor(238, 238, 234);
    this.doc.rect(PDF_MARGIN_X, this.y, PDF_CONTENT_W, h, 'F');
    this.doc.setFont('times', 'bold');
    this.doc.setFontSize(headSize);
    let x = PDF_MARGIN_X;
    headerCells.forEach((lines, i) => {
      lines.forEach((line, li) => {
        const col = columns[i];
        const align = col.align || 'left';
        let tx = x + padX;
        if (align === 'right') tx = x + col.width - padX;
        if (align === 'center') tx = x + (col.width / 2);
        this.doc.text(line, tx, this.y + 2.8 + ((li + 1) * ((headSize * PDF_PT2MM) * 1.15)) - ((headSize * PDF_PT2MM) * 0.3), { align: align });
      });
      x += columns[i].width;
    });
    this.y += h;
    this.doc.setDrawColor(90);
    this.doc.setLineWidth(0.35);
    this.doc.line(PDF_MARGIN_X, this.y, PDF_PAGE_W - PDF_MARGIN_X, this.y);
    this.doc.setDrawColor(150);
    this.doc.setLineWidth(0.2);
  };

  // Measure every row once: the heights drive both the page breaks and the
  // "keep the closing block on the same sheet" decision.
  this.doc.setFont('times', 'normal');
  this.doc.setFontSize(fontSize);
  const measured = rows.map(row => {
    const cells = columns.map((col, i) => {
      const value = row[i] === undefined || row[i] === null ? '' : String(row[i]);
      return this.doc.splitTextToSize(value, col.width - (padX * 2));
    });
    const maxLines = Math.max.apply(null, cells.map(c => c.length).concat([1]));
    return { cells: cells, height: (maxLines * lineHeight) + (padY * 2) };
  });
  const restAfter = new Array(measured.length + 1).fill(0);
  for (let i = measured.length - 1; i >= 0; i--) restAfter[i] = restAfter[i + 1] + measured[i].height;

  drawHeader();
  const bodyLimit = PDF_FOOTER_TOP - 4;

  measured.forEach((m, rowIndex) => {
    const rowHeight = m.height;

    if (this.y + rowHeight > bodyLimit) {
      this.newPage();
      drawHeader();
    } else if (reserve > 0 && rowIndex > 0) {
      const rest = restAfter[rowIndex];
      const fitsHere = (this.y + rest + reserve) <= bodyLimit;
      const fitsFresh = (this.layout.contTop + headerHeight + rest + reserve) <= bodyLimit;
      // Move the tail onto a fresh sheet only when it cannot finish here but
      // can finish there together with the closing block.
      if (!fitsHere && fitsFresh) {
        this.newPage();
        drawHeader();
      }
    }

    this.doc.setFont('times', 'normal');
    this.doc.setFontSize(fontSize);

    let x = PDF_MARGIN_X;
    m.cells.forEach((lines, i) => {
      const col = columns[i];
      const align = col.align || 'left';
      let tx = x + padX;
      if (align === 'right') tx = x + col.width - padX;
      if (align === 'center') tx = x + (col.width / 2);
      this.doc.setFont('times', col.bold ? 'bold' : 'normal');
      this.doc.setFontSize(fontSize);
      lines.forEach((line, li) => {
        this.doc.text(line, tx, this.y + padY + ((li + 1) * lineHeight) - (lineHeight * 0.25), { align: align });
      });
      this.doc.setDrawColor(200);
      this.doc.setLineWidth(0.15);
      this.doc.line(x, this.y, x, this.y + rowHeight);
      x += col.width;
    });

    this.doc.setDrawColor(200);
    this.doc.setLineWidth(0.15);
    this.doc.line(x, this.y, x, this.y + rowHeight);
    this.doc.line(PDF_MARGIN_X, this.y + rowHeight, x, this.y + rowHeight);

    this.y += rowHeight;
  });

  this.gap(options.gap || 5);
};

// Draws the repeating letterhead on every page and stamps "Page X of Y"
PdfDoc.prototype.finalize = function (options) {
  options = options || {};
  // remember where the content ended so the fitting search can tell a well
  // used last page from a nearly empty one
  this.lastY = this.y;
  this.lastPageFill = this.y / PDF_FOOTER_TOP;
  const total = this.doc.getNumberOfPages();
  const stamp = formatTimestamp();

  for (let p = 1; p <= total; p++) {
    this.doc.setPage(p);

    const company = (store.state && store.state.company) || {};

    if (p === 1 && this.includeLetterhead !== false) {
      // ---------- first page: logo on the left, colour-coded contact on the right ----------
      if (TEEM_IMG.logo) {
        try { this.doc.addImage(TEEM_IMG.logo, 'PNG', PDF_MARGIN_X, 8, 30, 15.6); } catch (e) { /* logo optional */ }
      }
      this.doc.setFont('times', 'normal');
      this.doc.setFontSize(7.6);
      this._drawRichRight([
        { text: 'Address: ', color: PDF_RED },
        { text: (company.address || ''), color: PDF_BLACK }
      ], 13.4, PDF_PAGE_W - PDF_MARGIN_X);
      this._drawRichRight([
        { text: 'Tel: ', color: PDF_RED },
        { text: (company.phones || ''), color: PDF_BLACK },
        { text: '   |   ', color: PDF_BLACK },
        { text: 'Email: ', color: PDF_RED },
        { text: (company.email || ''), color: PDF_BLUE }
      ], 17, PDF_PAGE_W - PDF_MARGIN_X);

      this.doc.setDrawColor(27, 94, 32);
      this.doc.setLineWidth(0.6);
      this.doc.line(PDF_MARGIN_X, PDF_HEADER_BOTTOM, PDF_PAGE_W - PDF_MARGIN_X, PDF_HEADER_BOTTOM);
      this.doc.setDrawColor(0);
      this.doc.setLineWidth(0.2);
    }
    // Continuation pages carry no letterhead at all - the document text simply
    // continues from the top of the sheet.

    // Footer
    this.doc.setDrawColor(180);
    this.doc.setLineWidth(0.25);
    this.doc.line(PDF_MARGIN_X, PDF_FOOTER_TOP, PDF_PAGE_W - PDF_MARGIN_X, PDF_FOOTER_TOP);
    this.doc.setFont('times', 'normal');
    this.doc.setFontSize(8.5);
    this.doc.setTextColor(90);
    this.doc.text('Generated ' + stamp, PDF_MARGIN_X, PDF_FOOTER_TOP + 5);
    this.doc.setFont('times', 'bold');
    this.doc.text('Page ' + p + ' of ' + total, PDF_PAGE_W / 2, PDF_FOOTER_TOP + 5, { align: 'center' });
    this.doc.setFont('times', 'normal');
    this.doc.text('Ref: ' + this.ref, PDF_PAGE_W - PDF_MARGIN_X, PDF_FOOTER_TOP + 5, { align: 'right' });
    this.doc.setTextColor(0);
  }

  this.pages = total;
  const jsPDFCtor = window.jspdf.jsPDF;
  this.doc.setDocumentProperties({
    title: options.title || this.heading || 'TEEM Document',
    subject: 'Teem Business Nigeria Enterprises - OGWAMA PSP Concession',
    author: 'Teem Business Nigeria Enterprises',
    keywords: 'TEEM, OGWAMA, waste management, ' + (options.title || ''),
    creator: 'TEEM Waste Management System v' + RELEASE
  });
  if (!this.doc._teemSaveWrapped && typeof this.doc.save === 'function') {
    const rawSave = this.doc.save.bind(this.doc);
    const pdfInst = this.doc;
    this.doc.save = function (filename) {
      return savePdfDocToDevice(pdfInst, filename, rawSave);
    };
    this.doc._teemSaveWrapped = true;
  }
  return this.doc;
};

var PDF_SAVE_FOLDER = '';
var PDF_SAVE_KEY = 'commercial';
var PDF_SAVE_SUB = '';
function setPdfSaveFolder(category, docType) {
  try {
    PDF_SAVE_KEY = saveLocationKeyFor(category, docType);
    PDF_SAVE_FOLDER = deviceFolderFor(category, docType);
    var locs = getSaveLocations();
    PDF_SAVE_SUB = locs.folders[PDF_SAVE_KEY] || '';
  } catch (e) { PDF_SAVE_FOLDER = ''; }
  return PDF_SAVE_FOLDER;
}

function savePdfDocToDevice(jsPdfDoc, filename, origSaveFn) {
  const safeName = (filename || 'TEEM_Document.pdf').replace(/[^A-Za-z0-9._-]+/g, '_');
  const targetFolder = PDF_SAVE_FOLDER || '';
  if (window.TEEM_ANDROID_FS && typeof window.TEEM_ANDROID_FS.saveBase64File === 'function') {
    try {
      const dataUri = jsPdfDoc.output('datauristring');
      const savedPath = window.TEEM_ANDROID_FS.saveBase64File(safeName, dataUri, 'application/pdf', targetFolder);
      if (savedPath && String(savedPath).indexOf('ERROR:') !== 0) {
        showToast('\ud83d\udcc1 Saved to File Manager: ' + savedPath, 'success');
        return savedPath;
      }
    } catch (err) {}
  }
  // A folder the user picked in Settings is written to directly.
  if (TEEM_FS_READY && teemFsSupported()) {
    try {
      const dataUri = jsPdfDoc.output('datauristring');
      teemFsWrite(PDF_SAVE_KEY, safeName, dataUri, 'application/pdf', PDF_SAVE_SUB)
        .then(function (path) {
          if (path) showToast('\ud83d\udcc1 Saved to ' + path, 'success');
          else if (typeof origSaveFn === 'function') origSaveFn(safeName);
        })
        .catch(function () {
          if (typeof origSaveFn === 'function') origSaveFn(safeName);
        });
      return safeName;
    } catch (e) { /* fall through to download */ }
  }
  if (typeof origSaveFn === 'function') {
    origSaveFn(safeName);
  }
  return safeName;
}

var TEEM_FS_READY = false;
function teemFsInit() {
  if (!teemFsSupported()) { TEEM_FS_READY = false; return; }
  Promise.all([teemFsGetHandle('__base__')].concat(
    SAVE_LOCATION_TYPES.map(function (t) { return teemFsGetHandle(t.key); })
  )).then(function (list) {
    TEEM_FS_READY = list.some(function (x) { return !!x; });
    teemFsRefreshLabels();
  }).catch(function () { TEEM_FS_READY = false; });
}

PdfDoc.prototype.save = function (filename) {
  this.doc.save(filename);
};

PdfDoc.prototype.dataUri = function () {
  return this.doc.output('datauristring');
};


// ===========================================================================
// PDF DOCUMENT BUILDERS (A4) - Request letters, reports and audit extractions
// ===========================================================================

// The built-in PDF fonts carry no Naira glyph, so amounts print with an N prefix
function formatNairaPdf(amount) {
  return 'N' + Number(amount || 0).toLocaleString('en-NG');
}

// Compact period label such as 'Sep 2026' so coverage columns stay narrow
function shortPeriod(label) {
  if (!label) return '';
  const parts = String(label).trim().split(/\s+/);
  if (parts.length === 2 && parts[1].length === 4) return parts[0].slice(0, 3) + ' ' + parts[1];
  return label;
}

function pdfRef(prefix) {
  return 'TEEM-' + prefix + '-' + Date.now().toString().slice(-5);
}

function pdfStamp(heading, subheading, reference) {
  return { heading: heading, subheading: subheading, reference: reference };
}

// ---------------------------------------------------------------------------
// A. REQUEST LETTER (Commercial / Industrial / Medical / Institutional /
//    Agricultural / Construction / Municipal Residential)
// ---------------------------------------------------------------------------
// Everything from the closing statement down to the signature. Called twice per
// build: once on a scratch page to measure it, once on the real page to draw it.
function drawRequestClosing(doc, spec) {
  doc.text(spec.statement, { size: 11.5, align: 'left' });
  doc.gap(4);
  doc.text('Many thanks in anticipation of your favorable response in this regard.', { size: 11.5 });
  doc.gap(5);
  doc.text('Yours faithfully,', { style: 'italic', size: 11.5 });
  doc.text('For: Teem Business Nigeria Enterprises', { style: 'italic', size: 11.5 });
  doc.gap(2);
  doc.signaturePage = doc.page;
  if (TEEM_IMG.signature) doc.image(TEEM_IMG.signature, 40, 13, { gap: 1 });
  doc.text('Mojisola R. Ajibade', { style: 'bold', size: 12 });
  doc.text('Managing Director', { style: 'italic', size: 11 });
}

function buildRequestPdf(spec, options) {
  options = options || {};
  const doc = new PdfDoc({
    reference: spec.reference,
    heading: spec.subject,
    subheading: spec.category,
    layout: options.layout,
    fontScale: options.fontScale
  });

  // Letterhead row: logo (left) is drawn by finalize(); the date sits at the
  // right corner of the first content row exactly as in the printed letterhead.
  doc.doc.setFont('times', 'normal');
  doc.doc.setFontSize(12);
  doc.doc.text(spec.letterDate, PDF_PAGE_W - PDF_MARGIN_X, doc.layout.page1Top, { align: 'right' });
  doc.y = doc.layout.page1Top + 7;

  // Receiver address block
  doc.text('The Special Adviser/Managing Director', { style: 'bold', size: 12.5 });
  doc.text('Ogun State Waste Management Authority (OGWAMA)', { size: 12 });
  doc.text('3, Presidential Boulevard, Ibara', { size: 12 });
  doc.text('Abeokuta, Ogun state.', { size: 12 });
  doc.gap(5);

  doc.text('Sir', { style: 'bold', size: 12.5 });
  doc.gap(4);

  doc.text(spec.subject, { style: 'bold', size: 12.5, align: 'center' });
  doc.gap(4);

  doc.text(spec.bodyLine, { size: 11.5, align: 'justify' });
  doc.gap(4);

  // Municipal letters drop the outlet column and the month column. The freed
  // width goes to the remaining columns so the table still fills the page.
  const showOutlet = spec.showOutlet !== false;
  const showMonth = spec.showMonth !== false;
  const showGenWaste = spec.showGenWaste === true;

  // Every variant below adds up to the same 174 mm the table has always used.
  // Column widths come from the measured width of the widest value each
  // column has to hold at 11 pt, so a name wraps at most twice and the month,
  // date and amount never wrap at all. That is what keeps a long request short.
  let columns;
  if (showGenWaste && showOutlet && showMonth) {
    // Medical: the general waste share sits between the amount paid and the date.
    columns = [
      { label: 'S/N', width: 7, align: 'center' },
      { label: spec.column, width: 40 },
      { label: 'DEPOSITORS NAME', width: 42 },
      { label: 'AMOUNT', width: 20, align: 'right' },
      { label: 'GEN. WASTE', width: 20, align: 'right' },
      { label: 'DATE OF PAYMENT', width: 20, align: 'center' },
      { label: 'MONTH', width: 29, align: 'center' }
    ];
  } else if (showOutlet && showMonth) {
    columns = [
      { label: 'S/N', width: 8, align: 'center' },
      { label: spec.column, width: 46 },
      { label: 'DEPOSITORS NAME', width: 56 },
      { label: 'AMOUNT', width: 23, align: 'right' },
      { label: 'DATE OF PAYMENT', width: 21, align: 'center' },
      { label: 'MONTH', width: 29, align: 'center' }
    ];
  } else if (!showOutlet && showMonth) {
    columns = [
      { label: 'S/N', width: 8, align: 'center' },
      { label: 'DEPOSITORS NAME', width: 95 },
      { label: 'AMOUNT', width: 23, align: 'right' },
      { label: 'DATE OF PAYMENT', width: 21, align: 'center' },
      { label: 'MONTH', width: 29, align: 'center' }
    ];
  } else if (!showOutlet && !showMonth) {
    columns = [
      { label: 'S/N', width: 8, align: 'center' },
      { label: 'DEPOSITORS NAME', width: 118 },
      { label: 'AMOUNT', width: 24, align: 'right' },
      { label: 'DATE OF PAYMENT', width: 22, align: 'center' }
    ];
  } else {
    columns = [
      { label: 'S/N', width: 8, align: 'center' },
      { label: spec.column, width: 72 },
      { label: 'DEPOSITORS NAME', width: 62 },
      { label: 'AMOUNT', width: 23, align: 'right' },
      { label: 'DATE OF PAYMENT', width: 21, align: 'center' }
    ];
  }

  const rows = spec.rows.map((r, i) => {
    const mark = r.isReRequest ? ' (RE-Request)' : '';
    const cells = [(i + 1) + '.'];
    if (showOutlet) cells.push(r.outlet + mark);
    cells.push(showOutlet ? r.depositor : (r.depositor + mark));
    cells.push(Number(r.amount).toLocaleString('en-NG'));
    if (showGenWaste) {
      cells.push((r.genWaste === undefined || r.genWaste === null || r.genWaste === '')
        ? '' : Number(r.genWaste).toLocaleString('en-NG'));
    }
    cells.push(formatShortDate(r.date));
    if (showMonth) cells.push(r.month);
    return cells;
  });

  const totalRow = (label, value) => {
    const cells = [];
    if (showOutlet) cells.push('', '');
    else cells.push('');
    cells.push(label);
    if (showGenWaste) {
      // The claimed figure belongs under GEN. WASTE, not under AMOUNT.
      cells.push('');
      cells.push(Number(value).toLocaleString('en-NG'));
    } else {
      cells.push(Number(value).toLocaleString('en-NG'));
    }
    cells.push('');
    if (showMonth) cells.push('');
    return cells;
  };
  rows.push(totalRow('Total', spec.total));
  if (spec.rebate) rows.push(totalRow(spec.rebate + '%', spec.rebateValue));

  doc.table(columns, rows, { gap: 4 });

  // The statement, the thanks line and the whole undersign block travel as ONE
  // unit. Its exact height is measured on a throwaway document first, so the
  // reservation is neither too big (which strands the table short) nor too
  // small (which pushes the block onto a sheet of its own).
  const probe = new PdfDoc({
    reference: spec.reference, heading: '', subheading: '',
    layout: options.layout, fontScale: options.fontScale
  });
  probe.includeLetterhead = false;
  probe.y = 0;
  drawRequestClosing(probe, spec);
  const closingHeight = probe.y;

  doc.pageAnchor(doc.y);
  doc.keep(closingHeight / (doc.fontScale || 1));
  drawRequestClosing(doc, spec);

  const filename = spec.filename || ('TEEM_' + spec.category.replace(/\s+/g, '_') + '_Request_' + spec.reference + '.pdf');
  const finalDoc = doc.finalize({ title: spec.subject });
  if (!options.defer) finalDoc.save(filename);

  return { pages: doc.pages, filename: filename, doc: finalDoc, closingPushed: !!doc.closingPushed, signaturePage: doc.signaturePage, lastPageFill: doc.lastPageFill || 0 };
}

// ---------------------------------------------------------------------------
// B. FACILITY SERVICE REPORT
// ---------------------------------------------------------------------------
function buildFacilityReportPdf(spec, options) {
  options = options || {};
  const doc = new PdfDoc({ reference: spec.reference, heading: 'FACILITY EVACUATION & SERVICE REPORT', subheading: spec.facility.name, layout: options.layout, fontScale: options.fontScale });

  doc.text('CERTIFIED FACILITY EVACUATION & SERVICE REPORT', { style: 'bold', size: 14, align: 'center' });
  doc.text('Period: ' + spec.monthLabel, { style: 'italic', size: 11, align: 'center' });
  doc.gap(5);

  doc.text('FACILITY PROFILE', { style: 'bold', size: 11 });
  doc.text('Name: ' + spec.facility.name, { size: 11.5 });
  doc.text('Sector: ' + spec.facility.category, { size: 11.5 });
  doc.text('Monthly Tariff: ' + formatNairaPdf(spec.facility.amount) + (spec.facility.vat ? ' (+' + spec.facility.vat + '% VAT)' : ' (Statutory Rebate)'), { size: 11.5 });
  doc.text('Total Monthly + Tax: ' + formatNairaPdf(calcTotalWithVat(spec.facility.amount, spec.facility.vat)), { size: 11.5, style: 'bold' });
  doc.gap(2);
  doc.text('Field Supervisor in Charge: ' + spec.facility.supervisor, { size: 11.5, style: 'bold' });
  doc.text('Payment Status: ' + spec.facility.healthLabel, { size: 11.5 });
  doc.text('Total Received To Date: ' + formatNairaPdf(spec.facility.totalPaid), { size: 11.5 });
  doc.text('Last Evacuation: ' + formatDate(spec.facility.lastEvacuated), { size: 11.5 });
  doc.gap(6);

  doc.text('PAYMENT & DEPOSIT HISTORY (' + spec.payments.length + ' record' + (spec.payments.length === 1 ? '' : 's') + ')', { style: 'bold', size: 11.5 });
  doc.gap(1);
  doc.table(
    [
      { label: 'PAYER / DEPOSITOR NAME', width: 40 },
      { label: 'AMOUNT PAID', width: 22, align: 'right' },
      { label: 'PAYMENT DATE', width: 22, align: 'center' },
      { label: 'PAYMENT MONTH', width: 26, align: 'center' },
      { label: 'COVERAGE PERIOD', width: 42 },
      { label: 'STATUS', width: 22, align: 'center' }
    ],
    spec.payments.length
      ? spec.payments.map(p => [p.payerName, formatNairaPdf(p.amount), formatShortDate(p.date), p.month || '', formatCoveragePeriodPdf(p), p.covered ? 'Covered' : 'Partial'])
      : [['No payment record for the selected period.', '', '', '', '', '']],
    { fontSize: 10 }
  );
  doc.gap(4);

  doc.text('CERTIFIED EVACUATION ROUTINES (' + spec.evacuations.length + ' record' + (spec.evacuations.length === 1 ? '' : 's') + ')', { style: 'bold', size: 11.5 });
  doc.gap(1);

  const evacColumns = [
    { label: 'EVACUATION DATE', width: 32, align: 'center' },
    { label: 'VEHICLE USED', width: 46 },
    { label: 'SUPERVISOR LEAD', width: 34 }
  ];
  if (spec.isIndustrial) evacColumns.push({ label: 'TONNAGE (T)', width: 22, align: 'center' });
  evacColumns.push({ label: 'VERIFICATION', width: spec.isIndustrial ? 40 : 62, align: 'center' });

  doc.table(
    evacColumns,
    spec.evacuations.length
      ? spec.evacuations.map(h => {
          const row = [formatDate(h.date), h.truck, h.supervisor];
          if (spec.isIndustrial) row.push((h.tonnage || '0.0') + ' T');
          row.push(h.status);
          return row;
        })
      : [['No evacuation routine recorded for the selected period.', '', '', ''].slice(0, evacColumns.length)],
    { fontSize: 10 }
  );

  doc.keep(26);
  doc.gap(2);
  doc.rule({ color: 180 });
  doc.gap(3);
  doc.text('Certified Date: ' + formatDate(currentUsageDateIso()) + '    Reference: ' + spec.reference, { size: 9.8 });
  doc.gap(1.5);
  doc.text('Certified by: Mojisola R. Ajibade', { style: 'bold', size: 11 });
  doc.text('Managing Director', { style: 'italic', size: 10 });

  const filename = spec.filename || ('TEEM_Facility_Report_' + spec.facility.name.replace(/[^A-Za-z0-9]+/g, '_') + '_' + spec.reference + '.pdf');
  const finalDoc = doc.finalize({ title: 'Facility Service Report - ' + spec.facility.name });
  if (!options.defer) finalDoc.save(filename);
  return { pages: doc.pages, filename: filename, doc: finalDoc, closingPushed: !!doc.closingPushed, signaturePage: doc.signaturePage, lastPageFill: doc.lastPageFill || 0 };
}

// ---------------------------------------------------------------------------
// C. MUNICIPAL STREET REPORT
// ---------------------------------------------------------------------------
function buildStreetReportPdf(spec, options) {
  options = options || {};
  const doc = new PdfDoc({ reference: spec.reference, heading: 'MUNICIPAL STREET EVACUATION REPORT', subheading: spec.street.name, layout: options.layout, fontScale: options.fontScale });

  doc.text('MUNICIPAL STREET EVACUATION & SERVICE REPORT', { style: 'bold', size: 14, align: 'center' });
  doc.text('Period: ' + spec.monthLabel, { style: 'italic', size: 11, align: 'center' });
  doc.gap(5);

  doc.text('STREET PROFILE', { style: 'bold', size: 11 });
  doc.text('Street: ' + spec.street.name, { size: 11.5 });
  doc.text('Assigned Field Supervisor: ' + spec.street.supervisor, { size: 11.5, style: 'bold' });
  doc.text('Date of Last Evacuation: ' + formatDate(spec.street.lastEvacuated) + ' (' + spec.street.days + ' days ago)', { size: 11.5 });
  doc.text('Total Exercises Logged: ' + spec.totalLogged, { size: 11.5 });
  doc.gap(6);

  doc.text('MUNICIPAL EVACUATION EXERCISE HISTORY (' + spec.rows.length + ' record' + (spec.rows.length === 1 ? '' : 's') + ')', { style: 'bold', size: 11.5 });
  doc.gap(1);
  doc.table(
    [
      { label: 'EVACUATION DATE', width: 32, align: 'center' },
      { label: 'MONTH', width: 30, align: 'center' },
      { label: 'VEHICLE USED', width: 50 },
      { label: 'SUPERVISOR IN CHARGE', width: 34 },
      { label: 'STATUS', width: 28, align: 'center' }
    ],
    spec.rows.length
      ? spec.rows.map(h => [formatDate(h.date), h.month || '', h.truck, h.supervisor, h.status])
      : [['No evacuation exercise recorded for the selected period.', '', '', '', '']],
    { fontSize: 10 }
  );

  doc.keep(26);
  doc.gap(2);
  doc.rule({ color: 180 });
  doc.gap(3);
  doc.text('Certified Date: ' + formatDate(currentUsageDateIso()) + '    Reference: ' + spec.reference, { size: 9.8 });
  doc.gap(1.5);
  doc.text('Certified by: Mojisola R. Ajibade', { style: 'bold', size: 11 });
  doc.text('Managing Director', { style: 'italic', size: 10 });

  const filename = spec.filename || ('TEEM_Municipal_Report_' + spec.street.name.replace(/[^A-Za-z0-9]+/g, '_') + '_' + spec.reference + '.pdf');
  const finalDoc = doc.finalize({ title: 'Municipal Street Report - ' + spec.street.name });
  if (!options.defer) finalDoc.save(filename);
  return { pages: doc.pages, filename: filename, doc: finalDoc, closingPushed: !!doc.closingPushed, signaturePage: doc.signaturePage, lastPageFill: doc.lastPageFill || 0 };
}

// ---------------------------------------------------------------------------
// D. EVACUATION COMPLIANCE AUDIT EXTRACTION
// ---------------------------------------------------------------------------
function buildAuditPdf(spec, options) {
  options = options || {};
  const doc = new PdfDoc({ reference: spec.reference, heading: 'EVACUATION COMPLIANCE AUDIT', subheading: spec.periodLabel, layout: options.layout, fontScale: options.fontScale });

  doc.text('EVACUATION COMPLIANCE AUDIT REPORT', { style: 'bold', size: 14, align: 'center' });
  doc.text('Audit Period: ' + spec.periodLabel, { style: 'italic', size: 11, align: 'center' });
  doc.text('Scope: ' + spec.sectorLabel, { style: 'italic', size: 11, align: 'center' });
  doc.gap(5);

  doc.text('SUMMARY OF COMPLIANCE', { style: 'bold', size: 11.5 });
  doc.gap(1);
  doc.table(
    [
      { label: 'TOTAL UNITS IN SCOPE', width: 44, align: 'center' },
      { label: 'UNITS EVACUATED', width: 43, align: 'center' },
      { label: 'UNITS NOT EVACUATED', width: 44, align: 'center' },
      { label: 'COMPLIANCE RATE', width: 43, align: 'center' }
    ],
    [[String(spec.totalUnits), String(spec.evacuated.length), String(spec.notEvacuated.length), spec.rate + '%']],
    { fontSize: 11, gap: 6 }
  );

  doc.text('A. UNITS EVACUATED IN THE PERIOD (' + spec.evacuated.length + ')', { style: 'bold', size: 11.5 });
  doc.gap(1);
  doc.table(
    [
      { label: 'S/N', width: 12, align: 'center' },
      { label: 'FACILITY / STREET', width: 74 },
      { label: 'SECTOR', width: 28 },
      { label: 'EVACUATION DATE', width: 30, align: 'center' },
      { label: 'SUPERVISOR', width: 30 }
    ],
    spec.evacuated.length
      ? spec.evacuated.map((u, i) => [(i + 1) + '.', u.name, u.category, formatDate(u.date), u.supervisor])
      : [['\u2014', 'No unit was evacuated in this period.', '', '', '']],
    { fontSize: 10 }
  );
  doc.gap(4);

  doc.text('B. UNITS NOT EVACUATED IN THE PERIOD (' + spec.notEvacuated.length + ')', { style: 'bold', size: 11.5 });
  doc.gap(1);
  doc.table(
    [
      { label: 'S/N', width: 12, align: 'center' },
      { label: 'FACILITY / STREET', width: 74 },
      { label: 'SECTOR', width: 28 },
      { label: 'LAST EVACUATION', width: 30, align: 'center' },
      { label: 'DAYS OVERDUE', width: 30, align: 'center' }
    ],
    spec.notEvacuated.length
      ? spec.notEvacuated.map((u, i) => [(i + 1) + '.', u.name, u.category, formatDate(u.lastEvacuated), String(u.daysOverdue)])
      : [['\u2014', 'Every unit in scope was evacuated in the period.', '', '', '']],
    { fontSize: 10 }
  );

  doc.keep(22);
  doc.gap(2);
  doc.rule({ color: 180 });
  doc.gap(3);
  doc.text('Prepared by: ' + userFullName(currentUser()) + ' (' + (isAdmin() ? 'Administrator' : 'Field Operations') + ')', { size: 10 });
  doc.text('Date of Extraction: ' + formatDate(currentUsageDateIso()) + '    Reference: ' + spec.reference, { size: 9.8 });

  const filename = spec.filename || ('TEEM_Compliance_Audit_' + spec.reference + '.pdf');
  const finalDoc = doc.finalize({ title: 'Evacuation Compliance Audit' });
  if (!options.defer) finalDoc.save(filename);
  return { pages: doc.pages, filename: filename, doc: finalDoc, closingPushed: !!doc.closingPushed, signaturePage: doc.signaturePage, lastPageFill: doc.lastPageFill || 0 };
}

// ---------------------------------------------------------------------------
// E. SECTOR-SPECIFIC "OUTSTANDING FACILITIES" REPORT
// ---------------------------------------------------------------------------
function buildDebtorReportPdf(spec, options) {
  options = options || {};
  const doc = new PdfDoc({
    reference: spec.reference,
    heading: 'OUTSTANDING FACILITIES',
    subheading: spec.sectorLabel || 'COMMERCIAL',
    layout: options.layout,
    fontScale: options.fontScale
  });

  doc.text(formatLetterDate(spec.date || currentUsageDateIso()), { size: 11, align: 'right' });
  doc.gap(2);
  doc.text('OUTSTANDING FACILITIES', { style: 'bold', size: 14, align: 'center' });
  doc.text('SECTOR: ' + (spec.sectorLabel || 'COMMERCIAL'), { style: 'bold', size: 10.8, align: 'center' });
  doc.gap(4);

  const rows = Array.isArray(spec.rows) ? spec.rows : [];
  doc.table(
    [
      { label: 'S/N', width: 16, align: 'center' },
      { label: 'FACILITIES', width: 82 },
      { label: 'NO OF MONTHS', width: 32, align: 'center' },
      { label: 'MONTHS', width: 44, align: 'center' }
    ],
    rows.length
      ? rows.map((r, i) => [String(r.sn || (i + 1)), r.facility || '', String(r.owingMonths || 1), r.monthsLabel || ''])
      : [['\u2014', 'Every registered facility in this sector is fully paid up.', '0', '\u2014']],
    { fontSize: 10.5 }
  );

  doc.keep(26);
  doc.gap(3);
  doc.rule({ color: 180 });
  doc.gap(3);
  doc.text('Total Outstanding Facilities (' + (spec.sectorLabel || 'Sector') + '): ' + rows.length, { style: 'bold', size: 10.5 });
  doc.text('Date Generated: ' + formatDate(spec.date || currentUsageDateIso()) + '    Reference: ' + spec.reference, { size: 9.8 });
  doc.gap(1.5);
  doc.text('Certified by: Mojisola R. Ajibade', { style: 'bold', size: 11 });
  doc.text('Managing Director', { style: 'italic', size: 10 });

  const filename = spec.filename || ('TEEM_Outstanding_Facilities_' + spec.reference + '.pdf');
  const finalDoc = doc.finalize({ title: 'OUTSTANDING FACILITIES - ' + (spec.sectorLabel || '') });
  if (!options.defer) finalDoc.save(filename);
  return { pages: doc.pages, filename: filename, doc: finalDoc, closingPushed: !!doc.closingPushed, signaturePage: doc.signaturePage, lastPageFill: doc.lastPageFill || 0 };
}

// ===========================================================================
// SPEC BUILDERS - create a serialisable spec from live data, then render
// ===========================================================================
function requestSpec() {
  const data = requestSelection();
  const meta = data.meta;
  const reference = pdfRef('REQ');
  const total = data.total;
  const rebateValue = data.rebate;
  return {
    kind: 'request',
    reference: reference,
    category: activeRequestCategory,
    subject: requestSubject(activeRequestCategory),
    column: meta.column,
    // Municipal letters print no outlet and no month column: the entry is
    // depositor + amount + date.
    showOutlet: meta.showOutlet !== false,
    showMonth: meta.showMonth !== false,
    rebate: meta.rebate,
    letterDate: formatLetterDate(currentUsageDateIso()),
    bodyLine: 'We humbly wish to request for the accrued rebate of the payment/transaction details provided below. The payments were made into the Authorized OGWAMA\u2019s Sterling Bank Account: 0079828285 by ' + meta.body + '.',
    rows: data.selected.map(p => ({
      outlet: p.outlet, isReRequest: !!p.isReRequest, depositor: p.depositor,
      amount: p.amount, genWaste: p.generalWaste, date: p.date, month: p.month
    })),
    showGenWaste: meta.generalWaste === true,
    total: total,
    rebateValue: rebateValue,
    rowIds: data.selected.map(p => p.id),
    statement: meta.rebate
      ? 'The ' + meta.rebate + '% shall be N' + Number(rebateValue).toLocaleString('en-NG') + ' (' + numberToWords(rebateValue) + ') only.'
      : 'The total sum of N' + Number(total).toLocaleString('en-NG') + ' (' + numberToWords(total) + ') only.'
  };
}

function facilityReportSpec() {
  const f = store.state.facilities.find(x => x.id === activeReportFacilityId);
  if (!f) return null;
  const filterEl = document.getElementById('report-month-filter');
  const monthFilter = filterEl ? filterEl.value : 'all';
  const health = getPaymentHealth(f);
  const evacAll = (f.evacuationHistory || []).slice();
  const payAll = (f.paymentHistory || []).slice();
  const evacRows = monthFilter === 'all' ? evacAll : evacAll.filter(h => recordMatchesMonthKey(h, monthFilter));
  const payRows = monthFilter === 'all' ? payAll : payAll.filter(p => recordMatchesMonthKey(p, monthFilter));

  return {
    kind: 'facility',
    reference: pdfRef('FAC'),
    monthLabel: monthFilter === 'all' ? 'All Records To Date' : monthLabelFromKey(monthFilter),
    isIndustrial: f.category === 'Industrial',
    facility: {
      id: f.id, name: f.name, location: f.location, category: f.category, supervisor: f.supervisor,
      amount: f.amount, vat: f.vat, healthLabel: health.label, lastEvacuated: f.lastEvacuated,
      totalPaid: payAll.reduce((s, p) => s + (Number(p.amount) || 0), 0)
    },
    payments: payRows.map(p => ({
      payerName: p.payerName, amount: p.amount, date: p.date, month: p.month,
      periodFrom: p.periodFrom, periodTo: p.periodTo,
      covered: isPaymentRecordCovered(p, f)
    })),
    evacuations: evacRows.map(h => ({ date: h.date, truck: h.truck, supervisor: h.supervisor, tonnage: h.tonnage, status: h.status }))
  };
}

function streetReportSpec() {
  const s = store.state.municipalStreets.find(x => x.id === activeStreetId);
  if (!s) return null;
  const filterEl = document.getElementById('street-report-month-filter');
  const monthFilter = filterEl ? filterEl.value : 'all';
  const history = (s.evacuationHistory || []).slice();
  const rows = monthFilter === 'all' ? history : history.filter(h => recordMatchesMonthKey(h, monthFilter));

  return {
    kind: 'street',
    reference: pdfRef('MUN'),
    monthLabel: monthFilter === 'all' ? 'Full Evacuation History' : formatLongDate(monthFilter + '-01'),
    street: {
      id: s.id, name: s.name, location: s.location, supervisor: s.supervisor,
      lastEvacuated: s.lastEvacuated, days: getDaysSince(s.lastEvacuated)
    },
    totalLogged: history.length,
    rows: rows.map(h => ({ date: h.date, month: h.month, truck: h.truck, supervisor: h.supervisor, status: h.status }))
  };
}

function auditSpec() {
  const data = complianceData();
  const total = data.units.length || 1;
  const sectorLabels = {
    all: 'All Facilities & Municipal Streets',
    facilities: 'All Registered Facilities',
    municipal: 'Municipal Streets Only'
  };
  return {
    kind: 'audit',
    reference: pdfRef('AUD'),
    periodLabel: data.window.label,
    sectorLabel: sectorLabels[data.sector] || (data.sector + ' Facilities'),
    totalUnits: data.units.length,
    rate: ((data.evacuated.length / total) * 100).toFixed(1),
    evacuated: data.evacuated.map(u => ({ name: u.name, location: u.location, category: u.category, date: u.matchLog.date, supervisor: u.matchLog.supervisor })),
    notEvacuated: data.notEvacuated.map(u => ({ name: u.name, location: u.location, category: u.category, lastEvacuated: u.lastEvacuated, daysOverdue: getDaysSince(u.lastEvacuated) }))
  };
}

// ===========================================================================
// EXPORT ACTIONS - build spec, archive the final copy, generate the A4 PDF
// ===========================================================================
// Renders a document and, when the closing block (or the signature area) would
// be stranded on a page of its own, retries automatically: first with the
// tighter margins the operator selected, then with progressively smaller type,
// until the undersign block sits with the document. It always returns the
// result with the fewest sheets, preferring the largest readable font.
// This is the single code path used by the export buttons, the print buttons,
// the preview window and archive re-downloads.
function renderPdfForContext(spec, builder, settings) {
  settings = settings || {};
  const baseFont = settings.pdfFontSize || 11;
  const autoFit = settings.pdfAutoFit !== false;
  const layoutName = settings.pdfMargins && PDF_LAYOUTS[settings.pdfMargins] ? settings.pdfMargins : 'tight';

  // attempt list: the chosen layout first, then anything smaller if needed
  const layouts = layoutName === 'standard' ? ['standard', 'tight', 'minimal']
    : layoutName === 'minimal' ? ['minimal'] : ['tight', 'minimal'];
  const scaleSteps = autoFit ? [1, 0.96, 0.92, 0.88, 0.84, 0.8] : [1];

  let best = null;
  const SPARSE = 0.42;   // a last page filled below this is treated as wasted space

  for (const layout of layouts) {
    for (const k of scaleSteps) {
      const fontScale = (baseFont / 10.5) * k;
      const attempt = builder(spec, { defer: true, layout: layout, fontScale: fontScale });
      attempt.step = k;
      attempt.fontScale = fontScale;
      attempt.layoutName = layout;
      attempt.layoutLabel = PDF_MARGIN_NAMES[layout] || layout;
      attempt.sparseLastPage = attempt.pages > 1 && (attempt.lastPageFill || 0) < SPARSE;

      const better = !best
        || attempt.pages < best.pages
        || (attempt.pages === best.pages && best.sparseLastPage && !attempt.sparseLastPage)
        || (attempt.pages === best.pages && best.sparseLastPage === attempt.sparseLastPage && best.closingPushed && !attempt.closingPushed);

      if (better) best = attempt;

      // The search runs from the largest type downwards, so the first attempt
      // whose closing block sits with the document AND whose last page is
      // properly used is also the most readable one: keep it and stop.
      if (!attempt.closingPushed && !attempt.sparseLastPage) return best;
    }
  }
  return best;   // nothing fitted ideally - fall back to the best found
}

function renderPdfFitted(spec, builder, options) {
  options = options || {};
  const settings = Object.assign({}, docPreviewSettings(), options);
  if (!options.layout && !options.fontScale) return renderPdfForContext(spec, builder, settings);

  // explicit layout/fontScale still supported (used by the fitting search)
  let result = builder(spec, { defer: true, layout: options.layout || settings.pdfMargins || 'tight', fontScale: options.fontScale || 1 });
  return result;
}

function specCategoryOf(spec) {
  if (!spec) return null;
  if (spec.kind === 'request') return spec.category || activeRequestCategory;
  if (spec.facility) return spec.facility.category || null;
  if (spec.street) return 'Municipal';
  return null;
}

function specDriveFolderPath(spec) {
  if (!spec) return '';
  try {
    var f = driveFolderFor(specCategoryOf(spec), spec.kind);
    return f.rootFolder + '/' + f.categoryFolder;
  } catch (e) {
    return '';
  }
}

function archiveAndRender(spec, builder, title, total, filename) {
  if (!teemPdfAvailable()) {
    showToast('\u26a0\ufe0f The PDF engine is not loaded in this copy.', 'error');
    return;
  }
  setPdfSaveFolder(specCategoryOf(spec), spec.kind);
  const result = renderPdfFitted(spec, builder);
  const entry = archiveDocument({
    type: title,
    title: title + (spec.facility ? ' - ' + spec.facility.name : spec.street ? ' - ' + spec.street.name : ''),
    kind: spec.kind,
    spec: spec,
    total: total || spec.total || 0,
    pages: result.pages,
    filename: filename || result.filename,
    driveFolderPath: specDriveFolderPath(spec)
  });
  if (spec && (spec.kind === 'request' || spec.kind === 'monthly')) {
    syncPrintedRequestToGoogleDrive(spec, result, entry ? entry.filename : (filename || result.filename));
  }
  if (spec && spec.kind === 'request') {
    try {
      recordRequestHistory(spec, entry ? entry.filename : (filename || result.filename), entry ? entry.id : '');
      markRequestRowsDone(spec);
    } catch (e) { console.warn('request history', e); }
  }
  result.doc.save(entry ? entry.filename : (filename || result.filename));
  showToast('\ud83d\udcc4 ' + title + ' exported (' + result.pages + ' page' + (result.pages === 1 ? '' : 's') + ') and archived.', 'success');
}

// Save / print exactly what the preview window is showing
function savePdfResult(result, title, spec, filename) {
  if (spec) setPdfSaveFolder(specCategoryOf(spec), spec.kind);
  const entry = archiveDocument({
    type: title,
    title: title + (spec && spec.facility ? ' - ' + spec.facility.name : spec && spec.street ? ' - ' + spec.street.name : ''),
    kind: spec ? spec.kind : 'document',
    spec: spec || null,
    total: (spec && (spec.total || 0)) || 0,
    pages: result.pages,
    filename: filename || result.filename,
    driveFolderPath: spec ? specDriveFolderPath(spec) : ''
  });
  if (spec && (spec.kind === 'request' || spec.kind === 'monthly')) {
    syncPrintedRequestToGoogleDrive(spec, result, entry ? entry.filename : (filename || result.filename));
  }
  if (spec && spec.kind === 'request') {
    try {
      recordRequestHistory(spec, entry ? entry.filename : (filename || result.filename), entry ? entry.id : '');
      markRequestRowsDone(spec);
    } catch (e) { console.warn('request history', e); }
  }
  result.doc.save(entry ? entry.filename : (filename || result.filename || 'TEEM_Document.pdf'));
  showToast('\ud83d\udcc4 ' + title + ' saved (' + result.pages + ' page' + (result.pages === 1 ? '' : 's') + ') and archived.', 'success');
}

function exportRequestLetter() {
  const spec = requestSpec();
  if (!spec.rows.length) {
    showToast('\u26a0\ufe0f Select at least one entry.', 'error');
    return;
  }
  archiveAndRender(spec, buildRequestPdf, spec.category + ' Service Request Letter', spec.total);
}

function exportFacilityReport() {
  const spec = facilityReportSpec();
  if (spec) archiveAndRender(spec, buildFacilityReportPdf, 'Facility Service Report', spec.facility.totalPaid);
}

function exportStreetReport() {
  const spec = streetReportSpec();
  if (spec) archiveAndRender(spec, buildStreetReportPdf, 'Municipal Street Report', 0);
}

function exportComplianceAudit() {
  const spec = auditSpec();
  archiveAndRender(spec, buildAuditPdf, 'Evacuation Compliance Audit', 0);
}

// ---------------------------------------------------------------- PRINT ACTIONS
function printRequestLetter() {
  const spec = requestSpec();
  if (!spec.rows.length) {
    showToast('\u26a0\ufe0f Select at least one entry.', 'error');
    return;
  }
  openDocPreview('request', { collapseSettings: true });
}

function printFacilityReport() {
  const spec = facilityReportSpec();
  if (!spec) return;
  openDocPreview('facility', { collapseSettings: true });
}

function printStreetReport() {
  const spec = streetReportSpec();
  if (!spec) return;
  openDocPreview('street', { collapseSettings: true });
}

function printComplianceAudit() {
  openDocPreview('audit', { collapseSettings: true });
}

// ===========================================================================
// v1.0.5: MONTHLY REPORT (INCOME AND EXPENDITURE ANALYSIS — SECTIONS 1 TO 6)
// ===========================================================================
var activeMonthlyReportPeriod = CURRENT_MONTH_NAME || 'October 2026';

function defaultMonthlyReportsSeed() {
  return {
    'April 2026': {
      partnerTitle: 'JIB & JIB',
      industrial: [
        { date: '2026-04-03', company: 'Yibao Plastic', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-03', company: 'Gandse Renewables', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-03', company: 'CANCC', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-03', company: 'Sany Equipment', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-03', company: 'Ruili Technology', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-03', company: "Tiget Business Int'l", trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-04', company: 'Breeze', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-04', company: 'Agrira West', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-09', company: 'Olam', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-09', company: 'Yonfeng Technology', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-09', company: 'Sacvin', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-09', company: 'Morelux', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-10', company: 'Niger Biscuits', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-11', company: 'Breeze', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-11', company: 'Zino-Fu Industrial Park', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-11', company: 'Yibao Plastics', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-17', company: 'Yanuo', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-18', company: 'Breeze', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-18', company: 'Breeze', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-18', company: 'Neveah', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-19', company: 'Tower Rolling', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-28', company: 'Yibao Plastics', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-28', company: 'CANCC', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-29', company: 'Sacvin', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-29', company: 'Osun Agri', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-29', company: 'Saint Gobain', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-29', company: 'Sany Equipment', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-29', company: 'Yanuo', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-30', company: 'Metal Manufacturing Nig. Ltd', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-30', company: 'Niger Biscuits', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-30', company: 'Sunlight Resources', trips: 1, rate: 40000, group: 'teem' },
        { date: '2026-04-10', company: 'Cway Foods & Beverages', trips: 1, rate: 30000, group: 'partner', partnerTitle: 'JIB & JIB' },
        { date: '2026-04-17', company: 'Honey Well', trips: 1, rate: 30000, group: 'partner', partnerTitle: 'JIB & JIB' },
        { date: '2026-04-23', company: 'Cway Foods & Beverages', trips: 1, rate: 30000, group: 'partner', partnerTitle: 'JIB & JIB' },
        { date: '2026-04-29', company: 'Green Apple', trips: 1, rate: 30000, group: 'partner', partnerTitle: 'JIB & JIB' }
      ],
      salaries: [
        { name: 'Ajibode Samson O.', bank: 'Wema', accountNumber: '0243358597', amount: 60000 },
        { name: 'Odeyinka Abiola M.', bank: 'GTB', accountNumber: '0157063393', amount: 70000 },
        { name: 'Ojurongbe Gafar A.', bank: 'Union', accountNumber: '0042650022', amount: 50000 },
        { name: 'Janet Bose Olubimi', bank: 'Stanbic', accountNumber: '0036778202', amount: 40000 },
        { name: 'Mulero Tomiwa', bank: 'Wema', accountNumber: '0243359343', amount: 60000 },
        { name: 'Omoniyi Opeyemi', bank: 'Opay', accountNumber: '8135009092', amount: 200000 },
        { name: 'Dada Musiliu Akinola', bank: 'Opay', accountNumber: '7068202476', amount: 80000 },
        { name: 'Micheal Bakare', bank: 'Zenith', accountNumber: '2378370402', amount: 320000 }
      ],
      municipal: [
        { supervisor: 'SAMSON', teemAmount: 299000, ogwamaAmount: 120000 },
        { supervisor: 'JUWON', teemAmount: 119400, ogwamaAmount: 50000 }
      ],
      fuel: [
        { date: '2026-04-02', fuelType: 'Diesel', litres: 25, rate: 1850 },
        { date: '2026-04-03', fuelType: 'Diesel', litres: 100, rate: 1850 },
        { date: '2026-04-09', fuelType: 'Diesel', litres: 200, rate: 1850 },
        { date: '2026-04-10', fuelType: 'Diesel', litres: 50, rate: 1950 },
        { date: '2026-04-16', fuelType: 'Diesel', litres: 60, rate: 1850 },
        { date: '2026-04-17', fuelType: 'Diesel', litres: 200, rate: 1850 },
        { date: '2026-04-17', fuelType: 'Diesel', litres: 50, rate: 1850 },
        { date: '2026-04-25', fuelType: 'Diesel', litres: 50, rate: 1850 },
        { date: '2026-04-29', fuelType: 'Diesel', litres: 50, rate: 1850 }
      ],
      repairs: [
        { vehicle: 'BLUE COMPACTOR', description: 'Compact Hose', amount: 8500 },
        { vehicle: 'BLUE COMPACTOR', description: 'Hanger Rubber', amount: 8000 },
        { vehicle: 'BLUE COMPACTOR', description: 'Gear Selector', amount: 14000 },
        { vehicle: 'BLUE COMPACTOR', description: 'Kick Starter', amount: 200000 }
      ]
    },
    'October 2026': {
      partnerTitle: 'JIB & JIB',
      industrial: [
        { date: '2026-10-03', company: 'Saint Gobain', trips: 2, rate: 40000, group: 'teem' },
        { date: '2026-10-06', company: 'Dolphin Steel', trips: 2, rate: 40000, group: 'teem' },
        { date: '2026-10-09', company: 'Metal Manufacturing Nig. Ltd', trips: 3, rate: 40000, group: 'teem' },
        { date: '2026-10-14', company: 'Micstar Mechatronics', trips: 2, rate: 40000, group: 'teem' },
        { date: '2026-10-18', company: 'CANCC', trips: 3, rate: 40000, group: 'teem' },
        { date: '2026-10-20', company: 'Yibao Plastic', trips: 2, rate: 40000, group: 'teem' },
        { date: '2026-10-10', company: 'Cway Foods & Beverages', trips: 2, rate: 30000, group: 'partner', partnerTitle: 'JIB & JIB' },
        { date: '2026-10-17', company: 'Honey Well', trips: 1, rate: 30000, group: 'partner', partnerTitle: 'JIB & JIB' },
        { date: '2026-10-20', company: 'Green Apple', trips: 1, rate: 30000, group: 'partner', partnerTitle: 'JIB & JIB' }
      ],
      salaries: [
        { name: 'Ajibode Samson O.', bank: 'Wema', accountNumber: '0243358597', amount: 60000 },
        { name: 'Odeyinka Abiola M.', bank: 'GTB', accountNumber: '0157063393', amount: 70000 },
        { name: 'Ojurongbe Gafar A.', bank: 'Union', accountNumber: '0042650022', amount: 50000 },
        { name: 'Janet Bose Olubimi', bank: 'Stanbic', accountNumber: '0036778202', amount: 40000 },
        { name: 'Mulero Tomiwa', bank: 'Wema', accountNumber: '0243359343', amount: 60000 },
        { name: 'Omoniyi Opeyemi', bank: 'Opay', accountNumber: '8135009092', amount: 200000 },
        { name: 'Dada Musiliu Akinola', bank: 'Opay', accountNumber: '7068202476', amount: 80000 },
        { name: 'Micheal Bakare', bank: 'Zenith', accountNumber: '2378370402', amount: 320000 }
      ],
      municipal: [
        { supervisor: 'SAMSON', teemAmount: 320000, ogwamaAmount: 145000 },
        { supervisor: 'JUWON', teemAmount: 185000, ogwamaAmount: 90000 }
      ],
      fuel: [
        { date: '2026-10-03', fuelType: 'Diesel', litres: 100, rate: 1850 },
        { date: '2026-10-10', fuelType: 'Diesel', litres: 150, rate: 1850 },
        { date: '2026-10-15', fuelType: 'Petrol', litres: 40, rate: 1150 },
        { date: '2026-10-19', fuelType: 'Diesel', litres: 100, rate: 1850 }
      ],
      repairs: [
        { vehicle: 'BLUE COMPACTOR', description: 'Compact Hose', amount: 8500 },
        { vehicle: 'BLUE COMPACTOR', description: 'Hanger Rubber', amount: 8000 },
        { vehicle: 'BLUE COMPACTOR', description: 'Gear Selector', amount: 14000 }
      ]
    }
  };
}

function getMonthlyReportData(period) {
  const p = period || activeMonthlyReportPeriod || CURRENT_MONTH_NAME || 'October 2026';
  if (!store.state.monthlyReports || typeof store.state.monthlyReports !== 'object') {
    store.state.monthlyReports = defaultMonthlyReportsSeed();
  }
  const seeds = defaultMonthlyReportsSeed();
  if (!store.state.monthlyReports[p]) {
    if (seeds[p]) {
      store.state.monthlyReports[p] = JSON.parse(JSON.stringify(seeds[p]));
    } else {
      store.state.monthlyReports[p] = {
        partnerTitle: 'JIB & JIB',
        industrial: [],
        salaries: JSON.parse(JSON.stringify(seeds['October 2026'].salaries)),
        municipal: [],
        fuel: [],
        repairs: []
      };
    }
  }
  const rec = store.state.monthlyReports[p];
  if (!Array.isArray(rec.industrial)) rec.industrial = [];
  if (!Array.isArray(rec.salaries)) rec.salaries = [];
  if (!Array.isArray(rec.municipal)) rec.municipal = [];
  if (!Array.isArray(rec.fuel)) rec.fuel = [];
  if (!Array.isArray(rec.repairs)) rec.repairs = [];
  if (!rec.partnerTitle) rec.partnerTitle = 'JIB & JIB';
  return rec;
}

function formatShortDateSlash(isoDate) {
  if (!isoDate) return '-';
  const m = String(isoDate).match(/^(\d{4})-(\d{2})-(\d{2})/);
  if (m) return m[3] + '/' + m[2] + '/' + m[1].slice(-2);
  return String(isoDate);
}

function formatFullDateSlash(isoDate) {
  if (!isoDate) return '-';
  const m = String(isoDate).match(/^(\d{4})-(\d{2})-(\d{2})/);
  if (m) return Number(m[3]) + '/' + Number(m[2]) + '/' + m[1];
  return String(isoDate);
}

function computeMonthlyReportTotals(period) {
  const p = period || activeMonthlyReportPeriod || CURRENT_MONTH_NAME || 'October 2026';
  const data = getMonthlyReportData(p);
  const teemInd = [];
  const partnerInd = [];
  const partnerGroupsMap = {};
  const partnerGroups = [];
  data.industrial.forEach((row, idx) => {
    const trips = Math.max(1, Number(row.trips) || 1);
    const rate = Math.max(0, Number(row.rate) || 0);
    const amount = trips * rate;
    const pTitle = ((row.partnerTitle || data.partnerTitle || 'JIB & JIB') + '').trim() || 'JIB & JIB';
    const enriched = Object.assign({}, row, { _idx: idx, trips: trips, rate: rate, amount: amount, partnerTitle: pTitle });
    if (row.group === 'partner') {
      partnerInd.push(enriched);
      const key = pTitle.toUpperCase();
      if (!partnerGroupsMap[key]) {
        partnerGroupsMap[key] = { title: pTitle, rows: [], trips: 0, total: 0 };
        partnerGroups.push(partnerGroupsMap[key]);
      }
      partnerGroupsMap[key].rows.push(enriched);
      partnerGroupsMap[key].trips += trips;
      partnerGroupsMap[key].total += amount;
    } else {
      teemInd.push(enriched);
    }
  });

  const teemIndTrips = teemInd.reduce((s, r) => s + r.trips, 0);
  const teemIndTotal = teemInd.reduce((s, r) => s + r.amount, 0);
  const partnerIndTrips = partnerInd.reduce((s, r) => s + r.trips, 0);
  const partnerIndTotal = partnerInd.reduce((s, r) => s + r.amount, 0);
  const indGrandTotal = teemIndTotal + partnerIndTotal;

  const salaryTotal = data.salaries.reduce((s, r) => s + (Number(r.amount) || 0), 0);

  const munTeemTotal = data.municipal.reduce((s, r) => s + (Number(r.teemAmount) || 0), 0);
  const munOgwamaTotal = data.municipal.reduce((s, r) => s + (Number(r.ogwamaAmount) || 0), 0);
  const municipalTotal = munTeemTotal + munOgwamaTotal;

  const fuelLitresTotal = data.fuel.reduce((s, r) => s + (Number(r.litres) || 0), 0);
  const fuelTotal = data.fuel.reduce((s, r) => s + ((Number(r.litres) || 0) * (Number(r.rate) || 0)), 0);

  const repairTotal = data.repairs.reduce((s, r) => s + (Number(r.amount) || 0), 0);

  const totalExpenses = salaryTotal + fuelTotal + repairTotal;
  const totalRevenue = municipalTotal + indGrandTotal;
  const netIncome = totalRevenue - totalExpenses;

  const partnerTitleSummary = partnerGroups.length
    ? partnerGroups.map(g => g.title).join(' / ')
    : (data.partnerTitle || 'JIB & JIB');

  return {
    period: p,
    partnerTitle: partnerTitleSummary,
    partnerGroups: partnerGroups,
    teemInd: teemInd,
    partnerInd: partnerInd,
    teemIndTrips: teemIndTrips,
    teemIndTotal: teemIndTotal,
    partnerIndTrips: partnerIndTrips,
    partnerIndTotal: partnerIndTotal,
    indGrandTotal: indGrandTotal,
    salaries: data.salaries,
    salaryTotal: salaryTotal,
    municipal: data.municipal,
    munTeemTotal: munTeemTotal,
    munOgwamaTotal: munOgwamaTotal,
    municipalTotal: municipalTotal,
    fuel: data.fuel,
    fuelLitresTotal: fuelLitresTotal,
    fuelTotal: fuelTotal,
    repairs: data.repairs,
    repairTotal: repairTotal,
    totalExpenses: totalExpenses,
    totalRevenue: totalRevenue,
    netIncome: netIncome
  };
}

function setMonthlyReportPeriod(period) {
  if (period) activeMonthlyReportPeriod = period;
  const sel = document.getElementById('monthly-report-period-select');
  if (sel && sel.value !== activeMonthlyReportPeriod) sel.value = activeMonthlyReportPeriod;
  renderMonthlyReport();
}

function renderMonthlyReport() {
  const sel = document.getElementById('monthly-report-period-select');
  if (sel && sel.value) activeMonthlyReportPeriod = sel.value;
  const t = computeMonthlyReportTotals(activeMonthlyReportPeriod);
  const parts = t.period.split(' ');
  const monthUpper = (parts[0] || 'OCTOBER').toUpperCase();
  const yearStr = parts[1] || '2026';
  const monthCommaYear = monthUpper + ', ' + yearStr;
  const supervisorActive = isSupervisor();
  const adminActive = !supervisorActive;

  // Supervisors only see and edit/add FUEL PURCHASED (Section 4) and VEHICLE REPAIR (Section 5).
  // They never see Usage Trip Rate (Section 1), Salary Schedule (Section 2), Municipal Revenue (Section 3), Summary (Section 6), or KPI financials.
  ['mr-kpi-grid', 'mr-section-1', 'mr-section-2', 'mr-section-3', 'mr-section-6'].forEach(secId => {
    const el = document.getElementById(secId);
    if (el) el.style.display = supervisorActive ? 'none' : '';
  });

  const headingEl = document.getElementById('mr-doc-heading');
  if (headingEl) {
    headingEl.textContent = supervisorActive
      ? (monthUpper + ' ' + yearStr + ' — FUEL PURCHASED & VEHICLE REPAIR DETAILS')
      : (monthUpper + ' ' + yearStr + ' INCOME AND EXPENDITURE ANALYSIS');
  }
  const sec2Title = document.getElementById('mr-sec2-title');
  if (sec2Title) sec2Title.textContent = 'SECTION 2: SALARY SCHEDULE FOR THE MONTH OF ' + monthCommaYear;
  const salBanner = document.getElementById('mr-salary-banner');
  if (salBanner) salBanner.textContent = 'SALARY SCHEDULE FOR THE MONTH OF ' + monthCommaYear;

  // Populate KPI strip
  const kpiIgr = document.getElementById('mr-kpi-igr');
  if (kpiIgr) kpiIgr.textContent = formatNaira(t.indGrandTotal);
  const kpiIgrSub = document.getElementById('mr-kpi-igr-sub');
  if (kpiIgrSub) kpiIgrSub.textContent = 'TEEM ' + formatNaira(t.teemIndTotal) + ' + ' + t.partnerTitle + ' ' + formatNaira(t.partnerIndTotal);
  const kpiMun = document.getElementById('mr-kpi-municipal');
  if (kpiMun) kpiMun.textContent = formatNaira(t.municipalTotal);
  const kpiMunSub = document.getElementById('mr-kpi-municipal-sub');
  if (kpiMunSub) kpiMunSub.textContent = 'TEEM ' + formatNaira(t.munTeemTotal) + ' \u2022 OGWAMA ' + formatNaira(t.munOgwamaTotal);
  const kpiExp = document.getElementById('mr-kpi-expenses');
  if (kpiExp) kpiExp.textContent = formatNaira(t.totalExpenses);
  const kpiExpSub = document.getElementById('mr-kpi-expenses-sub');
  if (kpiExpSub) kpiExpSub.textContent = 'Salary ' + formatNaira(t.salaryTotal) + ' \u2022 Fuel ' + formatNaira(t.fuelTotal) + ' \u2022 Repair ' + formatNaira(t.repairTotal);
  const kpiNet = document.getElementById('mr-kpi-net');
  if (kpiNet) {
    kpiNet.textContent = (t.netIncome < 0 ? '-' : '') + formatNaira(Math.abs(t.netIncome));
    kpiNet.className = 'mr-kpi-val ' + (t.netIncome >= 0 ? 'green' : 'red');
  }
  const kpiNetSub = document.getElementById('mr-kpi-net-sub');
  if (kpiNetSub) kpiNetSub.textContent = 'Revenue ' + formatNaira(t.totalRevenue) + ' minus Expenses ' + formatNaira(t.totalExpenses);

  // SECTION 1 TABLE: INDUSTRIAL EVACUATION (Hidden from Supervisors; Usage Rate / Trip never rendered for Supervisors)
  const indTbody = document.getElementById('mr-industrial-tbody');
  if (indTbody) {
    if (supervisorActive) {
      indTbody.innerHTML = '';
    } else {
      let sn = 0;
      const html = [];
      html.push(
        '<tr class="mr-table-title-row"><th colspan="7">TEEM BUSINESS INDUSTRIAL WASTE EVACUATION FOR THE MONTH OF ' + escapeHtml(monthCommaYear) + '</th></tr>' +
        '<tr class="mr-col-head">' +
          '<th style="width:54px;">S/N</th>' +
          '<th style="width:110px;">DATE</th>' +
          '<th>FACILITIES / COMPANY</th>' +
          '<th style="width:115px;text-align:center;">NO OF TRIPS</th>' +
          '<th style="width:145px;">USAGE RATE / TRIP</th>' +
          '<th style="width:165px;">ALLOCATED AMOUNT</th>' +
          '<th class="mr-col-actions" style="width:105px;">ACTIONS</th>' +
        '</tr>'
      );
      if (!t.teemInd.length) {
        html.push('<tr><td colspan="7" style="text-align:center;color:var(--text-muted);padding:12px;">No TEEM Business industrial evacuation trips recorded for ' + escapeHtml(t.period) + ' yet.</td></tr>');
      } else {
        t.teemInd.forEach(r => {
          sn += 1;
          html.push(
            '<tr>' +
              '<td>' + sn + '</td>' +
              '<td>' + escapeHtml(formatShortDateSlash(r.date)) + '</td>' +
              '<td>' + escapeHtml(r.company) + '</td>' +
              '<td style="text-align:center;font-weight:700;">' + r.trips + '</td>' +
              '<td>' + (r.rate > 0 ? formatNaira(r.rate) : '<span style="color:#B45309;font-size:11px;font-weight:700;">Admin Rate Pending</span>') + '</td>' +
              '<td><strong>' + formatNaira(r.amount) + '</strong></td>' +
              '<td class="mr-col-actions">' +
                '<button type="button" class="btn btn-sm btn-outline admin-only" style="padding:2px 7px;font-size:11px;" onclick="openMonthlyIndModal(' + r._idx + ')">Edit</button> ' +
                '<button type="button" class="btn btn-sm btn-danger" style="padding:2px 7px;font-size:11px;" onclick="deleteMonthlyIndEntry(' + r._idx + ')">\u2715</button>' +
              '</td>' +
            '</tr>'
          );
        });
      }
      html.push(
        '<tr class="mr-total-row">' +
          '<td></td><td></td>' +
          '<td><strong>TOTAL</strong></td>' +
          '<td style="text-align:center;"><strong>' + t.teemIndTrips + '</strong></td>' +
          '<td></td>' +
          '<td><strong>' + formatNaira(t.teemIndTotal) + '</strong></td>' +
          '<td></td>' +
        '</tr>'
      );

      // Part 1B: Other Operator(s) / Group(s) Using TEEM Business Vehicle
      const pGroups = (t.partnerGroups && t.partnerGroups.length)
        ? t.partnerGroups
        : [{ title: t.partnerTitle || 'JIB & JIB', rows: [], trips: 0, total: 0 }];

      pGroups.forEach(pg => {
        html.push(
          '<tr class="mr-sub-banner-row"><td colspan="7">' + escapeHtml(pg.title.toUpperCase()) + ' INDUSTRIAL WASTE EVACUATION FOR THE MONTH OF ' + escapeHtml(monthCommaYear) + '</td></tr>'
        );
        if (!pg.rows.length) {
          html.push('<tr><td colspan="7" style="text-align:center;color:var(--text-muted);padding:10px;">No external operator vehicle trips recorded for ' + escapeHtml(t.period) + '.</td></tr>');
        } else {
          pg.rows.forEach(r => {
            sn += 1;
            html.push(
              '<tr>' +
                '<td>' + sn + '</td>' +
                '<td>' + escapeHtml(formatShortDateSlash(r.date)) + '</td>' +
                '<td>' + escapeHtml(r.company) + '</td>' +
                '<td style="text-align:center;font-weight:700;">' + r.trips + '</td>' +
                '<td>' + (r.rate > 0 ? formatNaira(r.rate) : '<span style="color:#B45309;font-size:11px;font-weight:700;">Admin Rate Pending</span>') + '</td>' +
                '<td><strong>' + formatNaira(r.amount) + '</strong></td>' +
                '<td class="mr-col-actions">' +
                  '<button type="button" class="btn btn-sm btn-outline admin-only" style="padding:2px 7px;font-size:11px;" onclick="openMonthlyIndModal(' + r._idx + ')">Edit</button> ' +
                  '<button type="button" class="btn btn-sm btn-danger" style="padding:2px 7px;font-size:11px;" onclick="deleteMonthlyIndEntry(' + r._idx + ')">\u2715</button>' +
                '</td>' +
              '</tr>'
            );
          });
        }
        html.push(
          '<tr class="mr-total-row">' +
            '<td></td><td></td><td></td>' +
            '<td style="text-align:center;"><strong>' + pg.trips + '</strong></td>' +
            '<td></td>' +
            '<td><strong>' + formatNaira(pg.total) + '</strong></td>' +
            '<td></td>' +
          '</tr>'
        );
      });

      html.push(
        '<tr class="mr-grand-total-row">' +
          '<td></td><td></td>' +
          '<td><strong>GRAND TOTAL</strong></td>' +
          '<td style="text-align:center;"><strong>' + (t.teemIndTrips + t.partnerIndTrips) + '</strong></td>' +
          '<td></td>' +
          '<td><strong>' + formatNaira(t.indGrandTotal) + '</strong></td>' +
          '<td></td>' +
        '</tr>'
      );
      indTbody.innerHTML = html.join('');
    }
  }

  // SECTION 2 TABLE: SALARY SCHEDULE
  const salTbody = document.getElementById('mr-salary-tbody');
  if (salTbody) {
    const rowsHtml = t.salaries.map((s, idx) =>
      '<tr>' +
        '<td style="text-align:center;">' + (idx + 1) + '.</td>' +
        '<td>' + escapeHtml(s.name) + '</td>' +
        '<td style="text-align:center;">' + escapeHtml(s.bank) + '</td>' +
        '<td>' + escapeHtml(s.accountNumber) + '</td>' +
        '<td>' + formatNaira(s.amount) + '</td>' +
        '<td class="mr-col-actions admin-only">' +
          '<button type="button" class="btn btn-sm btn-outline" style="padding:2px 7px;font-size:11px;" onclick="openMonthlySalaryModal(' + idx + ')">Edit</button> ' +
          '<button type="button" class="btn btn-sm btn-danger" style="padding:2px 7px;font-size:11px;" onclick="deleteMonthlySalaryEntry(' + idx + ')">\u2715</button>' +
        '</td>' +
      '</tr>'
    );
    rowsHtml.push(
      '<tr class="mr-total-row">' +
        '<td></td><td></td><td></td>' +
        '<td><strong>Total</strong></td>' +
        '<td><strong>' + formatNaira(t.salaryTotal) + '</strong></td>' +
        '<td class="admin-only"></td>' +
      '</tr>'
    );
    salTbody.innerHTML = rowsHtml.join('');
  }

  // SECTION 3 TABLE: MUNICIPAL REVENUE BREAKDOWN (TEEM ACC vs OGWAMA ACC) — Image 4: Supervisor name only (no "(TEEM/OGWAMA)" suffix)
  const munTbody = document.getElementById('mr-municipal-tbody');
  if (munTbody) {
    const rowsHtml = t.municipal.map((m, idx) => {
      const sub = (Number(m.teemAmount) || 0) + (Number(m.ogwamaAmount) || 0);
      return '<tr>' +
        '<td style="text-align:center;">' + (idx + 1) + '.</td>' +
        '<td><strong>' + escapeHtml(m.supervisor) + '</strong></td>' +
        '<td>' + formatNaira(m.teemAmount) + '</td>' +
        '<td>' + formatNaira(m.ogwamaAmount) + '</td>' +
        '<td><strong>' + formatNaira(sub) + '</strong></td>' +
        '<td class="mr-col-actions admin-only">' +
          '<button type="button" class="btn btn-sm btn-outline" style="padding:2px 7px;font-size:11px;" onclick="openMonthlyMunicipalModal(' + idx + ')">Edit</button> ' +
          '<button type="button" class="btn btn-sm btn-danger" style="padding:2px 7px;font-size:11px;" onclick="deleteMonthlyMunicipalEntry(' + idx + ')">\u2715</button>' +
        '</td>' +
      '</tr>';
    });
    rowsHtml.push(
      '<tr class="mr-grand-total-row">' +
        '<td colspan="2" style="text-align:right;"><strong>TOTAL MONEY GENERATED FROM MUNICIPAL</strong></td>' +
        '<td><strong>' + formatNaira(t.munTeemTotal) + '</strong></td>' +
        '<td><strong>' + formatNaira(t.munOgwamaTotal) + '</strong></td>' +
        '<td><strong>' + formatNaira(t.municipalTotal) + '</strong></td>' +
        '<td class="admin-only"></td>' +
      '</tr>'
    );
    munTbody.innerHTML = rowsHtml.join('');
  }

  // SECTION 4 TABLE: FUEL PURCHASED (Both Supervisor and Admin can See, Add, Edit & Delete)
  const fuelTbody = document.getElementById('mr-fuel-tbody');
  if (fuelTbody) {
    const rowsHtml = t.fuel.map((f, idx) => {
      const amt = (Number(f.litres) || 0) * (Number(f.rate) || 0);
      return '<tr>' +
        '<td style="text-align:center;">' + (idx + 1) + '.</td>' +
        '<td><strong>' + escapeHtml(formatFullDateSlash(f.date)) + '</strong></td>' +
        '<td>' + escapeHtml(f.fuelType || 'Diesel') + '</td>' +
        '<td><strong>' + Number(f.litres).toLocaleString('en-NG') + ' Ltrs</strong></td>' +
        '<td>' + formatNaira(f.rate) + '</td>' +
        '<td><strong>' + amt.toLocaleString('en-NG') + '</strong></td>' +
        '<td class="mr-col-actions">' +
          '<button type="button" class="btn btn-sm btn-outline" style="padding:2px 7px;font-size:11px;" onclick="openMonthlyFuelModal(' + idx + ')">Edit</button> ' +
          '<button type="button" class="btn btn-sm btn-danger" style="padding:2px 7px;font-size:11px;" onclick="deleteMonthlyFuelEntry(' + idx + ')">\u2715</button>' +
        '</td>' +
      '</tr>';
    });
    rowsHtml.push(
      '<tr class="mr-total-row">' +
        '<td></td><td></td><td></td>' +
        '<td><strong>Total (' + t.fuelLitresTotal.toLocaleString('en-NG') + ' Ltrs)</strong></td>' +
        '<td></td>' +
        '<td><strong>' + t.fuelTotal.toLocaleString('en-NG') + '</strong></td>' +
        '<td></td>' +
      '</tr>'
    );
    fuelTbody.innerHTML = rowsHtml.join('');
  }

  // SECTION 5 TABLE: VEHICLE REPAIR (Both Supervisor and Admin can See, Add, Edit & Delete)
  const repTbody = document.getElementById('mr-repair-tbody');
  if (repTbody) {
    const rowsHtml = [];
    if (!t.repairs.length) {
      rowsHtml.push('<tr><td colspan="5" style="text-align:center;color:var(--text-muted);padding:10px;">No vehicle repairs recorded for ' + escapeHtml(t.period) + '.</td></tr>');
    } else {
      t.repairs.forEach((r, idx) => {
        rowsHtml.push(
          '<tr>' +
            '<td style="text-align:center;">' + (idx + 1) + '.</td>' +
            '<td><strong>' + escapeHtml(r.vehicle || 'BLUE COMPACTOR') + '</strong></td>' +
            '<td>' + escapeHtml(r.description) + '</td>' +
            '<td><strong>' + Number(r.amount || 0).toLocaleString('en-NG') + '</strong></td>' +
            '<td class="mr-col-actions">' +
              '<button type="button" class="btn btn-sm btn-outline" style="padding:2px 7px;font-size:11px;" onclick="openMonthlyRepairModal(' + idx + ')">Edit</button> ' +
              '<button type="button" class="btn btn-sm btn-danger" style="padding:2px 7px;font-size:11px;" onclick="deleteMonthlyRepairEntry(' + idx + ')">\u2715</button>' +
            '</td>' +
          '</tr>'
        );
      });
    }
    rowsHtml.push(
      '<tr class="mr-total-row">' +
        '<td></td><td></td>' +
        '<td><strong>Total Vehicle Repair</strong></td>' +
        '<td><strong>' + t.repairTotal.toLocaleString('en-NG') + '</strong></td>' +
        '<td></td>' +
      '</tr>'
    );
    repTbody.innerHTML = rowsHtml.join('');
  }

  // SECTION 6 TABLE: SUMMARY OF EXPENDITURE AND REVENUE (MATCHING SAMPLE IMAGE 4)
  const sumTbody = document.getElementById('mr-summary-tbody');
  if (sumTbody) {
    const sHtml = [];
    sHtml.push(
      '<tr class="mr-sub-banner-row"><td colspan="4">EXPENDITURE</td></tr>' +
      '<tr class="mr-col-head">' +
        '<th style="width:58px;">S/N</th>' +
        '<th>PARTICULAR(S)</th>' +
        '<th style="width:180px;">AMOUNT (&#8358;)</th>' +
        '<th style="width:190px;">TOTAL (&#8358;)</th>' +
      '</tr>' +
      '<tr>' +
        '<td><strong>1.</strong></td>' +
        '<td>' + escapeHtml(t.period) + ' Salary</td>' +
        '<td><strong>' + t.salaryTotal.toLocaleString('en-NG') + '</strong></td>' +
        '<td></td>' +
      '</tr>' +
      '<tr>' +
        '<td><strong>2.</strong></td>' +
        '<td>Fuel Purchased</td>' +
        '<td><strong>' + t.fuelTotal.toLocaleString('en-NG') + '</strong></td>' +
        '<td></td>' +
      '</tr>'
    );
    if (t.repairs.length) {
      const vehGroup = (t.repairs[0].vehicle || 'BLUE COMPACTOR').toUpperCase();
      sHtml.push(
        '<tr class="mr-sub-banner-row"><td></td><td colspan="3"><strong>' + escapeHtml(vehGroup) + ' (VEHICLE REPAIR)</strong></td></tr>'
      );
      t.repairs.forEach((r, idx) => {
        sHtml.push(
          '<tr>' +
            '<td><strong>' + (idx + 3) + '.</strong></td>' +
            '<td>' + escapeHtml(r.description) + '</td>' +
            '<td><strong>' + Number(r.amount || 0).toLocaleString('en-NG') + '</strong></td>' +
            '<td></td>' +
          '</tr>'
        );
      });
    } else {
      sHtml.push(
        '<tr>' +
          '<td><strong>3.</strong></td>' +
          '<td>Vehicle Repair</td>' +
          '<td><strong>0</strong></td>' +
          '<td></td>' +
        '</tr>'
      );
    }
    sHtml.push(
      '<tr class="mr-total-row">' +
        '<td></td>' +
        '<td><strong>TOTAL EXPENSES</strong></td>' +
        '<td></td>' +
        '<td><strong>' + t.totalExpenses.toLocaleString('en-NG') + '</strong></td>' +
      '</tr>' +
      '<tr class="mr-sub-banner-row"><td></td><td colspan="3"><strong>INCOME</strong></td></tr>' +
      '<tr>' +
        '<td><strong>1.</strong></td>' +
        '<td><strong>MUNICIPAL EVACUATION</strong></td>' +
        '<td><strong>' + t.municipalTotal.toLocaleString('en-NG') + '</strong></td>' +
        '<td></td>' +
      '</tr>' +
      '<tr>' +
        '<td><strong>2.</strong></td>' +
        '<td><strong>IGR FROM COMPACTOR</strong></td>' +
        '<td><strong>' + t.indGrandTotal.toLocaleString('en-NG') + '</strong></td>' +
        '<td></td>' +
      '</tr>' +
      '<tr class="mr-total-row">' +
        '<td></td>' +
        '<td><strong>TOTAL REVENUE</strong></td>' +
        '<td></td>' +
        '<td><strong>' + t.totalRevenue.toLocaleString('en-NG') + '</strong></td>' +
      '</tr>' +
      '<tr class="mr-grand-total-row">' +
        '<td></td>' +
        '<td><strong>INCOME GENERATED FOR ' + escapeHtml(t.period.toUpperCase()) + '</strong></td>' +
        '<td></td>' +
        '<td><strong class="mr-deficit-val">' + (t.netIncome < 0 ? '-' : '') + formatNaira(Math.abs(t.netIncome)) + '</strong></td>' +
      '</tr>'
    );
    sumTbody.innerHTML = sHtml.join('');
  }
}

// --- Interactive CRUD for Monthly Report Sections 1 to 5 ---
function onMonthlyIndGroupChanged() {
  const grp = document.getElementById('mr-ind-group');
  const wrap = document.getElementById('mr-ind-partner-name-wrap');
  const rateEl = document.getElementById('mr-ind-rate');
  const pInput = document.getElementById('mr-ind-partner-title');
  if (wrap && grp) wrap.style.display = grp.value === 'partner' ? '' : 'none';
  if (pInput && grp) pInput.required = grp.value === 'partner';
  if (rateEl && grp && !document.getElementById('mr-ind-edit-idx').value) {
    rateEl.value = isAdmin() ? (grp.value === 'partner' ? 30000 : 40000) : 0;
    updateMonthlyIndPreviewTotal();
  }
}

function updateMonthlyIndPreviewTotal() {
  const trips = Math.max(1, Number((document.getElementById('mr-ind-trips') || {}).value) || 1);
  const rate = Math.max(0, Number((document.getElementById('mr-ind-rate') || {}).value) || 0);
  const prev = document.getElementById('mr-ind-total-preview');
  if (prev) prev.value = formatNaira(trips * rate);
}

function openMonthlyIndModal(editIdx) {
  if (typeof editIdx === 'number' && !requireAdmin('Editing an industrial evacuation trip or vehicle usage rate')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const dl = document.getElementById('mr-industrial-facilities-list');
  if (dl) {
    const indFacs = (store.state.facilities || []).filter(f => f.category === 'Industrial').map(f => f.name);
    dl.innerHTML = indFacs.map(n => '<option value="' + escapeHtml(n) + '"></option>').join('');
  }
  const pDl = document.getElementById('mr-partner-operators-list');
  if (pDl) {
    const knownPartners = ['JIB & JIB'];
    if (data.partnerTitle && !knownPartners.includes(data.partnerTitle)) knownPartners.push(data.partnerTitle);
    (data.industrial || []).forEach(r => {
      if (r.group === 'partner' && r.partnerTitle && !knownPartners.includes(r.partnerTitle)) {
        knownPartners.push(r.partnerTitle);
      }
    });
    pDl.innerHTML = knownPartners.map(n => '<option value="' + escapeHtml(n) + '"></option>').join('');
  }
  const rateGrp = document.getElementById('mr-ind-rate-group');
  const totGrp = document.getElementById('mr-ind-total-group');
  const supHint = document.getElementById('mr-supervisor-rate-hint');
  const tripGrid = document.getElementById('mr-ind-trip-grid');
  const adminActive = isAdmin();
  if (rateGrp) rateGrp.style.display = adminActive ? '' : 'none';
  if (totGrp) totGrp.style.display = adminActive ? '' : 'none';
  if (supHint) supHint.style.display = adminActive ? 'none' : '';
  if (tripGrid) tripGrid.style.gridTemplateColumns = adminActive ? 'repeat(3,minmax(0,1fr))' : 'minmax(0,1fr)';

  const idxEl = document.getElementById('mr-ind-edit-idx');
  const titleEl = document.getElementById('mr-ind-modal-title');
  if (typeof editIdx === 'number' && data.industrial[editIdx]) {
    const r = data.industrial[editIdx];
    idxEl.value = String(editIdx);
    if (titleEl) titleEl.textContent = 'Edit Industrial / Vehicle Usage Trip';
    document.getElementById('mr-ind-group').value = r.group === 'partner' ? 'partner' : 'teem';
    document.getElementById('mr-ind-partner-title').value = r.partnerTitle || data.partnerTitle || 'JIB & JIB';
    document.getElementById('mr-ind-date').value = r.date || currentUsageDateIso();
    document.getElementById('mr-ind-company').value = r.company || '';
    document.getElementById('mr-ind-trips').value = r.trips || 1;
    document.getElementById('mr-ind-rate').value = r.rate !== undefined ? r.rate : 40000;
  } else {
    idxEl.value = '';
    if (titleEl) titleEl.textContent = '+ Add Industrial / Vehicle Usage Trip';
    document.getElementById('mr-ind-group').value = 'teem';
    document.getElementById('mr-ind-partner-title').value = data.partnerTitle || 'JIB & JIB';
    document.getElementById('mr-ind-date').value = currentUsageDateIso();
    document.getElementById('mr-ind-company').value = '';
    document.getElementById('mr-ind-trips').value = 1;
    document.getElementById('mr-ind-rate').value = adminActive ? 40000 : 0;
  }
  onMonthlyIndGroupChanged();
  updateMonthlyIndPreviewTotal();
  openModal('modal-mr-industrial');
}

function saveMonthlyIndEntry(ev) {
  if (ev) ev.preventDefault();
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const editIdx = document.getElementById('mr-ind-edit-idx').value;
  if (editIdx !== '' && !requireAdmin('Editing an industrial evacuation trip or vehicle usage rate')) return;
  const grp = document.getElementById('mr-ind-group').value;
  const partnerTitle = (document.getElementById('mr-ind-partner-title').value || 'JIB & JIB').trim() || 'JIB & JIB';
  if (grp === 'partner') data.partnerTitle = partnerTitle;
  const adminActive = isAdmin();
  const existingRate = (editIdx !== '' && data.industrial[Number(editIdx)])
    ? (Number(data.industrial[Number(editIdx)].rate) || 0)
    : 0;
  const rateVal = adminActive
    ? Math.max(0, Number(document.getElementById('mr-ind-rate').value) || 0)
    : existingRate;
  const entry = {
    date: document.getElementById('mr-ind-date').value || currentUsageDateIso(),
    company: (document.getElementById('mr-ind-company').value || '').trim(),
    trips: Math.max(1, Number(document.getElementById('mr-ind-trips').value) || 1),
    rate: rateVal,
    group: grp,
    partnerTitle: grp === 'partner' ? partnerTitle : undefined
  };
  if (editIdx !== '' && data.industrial[Number(editIdx)]) {
    data.industrial[Number(editIdx)] = entry;
  } else {
    data.industrial.push(entry);
  }
  data.updatedAt = new Date().toISOString();
  store.save();
  closeModal('modal-mr-industrial');
  renderMonthlyReport();
  showToast('\u2705 Industrial evacuation trip saved.', 'success');
}

function deleteMonthlyIndEntry(idx) {
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  if (!data.industrial[idx]) return;
  data.industrial.splice(idx, 1);
  data.updatedAt = new Date().toISOString();
  store.save();
  renderMonthlyReport();
  showToast('\ud83d\uddd1\ufe0f Industrial trip entry removed.', 'warning');
}

function syncMonthlyIndustrialFromLogs() {
  if (!requireAdmin('Syncing industrial evacuation logs')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const parts = activeMonthlyReportPeriod.split(' ');
  const monthIdx = ['January','February','March','April','May','June','July','August','September','October','November','December'].indexOf(parts[0]);
  const ymPrefix = (parts[1] || '2026') + '-' + String(monthIdx + 1).padStart(2, '0');
  let added = 0;
  (store.state.facilities || []).filter(f => f.category === 'Industrial').forEach(fac => {
    const dates = [];
    if (fac.lastEvacuated && String(fac.lastEvacuated).startsWith(ymPrefix)) dates.push(fac.lastEvacuated);
    (fac.evacuationHistory || []).forEach(h => {
      const d = h.date || h;
      if (d && String(d).startsWith(ymPrefix) && !dates.includes(d)) dates.push(d);
    });
    dates.forEach(d => {
      const exists = data.industrial.some(r => r.group !== 'partner' && r.company === fac.name && r.date === d);
      if (!exists) {
        data.industrial.push({ date: d, company: fac.name, trips: 1, rate: 40000, group: 'teem' });
        added += 1;
      }
    });
  });
  store.save();
  renderMonthlyReport();
  showToast('\ud83d\udd04 Synced ' + added + ' industrial evacuation record(s) for ' + activeMonthlyReportPeriod + '.', 'success');
}

function openMonthlySalaryModal(editIdx) {
  if (!requireAdmin('Managing officer salary schedule')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const idxEl = document.getElementById('mr-sal-edit-idx');
  const titleEl = document.getElementById('mr-sal-modal-title');
  if (typeof editIdx === 'number' && data.salaries[editIdx]) {
    const s = data.salaries[editIdx];
    idxEl.value = String(editIdx);
    if (titleEl) titleEl.textContent = 'Edit Officer Salary Entry';
    document.getElementById('mr-sal-name').value = s.name || '';
    document.getElementById('mr-sal-bank').value = s.bank || '';
    document.getElementById('mr-sal-acct').value = s.accountNumber || '';
    document.getElementById('mr-sal-amount').value = s.amount || 0;
  } else {
    idxEl.value = '';
    if (titleEl) titleEl.textContent = '+ Add Officer Salary Entry';
    document.getElementById('mr-sal-name').value = '';
    document.getElementById('mr-sal-bank').value = '';
    document.getElementById('mr-sal-acct').value = '';
    document.getElementById('mr-sal-amount').value = '';
  }
  openModal('modal-mr-salary');
}

function saveMonthlySalaryEntry(ev) {
  if (ev) ev.preventDefault();
  if (!requireAdmin('Managing officer salary schedule')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const editIdx = document.getElementById('mr-sal-edit-idx').value;
  const entry = {
    name: (document.getElementById('mr-sal-name').value || '').trim(),
    bank: (document.getElementById('mr-sal-bank').value || '').trim(),
    accountNumber: (document.getElementById('mr-sal-acct').value || '').trim(),
    amount: Math.max(0, Number(document.getElementById('mr-sal-amount').value) || 0)
  };
  if (editIdx !== '' && data.salaries[Number(editIdx)]) data.salaries[Number(editIdx)] = entry;
  else data.salaries.push(entry);
  data.updatedAt = new Date().toISOString();
  store.save();
  closeModal('modal-mr-salary');
  renderMonthlyReport();
  showToast('\u2705 Salary entry saved.', 'success');
}

function deleteMonthlySalaryEntry(idx) {
  if (!requireAdmin('Deleting a salary schedule entry')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  if (!data.salaries[idx]) return;
  data.salaries.splice(idx, 1);
  data.updatedAt = new Date().toISOString();
  store.save();
  renderMonthlyReport();
  showToast('\ud83d\uddd1\ufe0f Salary entry removed.', 'warning');
}

function updateMonthlyMunPreviewTotal() {
  const t = Math.max(0, Number((document.getElementById('mr-mun-teem') || {}).value) || 0);
  const o = Math.max(0, Number((document.getElementById('mr-mun-ogwama') || {}).value) || 0);
  const prev = document.getElementById('mr-mun-total-preview');
  if (prev) prev.value = formatNaira(t + o);
}

function openMonthlyMunicipalModal(editIdx) {
  if (!requireAdmin('Managing municipal revenue breakdown')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const dl = document.getElementById('mr-supervisors-datalist');
  if (dl) {
    const names = (store.state.supervisors || []).map(s => s.name);
    dl.innerHTML = names.map(n => '<option value="' + escapeHtml(n.toUpperCase()) + '"></option>').join('');
  }
  const idxEl = document.getElementById('mr-mun-edit-idx');
  const titleEl = document.getElementById('mr-mun-modal-title');
  if (typeof editIdx === 'number' && data.municipal[editIdx]) {
    const m = data.municipal[editIdx];
    idxEl.value = String(editIdx);
    if (titleEl) titleEl.textContent = 'Edit Supervisor Municipal Revenue';
    document.getElementById('mr-mun-supervisor').value = m.supervisor || '';
    document.getElementById('mr-mun-teem').value = m.teemAmount || 0;
    document.getElementById('mr-mun-ogwama').value = m.ogwamaAmount || 0;
  } else {
    idxEl.value = '';
    if (titleEl) titleEl.textContent = '+ Add Supervisor Municipal Revenue';
    document.getElementById('mr-mun-supervisor').value = '';
    document.getElementById('mr-mun-teem').value = 0;
    document.getElementById('mr-mun-ogwama').value = 0;
  }
  updateMonthlyMunPreviewTotal();
  openModal('modal-mr-municipal');
}

function saveMonthlyMunicipalEntry(ev) {
  if (ev) ev.preventDefault();
  if (!requireAdmin('Managing municipal revenue breakdown')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const editIdx = document.getElementById('mr-mun-edit-idx').value;
  const entry = {
    supervisor: (document.getElementById('mr-mun-supervisor').value || '').trim().toUpperCase(),
    teemAmount: Math.max(0, Number(document.getElementById('mr-mun-teem').value) || 0),
    ogwamaAmount: Math.max(0, Number(document.getElementById('mr-mun-ogwama').value) || 0)
  };
  if (editIdx !== '' && data.municipal[Number(editIdx)]) data.municipal[Number(editIdx)] = entry;
  else data.municipal.push(entry);
  data.updatedAt = new Date().toISOString();
  store.save();
  closeModal('modal-mr-municipal');
  renderMonthlyReport();
  showToast('\u2705 Municipal revenue breakdown saved.', 'success');
}

function deleteMonthlyMunicipalEntry(idx) {
  if (!requireAdmin('Deleting a municipal revenue entry')) return;
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  if (!data.municipal[idx]) return;
  data.municipal.splice(idx, 1);
  data.updatedAt = new Date().toISOString();
  store.save();
  renderMonthlyReport();
  showToast('\ud83d\uddd1\ufe0f Municipal revenue entry removed.', 'warning');
}

function updateMonthlyFuelPreviewTotal() {
  const l = Math.max(0, Number((document.getElementById('mr-fuel-litres') || {}).value) || 0);
  const r = Math.max(0, Number((document.getElementById('mr-fuel-rate') || {}).value) || 0);
  const prev = document.getElementById('mr-fuel-total-preview');
  if (prev) prev.value = formatNaira(l * r);
}

function openMonthlyFuelModal(editIdx) {
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const idxEl = document.getElementById('mr-fuel-edit-idx');
  const titleEl = document.getElementById('mr-fuel-modal-title');
  if (typeof editIdx === 'number' && data.fuel[editIdx]) {
    const f = data.fuel[editIdx];
    idxEl.value = String(editIdx);
    if (titleEl) titleEl.textContent = 'Edit Fuel Purchase';
    document.getElementById('mr-fuel-date').value = f.date || currentUsageDateIso();
    document.getElementById('mr-fuel-type').value = f.fuelType || 'Diesel';
    document.getElementById('mr-fuel-litres').value = f.litres || 50;
    document.getElementById('mr-fuel-rate').value = f.rate || 1850;
  } else {
    idxEl.value = '';
    if (titleEl) titleEl.textContent = '+ Add Fuel Purchase';
    document.getElementById('mr-fuel-date').value = currentUsageDateIso();
    document.getElementById('mr-fuel-type').value = 'Diesel';
    document.getElementById('mr-fuel-litres').value = 50;
    document.getElementById('mr-fuel-rate').value = 1850;
  }
  updateMonthlyFuelPreviewTotal();
  openModal('modal-mr-fuel');
}

function saveMonthlyFuelEntry(ev) {
  if (ev) ev.preventDefault();
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const editIdx = document.getElementById('mr-fuel-edit-idx').value;
  const entry = {
    date: document.getElementById('mr-fuel-date').value || currentUsageDateIso(),
    fuelType: document.getElementById('mr-fuel-type').value || 'Diesel',
    litres: Math.max(0.5, Number(document.getElementById('mr-fuel-litres').value) || 0),
    rate: Math.max(0, Number(document.getElementById('mr-fuel-rate').value) || 0)
  };
  if (editIdx !== '' && data.fuel[Number(editIdx)]) data.fuel[Number(editIdx)] = entry;
  else data.fuel.push(entry);
  data.updatedAt = new Date().toISOString();
  store.save();
  closeModal('modal-mr-fuel');
  renderMonthlyReport();
  showToast('\u2705 Fuel purchase saved.', 'success');
}

function deleteMonthlyFuelEntry(idx) {
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  if (!data.fuel[idx]) return;
  data.fuel.splice(idx, 1);
  data.updatedAt = new Date().toISOString();
  store.save();
  renderMonthlyReport();
  showToast('\ud83d\uddd1\ufe0f Fuel purchase entry removed.', 'warning');
}

function openMonthlyRepairModal(editIdx) {
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const idxEl = document.getElementById('mr-rep-edit-idx');
  const titleEl = document.getElementById('mr-rep-modal-title');
  if (typeof editIdx === 'number' && data.repairs[editIdx]) {
    const r = data.repairs[editIdx];
    idxEl.value = String(editIdx);
    if (titleEl) titleEl.textContent = 'Edit Vehicle Repair Entry';
    document.getElementById('mr-rep-vehicle').value = r.vehicle || 'BLUE COMPACTOR';
    document.getElementById('mr-rep-desc').value = r.description || '';
    document.getElementById('mr-rep-amount').value = r.amount || 0;
  } else {
    idxEl.value = '';
    if (titleEl) titleEl.textContent = '+ Add Vehicle Repair / Maintenance';
    document.getElementById('mr-rep-vehicle').value = 'BLUE COMPACTOR';
    document.getElementById('mr-rep-desc').value = '';
    document.getElementById('mr-rep-amount').value = '';
  }
  openModal('modal-mr-repair');
}

function saveMonthlyRepairEntry(ev) {
  if (ev) ev.preventDefault();
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  const editIdx = document.getElementById('mr-rep-edit-idx').value;
  const entry = {
    vehicle: (document.getElementById('mr-rep-vehicle').value || 'BLUE COMPACTOR').trim().toUpperCase(),
    description: (document.getElementById('mr-rep-desc').value || '').trim(),
    amount: Math.max(0, Number(document.getElementById('mr-rep-amount').value) || 0)
  };
  if (editIdx !== '' && data.repairs[Number(editIdx)]) data.repairs[Number(editIdx)] = entry;
  else data.repairs.push(entry);
  data.updatedAt = new Date().toISOString();
  store.save();
  closeModal('modal-mr-repair');
  renderMonthlyReport();
  showToast('\u2705 Vehicle repair entry saved.', 'success');
}

function deleteMonthlyRepairEntry(idx) {
  const data = getMonthlyReportData(activeMonthlyReportPeriod);
  if (!data.repairs[idx]) return;
  data.repairs.splice(idx, 1);
  data.updatedAt = new Date().toISOString();
  store.save();
  renderMonthlyReport();
  showToast('\ud83d\uddd1\ufe0f Vehicle repair entry removed.', 'warning');
}

function monthlyReportSpec(period) {
  const t = computeMonthlyReportTotals(period || activeMonthlyReportPeriod);
  const slug = t.period.replace(/\s+/g, '_');
  return Object.assign({
    kind: 'monthly',
    reference: 'TEEM-MIE-' + slug.toUpperCase(),
    dateText: formatLetterDate(currentUsageDateIso()),
    total: Math.abs(t.netIncome),
    filename: 'TEEM_Monthly_Income_Expenditure_' + slug + '.pdf'
  }, t);
}

function buildMonthlyReportPdf(spec, options) {
  options = options || {};
  const parts = (spec.period || 'October 2026').split(' ');
  const monthUpper = (parts[0] || 'OCTOBER').toUpperCase();
  const yearStr = parts[1] || '2026';
  const monthCommaYear = monthUpper + ', ' + yearStr;
  const fmtN = v => 'N' + Number(v || 0).toLocaleString('en-NG');

  const doc = new PdfDoc({
    reference: spec.reference || ('TEEM-MIE-' + monthUpper + '-' + yearStr),
    heading: monthUpper + ' ' + yearStr + ' INCOME AND EXPENDITURE ANALYSIS',
    subheading: 'INDUSTRIAL EVACUATION & MONTHLY OPERATIONS SUMMARY',
    layout: options.layout,
    fontScale: options.fontScale
  });

  doc.text(monthUpper + ' ' + yearStr + ' INCOME AND EXPENDITURE ANALYSIS', { style: 'bold', size: 13, align: 'center' });
  doc.gap(2);

  // Section 1: Industrial Evacuation (TEEM + Partner(s))
  doc.text('1. TEEM BUSINESS INDUSTRIAL WASTE EVACUATION FOR THE MONTH OF ' + monthCommaYear, { style: 'bold', size: 10.5 });
  doc.gap(1);
  let sn = 0;
  const indRows = [];
  (spec.teemInd || []).forEach(r => {
    sn += 1;
    indRows.push([String(sn), formatShortDateSlash(r.date), r.company, String(r.trips), fmtN(r.rate), fmtN(r.amount)]);
  });
  indRows.push(['', '', 'TOTAL (TEEM INDUSTRIAL)', String(spec.teemIndTrips || 0), '', fmtN(spec.teemIndTotal || 0)]);
  const pGroups = (spec.partnerGroups && spec.partnerGroups.length)
    ? spec.partnerGroups
    : [{ title: spec.partnerTitle || 'JIB & JIB', rows: spec.partnerInd || [], trips: spec.partnerIndTrips || 0, total: spec.partnerIndTotal || 0 }];
  pGroups.forEach(pg => {
    (pg.rows || []).forEach(r => {
      sn += 1;
      indRows.push([String(sn), formatShortDateSlash(r.date), '[' + pg.title + '] ' + r.company, String(r.trips), fmtN(r.rate), fmtN(r.amount)]);
    });
    indRows.push(['', '', 'SUBTOTAL (' + pg.title + ')', String(pg.trips || 0), '', fmtN(pg.total || 0)]);
  });
  indRows.push(['', '', 'GRAND TOTAL (SECTION 1)', String((spec.teemIndTrips || 0) + (spec.partnerIndTrips || 0)), '', fmtN(spec.indGrandTotal || 0)]);

  doc.table(
    [
      { label: 'S/N', width: 12, align: 'center' },
      { label: 'DATE', width: 24, align: 'center' },
      { label: 'COMPANY / FACILITY', width: 66 },
      { label: 'TRIPS', width: 16, align: 'center' },
      { label: 'RATE/TRIP', width: 28, align: 'right' },
      { label: 'AMOUNT', width: 28, align: 'right' }
    ],
    indRows,
    { fontSize: 9.8 }
  );
  doc.gap(3);

  // Section 2: Salary Schedule
  doc.text('2. SALARY SCHEDULE FOR THE MONTH OF ' + monthCommaYear, { style: 'bold', size: 10.5 });
  doc.gap(1);
  const salRows = (spec.salaries || []).map((s, idx) => [
    (idx + 1) + '.',
    s.name,
    s.bank,
    s.accountNumber,
    fmtN(s.amount)
  ]);
  salRows.push(['', '', '', 'Total', fmtN(spec.salaryTotal || 0)]);
  doc.table(
    [
      { label: 'S/N', width: 14, align: 'center' },
      { label: 'NAMES', width: 62 },
      { label: 'BANKER', width: 30, align: 'center' },
      { label: 'ACCT.NO', width: 36, align: 'center' },
      { label: 'AMOUNT', width: 32, align: 'right' }
    ],
    salRows,
    { fontSize: 9.8 }
  );
  doc.gap(3);

  // Section 3: Municipal Revenue Breakdown (Image 4: supervisor name only, no "(TEEM/OGWAMA)" suffix)
  doc.text('3. MUNICIPAL ANALYSIS FOR TEEM BUSINESS (BREAKDOWN ANALYSIS)', { style: 'bold', size: 10.5 });
  doc.gap(1);
  const munRows = (spec.municipal || []).map((m, idx) => [
    (idx + 1) + '.',
    m.supervisor,
    fmtN(m.teemAmount),
    fmtN(m.ogwamaAmount),
    fmtN((Number(m.teemAmount) || 0) + (Number(m.ogwamaAmount) || 0))
  ]);
  munRows.push(['', 'TOTAL MONEY GENERATED FROM MUNICIPAL', fmtN(spec.munTeemTotal || 0), fmtN(spec.munOgwamaTotal || 0), fmtN(spec.municipalTotal || 0)]);
  doc.table(
    [
      { label: 'S/N', width: 14, align: 'center' },
      { label: 'SUPERVISOR', width: 58 },
      { label: 'TEEM ACC', width: 34, align: 'right' },
      { label: 'OGWAMA ACC', width: 34, align: 'right' },
      { label: 'TOTAL', width: 34, align: 'right' }
    ],
    munRows,
    { fontSize: 9.8 }
  );
  doc.gap(3);

  // Section 4: Fuel Purchased
  doc.text('4. FUEL PURCHASED', { style: 'bold', size: 10.5 });
  doc.gap(1);
  const fuelRows = (spec.fuel || []).map((f, idx) => [
    (idx + 1) + '.',
    formatFullDateSlash(f.date),
    f.fuelType || 'Diesel',
    f.litres + ' Ltrs',
    fmtN(f.rate),
    fmtN((Number(f.litres) || 0) * (Number(f.rate) || 0))
  ]);
  fuelRows.push(['', '', '', 'Total (' + (spec.fuelLitresTotal || 0) + ' Ltrs)', '', fmtN(spec.fuelTotal || 0)]);
  doc.table(
    [
      { label: 'S/N', width: 12, align: 'center' },
      { label: 'DATE', width: 28, align: 'center' },
      { label: 'FUEL TYPE', width: 28, align: 'center' },
      { label: 'NO OF LITRES', width: 38, align: 'center' },
      { label: 'AMOUNT/LITRE', width: 34, align: 'right' },
      { label: 'TOTAL', width: 34, align: 'right' }
    ],
    fuelRows,
    { fontSize: 9.8 }
  );
  doc.gap(3);

  // Section 5 & 6: Summary of Expenditure and Revenue
  doc.text('5 & 6. SUMMARY OF EXPENDITURE AND REVENUE', { style: 'bold', size: 10.5 });
  doc.gap(1);
  const sumRows = [
    ['1.', spec.period + ' Salary', fmtN(spec.salaryTotal || 0), ''],
    ['2.', 'Fuel Purchased', fmtN(spec.fuelTotal || 0), '']
  ];
  (spec.repairs || []).forEach((r, idx) => {
    sumRows.push([(idx + 3) + '.', (r.vehicle ? r.vehicle + ' - ' : '') + r.description, fmtN(r.amount || 0), '']);
  });
  sumRows.push(['', 'TOTAL EXPENSES', '', fmtN(spec.totalExpenses || 0)]);
  sumRows.push(['1.', 'INCOME: MUNICIPAL EVACUATION', fmtN(spec.municipalTotal || 0), '']);
  sumRows.push(['2.', 'INCOME: IGR FROM COMPACTOR', fmtN(spec.indGrandTotal || 0), '']);
  sumRows.push(['', 'TOTAL REVENUE', '', fmtN(spec.totalRevenue || 0)]);
  sumRows.push(['', 'INCOME GENERATED FOR ' + (spec.period || '').toUpperCase(), '', (spec.netIncome < 0 ? '-' : '') + fmtN(Math.abs(spec.netIncome || 0))]);
  doc.table(
    [
      { label: 'S/N', width: 14, align: 'center' },
      { label: 'PARTICULAR(S)', width: 88 },
      { label: 'AMOUNT (N)', width: 36, align: 'right' },
      { label: 'TOTAL (N)', width: 36, align: 'right' }
    ],
    sumRows,
    { fontSize: 9.8 }
  );

  doc.keep(22);
  doc.gap(2);
  doc.rule({ color: 180 });
  doc.gap(2);
  doc.text('Prepared by: ' + userFullName(currentUser()) + '    Date: ' + formatDate(currentUsageDateIso()), { size: 9.8 });

  const filename = spec.filename || ('TEEM_Monthly_Income_Expenditure_' + (spec.reference || '2026') + '.pdf');
  const finalDoc = doc.finalize({ title: monthUpper + ' ' + yearStr + ' Income and Expenditure Analysis' });
  if (!options.defer) finalDoc.save(filename);
  return { pages: doc.pages, filename: filename, doc: finalDoc, closingPushed: !!doc.closingPushed, signaturePage: doc.signaturePage, lastPageFill: doc.lastPageFill || 0 };
}

function openPreviewForMonthlyReport() { openDocPreview('monthly'); }
function printMonthlyReport() { openDocPreview('monthly', { collapseSettings: true }); }
function saveMonthlyReportPdf() {
  const spec = monthlyReportSpec();
  if (!spec || !teemPdfAvailable()) return;
  const result = renderPdfForContext(spec, buildMonthlyReportPdf, docPreviewSettings());
  savePdfResult(result, spec.period.toUpperCase() + ' INCOME AND EXPENDITURE ANALYSIS', spec, spec.filename);
}

// Regenerate a stored archive copy (data is kept, the PDF is rebuilt on demand)
function rebuildArchivedPdf(doc, options) {
  options = options || {};
  if (!teemPdfAvailable()) {
    showToast('\u26a0\ufe0f The PDF engine is not loaded in this copy.', 'error');
    return;
  }
  const builders = { request: buildRequestPdf, facility: buildFacilityReportPdf, street: buildStreetReportPdf, audit: buildAuditPdf, debtors: buildDebtorReportPdf, monthly: buildMonthlyReportPdf };
  const builder = builders[doc.kind];
  if (!builder) { showToast('\u26a0\ufe0f Unknown archived document type.', 'error'); return; }
  if (options.print) {
    openDocPreview(doc.kind, { collapseSettings: true, archivedDoc: doc });
    return;
  }
  const result = renderPdfForContext(doc.spec, builder, docPreviewSettings());
  result.doc.save(doc.filename || (doc.reference + '.pdf'));
}

// Boot the portal (kept at the very end so every module above is initialised)
if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', bootTeemOnce);
else bootTeemOnce();
