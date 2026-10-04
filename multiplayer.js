// ─── YUM-CARD ONLINE MULTIPLAYER (LIVE SCORE RACE) ──────────────────────────
// Adds a "Find Match" button and a friend-code flow to yum-card so two players
// can be paired online and watch each other's grand total update live while
// each fills their own score sheet.
//
// Backend: reuses the existing yum-game Firebase Realtime Database, but under a
// dedicated `yumCard/` namespace so it never collides with the full yum game's
// rooms or matchmaking queue.
//
//   yumCard/queue/$uid   — players who tapped Find Match and are waiting
//   yumCard/offers/$uid  — pending pairing offers addressed to $uid
//   yumCard/rooms/$code  — a match: { host, createdAt, mode, players/$uid/... }
//
// Pairing mirrors the yum app's proven queue→offer→host-creates-room handshake
// (lower-UID hosts, atomic offer-slot transaction, promote fallback) trimmed for
// the two-player live-score use case. No game-engine porting: this module reads
// the local sheet's already-computed totals from the DOM and publishes them.
//
// This file is intentionally self-contained: it loads the Firebase compat SDK on
// demand, so index.html only needs one <script src="multiplayer.js"> tag.

(function () {
  'use strict';

  // ── Firebase project (shared yum-game project; these keys are public) ──────
  var firebaseConfig = {
    apiKey: "AIzaSyBl1XezlXttwyQLBsEJJV0nkxomzL0uhZw",
    authDomain: "yum-game.firebaseapp.com",
    databaseURL: "https://yum-game-default-rtdb.firebaseio.com",
    projectId: "yum-game",
    storageBucket: "yum-game.firebasestorage.app",
    messagingSenderId: "418931435506",
    appId: "1:418931435506:web:1f37261a6bf89c596b2d6b"
  };

  var SDK_VERSION = '10.12.5';
  var SDK_BASE = 'https://www.gstatic.com/firebasejs/' + SDK_VERSION + '/';
  var SDK_FILES = [
    'firebase-app-compat.js',
    'firebase-auth-compat.js',
    'firebase-database-compat.js'
  ];

  var NS      = 'yumCard';
  var QUEUE   = NS + '/queue';
  var OFFERS  = NS + '/offers';
  var ROOMS   = NS + '/rooms';

  var STALE_MS         = 90 * 1000;   // ignore queue entries older than this
  var PROMOTE_AFTER_MS = 8000;        // reversed-direction host fallback
  var OFFER_WAIT_MS    = 12000;       // free a stuck offer slot after this
  var QUEUE_LIMIT      = 30;
  var SYNC_MIN_MS      = 400;         // min gap between score pushes
  var POLL_MS          = 1500;        // fallback score poll while in a match
  var OPP_GONE_MS      = 2 * 60 * 1000; // no heartbeat for this long → stale (fallback)
  var READY_TIMEOUT_MS = 30 * 1000;   // both players must accept within this window
  // Presence uses only lastActiveAt (an existing field): the database rules
  // reject rooms/players carrying unknown keys, so nothing new is written.
  var HEARTBEAT_MS     = 10 * 1000;   // lastActiveAt ping while in a match
  var DROP_MS          = 30 * 1000;   // no ping for this long → player dropped
  var RECONNECT_MS     = 60 * 1000;   // a dropped player may come back within this
  var MATCH_KEY        = 'yum-card-mp-match'; // local record of the live match, for rejoin

  // ── Runtime state ──────────────────────────────────────────────────────────
  var db = null, auth = null, uid = null, myName = 'Player';
  var mode = 'yum';
  // The database rules may only accept the original modes. Yamio uses the
  // Yahtzee card, so if a write with mode "yamio" is denied we retry with
  // "yahtzee" on the wire and keep Yamio locally (same card; power-ups travel
  // in `cells`). Once the rules allow "yamio", no fallback is ever needed.
  var modeFallback = false;
  function wireMode() { return (mode === 'yamio' && modeFallback) ? 'yahtzee' : mode; }
  function sameCard(a, b) {
    if (a === b) return true;
    return (a === 'yahtzee' || a === 'yamio') && (b === 'yahtzee' || b === 'yamio');
  }
  function isPermErr(e) { return /permission/i.test((e && (e.code || e.message)) || ''); }
  function enableModeFallback() {
    if (mode !== 'yamio' || modeFallback) return false;
    modeFallback = true;
    console.warn('[yumcard-mp] "yamio" rejected by the database rules; using "yahtzee" on the wire');
    return true;
  }

  var mmActive = false;               // searching or in a match
  var role = null;                    // 'host' | 'guest' | null
  var inQueue = false;
  var claimInFlight = false;
  var offerSeen = false;

  var roomCode = null;
  var roomRef = null;
  var playersRef = null;
  var playersListener = null;
  var myPlayerRef = null;

  var offerRef = null;
  var offerListener = null;
  var queueRef = null;
  var queueWatcher = null;
  var promoteTimer = null;
  var offerWaitTimer = null;

  var lastPushSig = null;
  var lastPushAt = 0;
  var pushQueued = false;
  var pollTimer = null;
  var scoreObserver = null;
  var oppData = null;
  var iAmDone = false;
  var rematchVoted = false;           // I have asked to advance to the next round
  var rematchVotes = {};              // uid -> round number requested, from the room
  var roundLocal = 0;                 // rounds completed via rematch on this client
  var gameOverShown = false;
  var matchPhase = null;              // 'ready' (accept screen) | 'playing'
  var readyAccepted = false;          // I tapped Accept
  var readySawOpp = false;            // opponent has appeared in the ready phase
  var matchCanceled = false;
  var readyTimer = null;
  var readyDeadline = 0;

  // Friend invites (QR / link) stay joinable for up to 5 days: the room outlives
  // the host's session, and the host re-arms it on every app open.
  var INVITE_TTL_MS = 5 * 24 * 60 * 60 * 1000;
  var INVITE_KEY = 'yum-card-mp-invite';
  var inviteCode = null;              // code of my pending (not yet started) invite
  var heartbeatTimer = null, reconnectTimer = null;

  // ── Small helpers ───────────────────────────────────────────────────────────
  function $(id) { return document.getElementById(id); }
  function esc(s) {
    return String(s == null ? '' : s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }
  function now() { return Date.now(); }
  // Line icons (stroke = text colour) for buttons and messages — no emoji.
  var UI_ICONS = {
    search: '<circle cx="11" cy="11" r="7"/><path d="M20 20l-3.5-3.5"/>',
    plus: '<circle cx="12" cy="12" r="9"/><path d="M12 8v8M8 12h8"/>',
    link: '<path d="M10 13a5 5 0 0 0 7 0l3-3a5 5 0 0 0-7-7l-1 1"/><path d="M14 11a5 5 0 0 0-7 0l-3 3a5 5 0 0 0 7 7l1-1"/>',
    share: '<path d="M12 3v12"/><path d="M8 7l4-4 4 4"/><path d="M5 13v6a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2v-6"/>',
    copy: '<rect x="9" y="9" width="12" height="12" rx="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/>',
    dice: '<rect x="3" y="3" width="18" height="18" rx="4"/><g fill="currentColor" stroke="none"><circle cx="8" cy="8" r="1.6"/><circle cx="16" cy="8" r="1.6"/><circle cx="12" cy="12" r="1.6"/><circle cx="8" cy="16" r="1.6"/><circle cx="16" cy="16" r="1.6"/></g>',
    flag: '<path d="M5 21V4"/><path d="M5 4h11l-2 4 2 4H5"/>',
    refresh: '<path d="M20 11a8 8 0 0 0-14.5-4.5L3 9"/><path d="M3 4v5h5"/><path d="M4 13a8 8 0 0 0 14.5 4.5L21 15"/><path d="M21 20v-5h-5"/>',
    hourglass: '<path d="M7 3h10v3l-4 6 4 6v3H7v-3l4-6-4-6z"/>',
    check: '<circle cx="12" cy="12" r="9"/><path d="M8 12l3 3 5-6"/>',
    back: '<path d="M19 12H5"/><path d="M11 18l-6-6 6-6"/>',
    eye: '<path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/>',
    crown: '<path d="M3 18h18l1-11-5.5 4L12 4l-4.5 7L2 7z"/>',
    trophy: '<path d="M8 21h8M12 17v4M7 4h10v5a5 5 0 0 1-10 0z"/><path d="M7 6H4v2a3 3 0 0 0 3 3M17 6h3v2a3 3 0 0 1-3 3"/>',
    frown: '<circle cx="12" cy="12" r="9"/><path d="M9 9h.01M15 9h.01"/><path d="M16 16a4 4 0 0 0-8 0"/>',
    tie: '<circle cx="12" cy="12" r="9"/><path d="M8 10h8M8 14h8"/>',
    warn: '<path d="M12 3l10 18H2z"/><path d="M12 9v5M12 17h.01"/>',
    exit: '<path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="M16 17l5-5-5-5"/><path d="M21 12H9"/>',
    zap: '<path d="M13 2L3 14h8l-1 8 10-12h-8z"/>'
  };
  function ui(name) {
    return '<svg class="mp-ico" viewBox="0 0 24 24" aria-hidden="true">' + (UI_ICONS[name] || '') + '</svg>';
  }
  function randCode() {
    var chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // no 0/O/1/I
    var s = '';
    for (var i = 0; i < 5; i++) s += chars[Math.floor(Math.random() * chars.length)];
    return s;
  }
  function currentMode() {
    var b = document.body.classList;
    return b.contains('mode-yahtzee') ? 'yahtzee' : b.contains('mode-yamio') ? 'yamio' : 'yum';
  }
  function modeName(m) {
    return m === 'yahtzee' ? 'Yahtzee' : m === 'yamio' ? 'Yamio' : 'Yum';
  }
  function T(fr, en) {
    return document.body.classList.contains('lang-en') ? en : fr;
  }

  // ── Local score reading (no game-engine changes — read the DOM) ─────────────
  // Editable cells live in <td class="input-cell" data-cell="…">; computed
  // totals are readonly inputs. recompute() keeps #grand-c / #uTotal-c / #lTotal-c
  // in sync on every entry, so we just read them.
  var ROW_LABELS = {
    u1: '1s', u2: '2s', u3: '3s', u4: '4s', u5: '5s', u6: '6s',
    l3k: T('3 pareils', '3 of a kind'), l4k: T('4 pareils', '4 of a kind'),
    lss_yum: T('Courte séq.', 'Short straight'), lls_yum: T('Longue séq.', 'Long straight'),
    lhr: T('Surplus', 'High roll'), lfh: T('Main pleine', 'Full house'), lyum: 'YUM',
    lss_ya: T('Petite suite', 'Sm. straight'), lls_ya: T('Grande suite', 'Lg. straight'),
    lyahtzee: 'Yahtzee', lchance: T('Chance', 'Chance'), lybonus: T('Bonus Y.', 'Y. bonus')
  };
  function labelFor(rowId, m) {
    if (rowId === 'lss') return m !== 'yum' ? ROW_LABELS.lss_ya : ROW_LABELS.lss_yum;
    if (rowId === 'lls') return m !== 'yum' ? ROW_LABELS.lls_ya : ROW_LABELS.lls_yum;
    return ROW_LABELS[rowId] || rowId;
  }
  function intOf(el) {
    if (!el) return 0;
    var v = parseInt(el.tagName === 'INPUT' ? el.value : el.textContent, 10);
    return isNaN(v) ? 0 : v;
  }
  // Categories that must carry a value (0 = scratched counts) for a sheet to be
  // "complete". Yahtzee bonus (lybonus) is optional — you only fill it if you
  // actually roll extra Yahtzees — so it is excluded from the completion check.
  var REQUIRED = {
    yum: ['u1', 'u2', 'u3', 'u4', 'u5', 'u6', 'l3k', 'l4k', 'lss', 'lls', 'lhr', 'lfh', 'lyum'],
    yahtzee: ['u1', 'u2', 'u3', 'u4', 'u5', 'u6', 'l3k', 'l4k', 'lfh', 'lss', 'lls', 'lyahtzee', 'lchance']
  };
  REQUIRED.yamio = REQUIRED.yahtzee; // same card; power-ups are optional
  // All three cards (Yum, Yahtzee, Yamio) are in play at once. The card of the
  // mode currently shown is read from the DOM; the other two come from the
  // sheet storage yum-card keeps up to date on every entry. Match score = sum
  // of the three cards; `sheets` carries every editable entry of each card
  // keyed by input id ("u1-1", "l3k-4", "d1-2", …) so the opponent can mirror
  // whichever card they are looking at.
  var MODES = ['yum', 'yahtzee', 'yamio'];
  function readDomCells() {
    var cells = {};
    var inputs = document.querySelectorAll('td.input-cell[data-cell] input');
    for (var i = 0; i < inputs.length; i++) {
      var inp = inputs[i];
      if (inp.value !== '') {
        var v = parseInt(inp.value, 10);
        cells[inp.id] = isNaN(v) ? 0 : v;   // key includes the column, e.g. "u6-3"
      }
    }
    return cells;
  }
  function readStoredCells(m) {
    try {
      var n = parseInt(localStorage.getItem('yum-card-' + m + '-v2-active'), 10);
      if (!(n >= 1 && n <= 5)) n = 1;
      var raw = localStorage.getItem('yum-card-' + m + '-v2-sheet-' + n);
      var src = (raw && JSON.parse(raw).cells) || {};
      var cells = {};
      Object.keys(src).forEach(function (k) { var v = parseInt(src[k], 10); if (!isNaN(v)) cells[k] = v; });
      return cells;
    } catch (e) { return {}; }
  }
  // Totals of one card (numeric cells map) in mode m over its 6 columns.
  // "Complete" = every required category filled in every column.
  function sheetTotals(cells, m) {
    var grand = 0, upper = 0, lower = 0;
    for (var c = 1; c <= 6; c++) {
      var t = colTotals(cells, c, m);
      grand += t.grand; upper += t.upper; lower += t.lower;
    }
    var req = REQUIRED[m] || REQUIRED.yum, allFilled = true;
    for (var cc = 1; cc <= 6 && allFilled; cc++) {
      for (var r = 0; r < req.length; r++) {
        if (!cells.hasOwnProperty(req[r] + '-' + cc)) { allFilled = false; break; }
      }
    }
    return { grand: grand, upper: upper, lower: lower, allFilled: allFilled, started: Object.keys(cells).length > 0 };
  }
  function readMyScore() {
    var cur = currentMode();
    var sheets = {}, per = {};
    var grand = 0, upper = 0, lower = 0, allFilled = true;
    MODES.forEach(function (m) {
      sheets[m] = m === cur ? readDomCells() : readStoredCells(m);
      per[m] = sheetTotals(sheets[m], m);
      grand += per[m].grand; upper += per[m].upper; lower += per[m].lower;
      if (!per[m].allFilled) allFilled = false;
    });
    return { grand: grand, upper: upper, lower: lower, cells: sheets[cur], sheets: sheets, per: per, allFilled: allFilled };
  }
  // Per-mode breakdown line shown under a player's total.
  function perModeLine(per) {
    return MODES.map(function (m) { return modeName(m) + ' ' + ((per && per[m]) ? per[m].grand : 0); }).join(' · ');
  }
  function oppCells() {
    return (oppData && oppData.sheets && oppData.sheets[currentMode()]) || {};
  }
  // Clear the local player's WHOLE sheet (all columns) and persist it, without
  // reaching into the game IIFE: blank the editable cells, then poke
  // #playerName's input listener (recompute + save) so totals and localStorage
  // update. Used by the rematch flow.
  function resetMyColumn() {
    var inputs = document.querySelectorAll('td.input-cell[data-cell] input');
    for (var i = 0; i < inputs.length; i++) {
      inputs[i].value = '';
      var td = inputs[i].closest('td');
      if (td) td.classList.remove('scratched');
    }
    var pn = $('playerName');
    if (pn) { try { pn.dispatchEvent(new Event('input', { bubbles: true })); } catch (e) {} }
  }

  // ── SDK / DB / auth bootstrap ───────────────────────────────────────────────
  function loadScript(src) {
    return new Promise(function (resolve, reject) {
      var s = document.createElement('script');
      s.src = src; s.async = false;
      s.onload = resolve;
      s.onerror = function () { reject(new Error('Failed to load ' + src)); };
      document.head.appendChild(s);
    });
  }
  var sdkPromise = null;
  function ensureSdk() {
    if (window.firebase && firebase.database && firebase.auth) return Promise.resolve(true);
    if (sdkPromise) return sdkPromise;
    sdkPromise = SDK_FILES.reduce(function (p, f) {
      return p.then(function () { return loadScript(SDK_BASE + f); });
    }, Promise.resolve()).then(function () { return true; });
    return sdkPromise;
  }
  var initPromise = null;
  function ensureReady() {
    if (initPromise) return initPromise;
    initPromise = ensureSdk().then(function () {
      if (!firebase.apps || firebase.apps.length === 0) firebase.initializeApp(firebaseConfig);
      db = firebase.database();
      auth = firebase.auth();
      // Local test hook: point at the Firebase emulator when explicitly opted in
      // (no effect in production; the flag is never set on the live site).
      if (window.__YUMCARD_MP_EMULATOR__) {
        try {
          db.useEmulator('127.0.0.1', window.__YUMCARD_MP_EMULATOR__.db || 9000);
          auth.useEmulator('http://127.0.0.1:' + (window.__YUMCARD_MP_EMULATOR__.auth || 9099), { disableWarnings: true });
        } catch (e) {}
      }
      if (auth.currentUser) return auth.currentUser;
      return new Promise(function (resolve) {
        var unsub = auth.onAuthStateChanged(function (u) { unsub(); resolve(u); });
      }).then(function (u) {
        if (u) return u;
        return auth.signInAnonymously().then(function (cred) { return cred.user; });
      });
    }).then(function (user) {
      uid = user ? user.uid : null;
      return uid;
    }).catch(function (e) {
      console.warn('[yumcard-mp] init failed:', e);
      initPromise = null; // allow retry
      throw e;
    });
    return initPromise;
  }

  // ── UI: floating button + overlay panel ─────────────────────────────────────
  function injectStyles() {
    if ($('mpStyles')) return;
    var css = document.createElement('style');
    css.id = 'mpStyles';
    css.textContent = [
      '#mpFab{position:fixed;right:14px;bottom:14px;z-index:900;background:var(--green,#2f6a5a);color:#fff;border:none;border-radius:999px;padding:12px 18px;font-size:14px;font-weight:800;box-shadow:0 4px 14px rgba(0,0,0,.28);cursor:pointer;display:flex;align-items:center;gap:8px}',
      '#mpFab:active{transform:scale(.97)}',
      '.mp-ico{width:1.1em;height:1.1em;vertical-align:-.18em;margin-right:6px;display:inline-block;fill:none;stroke:currentColor;stroke-width:2;stroke-linecap:round;stroke-linejoin:round}',
      '.mp-card .crown .mp-ico{width:22px;height:22px;margin:0;fill:#f4c842;stroke:#b8860b;stroke-width:1}',
      '.mp-gameover .mp-ico{width:1.3em;height:1.3em}',
      '.mp-toast .mp-ico{width:1.1em;height:1.1em;stroke-width:2.2}',
      '#mpFab .mp-ico{margin-right:2px}',
      '.mp-live-bar .view .mp-ico{margin-right:4px;stroke-width:2.4}',
      '#mpFab .dot{width:9px;height:9px;border-radius:50%;background:#ffd24a;box-shadow:0 0 0 0 rgba(255,210,74,.7);animation:mpPulse 1.8s infinite}',
      '@keyframes mpPulse{0%{box-shadow:0 0 0 0 rgba(255,210,74,.6)}70%{box-shadow:0 0 0 8px rgba(255,210,74,0)}100%{box-shadow:0 0 0 0 rgba(255,210,74,0)}}',
      '.mp-backdrop{position:fixed;inset:0;z-index:1000;background:rgba(20,30,26,.55);display:none;align-items:flex-end;justify-content:center}',
      '.mp-backdrop.show{display:flex}',
      '@media(min-width:560px){.mp-backdrop{align-items:center}}',
      '.mp-sheet{background:var(--paper,#fbfaf3);width:100%;max-width:480px;border-radius:18px 18px 0 0;padding:18px 16px calc(18px + env(safe-area-inset-bottom));box-shadow:0 -6px 30px rgba(0,0,0,.3);max-height:92vh;overflow:auto}',
      '@media(min-width:560px){.mp-sheet{border-radius:18px}}',
      '.mp-sheet h2{margin:0 0 2px;font-size:19px;color:var(--green-dark,#235244);display:flex;align-items:center;justify-content:space-between}',
      '.mp-close{background:none;border:none;font-size:24px;line-height:1;color:#789;cursor:pointer;padding:2px 6px}',
      '.mp-sub{font-size:12.5px;color:#5a6b64;margin:0 0 14px}',
      '.mp-btn{display:block;width:100%;box-sizing:border-box;border:none;border-radius:12px;padding:14px;font-size:15px;font-weight:800;cursor:pointer;margin-top:10px}',
      '.mp-btn.primary{background:var(--green,#2f6a5a);color:#fff}',
      '.mp-btn.accent{background:var(--yellow,#f4c842);color:var(--green-dark,#235244)}',
      '.mp-btn.ghost{background:var(--green-light,#c3dcd2);color:var(--green-dark,#235244)}',
      '.mp-btn.danger{background:#c8443c;color:#fff}',
      '.mp-btn:disabled{opacity:.55;cursor:default}',
      '.mp-btn:active{transform:scale(.99)}',
      '.mp-row{display:flex;gap:8px;align-items:center;margin-top:10px}',
      '.mp-row input{flex:1;min-width:0;box-sizing:border-box;border:2px solid var(--green,#2f6a5a);border-radius:10px;padding:12px;font-size:16px;background:#fff;color:#123}',
      '#mpCodeInput{text-transform:uppercase;letter-spacing:2px;font-weight:800}',
      '.mp-divider{display:flex;align-items:center;gap:10px;color:#8a978f;font-size:11px;font-weight:800;margin:16px 0 4px}',
      '.mp-divider::before,.mp-divider::after{content:"";flex:1;height:1px;background:#d5ded8}',
      '.mp-field{margin-top:6px}',
      '.mp-field label{font-size:11px;font-weight:800;color:#5a6b64;text-transform:uppercase;letter-spacing:.5px}',
      '.mp-colsel{display:flex;gap:6px;margin-top:6px}',
      '.mp-colsel button{flex:1;border:2px solid var(--green-light,#c3dcd2);background:#fff;border-radius:9px;padding:9px 0;font-weight:800;color:var(--green-dark,#235244);cursor:pointer}',
      '.mp-colsel button.on{background:var(--green,#2f6a5a);color:#fff;border-color:var(--green,#2f6a5a)}',
      '.mp-note{font-size:11.5px;color:#7a877f;margin-top:12px;line-height:1.4}',
      '.mp-err{background:#fbe3e1;color:#9a2b23;border-radius:10px;padding:10px;font-size:12.5px;margin-top:10px;display:none}',
      '.mp-err.show{display:block}',
      '.mp-spin{width:34px;height:34px;border:4px solid var(--green-light,#c3dcd2);border-top-color:var(--green,#2f6a5a);border-radius:50%;animation:mpSpin 1s linear infinite;margin:14px auto}',
      '@keyframes mpSpin{to{transform:rotate(360deg)}}',
      '.mp-center{text-align:center}',
      '.mp-code-big{font-size:34px;font-weight:900;letter-spacing:6px;color:var(--green-dark,#235244);text-align:center;background:var(--green-light,#c3dcd2);border-radius:12px;padding:14px;margin:12px 0}',
      '.mp-gameover{display:none}',
      '.mp-gameover.show{display:block;text-align:center;font-size:17px;font-weight:900;border-radius:12px;padding:12px;margin:2px 0 8px;animation:mpPop .3s ease}',
      '.mp-gameover.win{background:#bfe6cf;color:#1c6b3f}',
      '.mp-gameover.lose{background:#f6e0de;color:#9a2b23}',
      '.mp-gameover.tie{background:var(--yellow-light,#fbe9a8);color:var(--green-dark,#235244)}',
      '@keyframes mpPop{0%{transform:scale(.9);opacity:0}100%{transform:scale(1);opacity:1}}',
      // scoreboard
      '.mp-vs{display:grid;grid-template-columns:1fr auto 1fr;gap:10px;align-items:stretch;margin-top:6px}',
      '.mp-card{background:#fff;border:2px solid var(--green-light,#c3dcd2);border-radius:14px;padding:12px 10px;text-align:center;position:relative}',
      '.mp-card.lead{border-color:var(--yellow,#f4c842);box-shadow:0 0 0 3px rgba(244,200,66,.35)}',
      '.mp-card .who{font-size:12px;font-weight:800;color:#5a6b64;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
      '.mp-card .tot{font-size:40px;font-weight:900;color:var(--green-dark,#235244);line-height:1.05;margin:4px 0}',
      '.mp-card .sub{font-size:11px;color:#7a877f}',
      '.mp-card .crown{position:absolute;top:-12px;left:50%;transform:translateX(-50%);font-size:18px}',
      '.mp-card .badge{display:inline-block;margin-top:6px;font-size:10px;font-weight:800;padding:2px 8px;border-radius:999px;background:var(--green-light,#c3dcd2);color:var(--green-dark,#235244)}',
      '.mp-card .badge.done{background:#bfe6cf;color:#1c6b3f}',
      '.mp-vs .mid{align-self:center;font-weight:900;color:#8a978f;font-size:13px}',
      '.mp-diff{text-align:center;font-size:12.5px;font-weight:700;color:#5a6b64;margin-top:10px;min-height:16px}',
      '.mp-details{margin-top:12px;border-top:1px solid #e2e9e4;padding-top:8px;display:none}',
      '.mp-details.show{display:block}',
      // opponent full-sheet mirror (6 columns)
      '.mp-sheet-scroll{overflow-x:auto;-webkit-overflow-scrolling:touch;border:1px solid #e2e9e4;border-radius:10px}',
      '.mp-mini{border-collapse:collapse;font-size:12px;width:100%;min-width:320px}',
      '.mp-mini th,.mp-mini td{padding:5px 4px;text-align:center;border-bottom:1px solid #eef2ef;border-right:1px solid #f0f4f1;color:#33443d;min-width:30px}',
      '.mp-mini thead th{background:var(--green,#2f6a5a);color:#fff;font-weight:800;position:sticky;top:0}',
      '.mp-mini th.cat,.mp-mini td.cat{text-align:left;font-weight:700;color:#5a6b64;white-space:nowrap;position:sticky;left:0;background:var(--paper,#fbfaf3);min-width:78px;box-shadow:1px 0 0 #e2e9e4}',
      '.mp-mini thead th.cat{background:var(--green,#2f6a5a)}',
      '.mp-mini tr.sum td{background:var(--yellow-light,#fbe9a8);font-weight:700}',
      '.mp-mini tr.sum td.cat{background:var(--yellow-light,#fbe9a8);color:var(--green-dark,#235244)}',
      '.mp-mini tr.grand td{background:var(--green-row,#d8e8e0);font-weight:900;color:var(--green-dark,#235244)}',
      '.mp-mini tr.grand td.cat{background:var(--green-row,#d8e8e0)}',
      '.mp-mini .sx{color:#c05a52;font-weight:800}',
      '.mp-mini .pw-ico{width:15px;height:15px;vertical-align:middle;display:inline-block}',
      '.mp-sheet-cap{text-align:center;font-size:12px;font-weight:800;color:var(--green-dark,#235244);margin-top:6px}',
      '.mp-sheet-empty{text-align:center;color:#7a877f;font-size:12.5px;padding:10px}',
      '.mp-toggle{background:none;border:none;color:var(--green,#2f6a5a);font-weight:800;font-size:12.5px;cursor:pointer;margin-top:8px;padding:4px}',
      '.mp-status{font-size:12.5px;color:#5a6b64;text-align:center;margin:8px 0 2px;min-height:16px}',
      // ready-check
      '.mp-ready{display:grid;grid-template-columns:1fr auto 1fr;gap:10px;align-items:center;margin:10px 0 6px}',
      '.mp-rc{background:#fff;border:2px solid var(--green-light,#c3dcd2);border-radius:14px;padding:14px 8px;text-align:center}',
      '.mp-rc .who{font-size:13px;font-weight:800;color:#5a6b64;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
      '.mp-rc .chip{margin-top:8px;font-size:11px;font-weight:800;padding:4px 10px;border-radius:999px;display:inline-block;background:#f0e6c9;color:#8a6d1e}',
      '.mp-rc .chip.ready{background:#bfe6cf;color:#1c6b3f}',
      '.mp-ready .mp-rc-vs{font-weight:900;color:#8a978f;font-size:13px}',
      '.mp-ready-count{text-align:center;font-size:13px;font-weight:700;color:#5a6b64;margin:4px 0 8px}',
      '.mp-ready-count span{color:var(--green-dark,#235244);font-weight:900}',
      // live score bar (between toolbar and sheet while a match is on)
      '.mp-live-bar{display:none;max-width:980px;margin:12px auto 0;padding:8px 12px;background:var(--green-dark,#235244);color:#fff;border-radius:10px;align-items:center;gap:10px;cursor:pointer;box-shadow:0 4px 12px rgba(0,0,0,.3);font-size:14px;-webkit-tap-highlight-color:transparent}',
      '.mp-live-bar.show{display:flex}',
      '.mp-live-bar .side{flex:1;min-width:0;display:flex;align-items:center;gap:8px}',
      '.mp-live-bar .side.opp{justify-content:flex-end}',
      '.mp-live-bar .nm{font-weight:700;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;opacity:.9}',
      '.mp-live-bar .sc{font-size:22px;font-weight:900;line-height:1}',
      '.mp-live-bar .sc.lead{color:var(--yellow,#f4c842)}',
      '.mp-live-bar .vs{font-size:11px;font-weight:900;opacity:.6}',
      '.mp-live-bar .view{background:var(--yellow,#f4c842);color:var(--green-dark,#235244);border:none;border-radius:999px;padding:7px 12px;font-weight:800;font-size:12px;cursor:pointer;white-space:nowrap}',
      '.mp-live-bar .view:active{transform:scale(.97)}',
      '@media(max-width:640px){.mp-live-bar{margin:8px 8px 0}}',
      // QR invite
      '.mp-qr{display:flex;justify-content:center;align-items:center;min-height:120px;margin:12px 0 4px}',
      '.mp-qr svg{width:210px;height:210px;background:#fff;padding:8px;border-radius:12px;border:2px solid var(--green-light,#c3dcd2);box-sizing:border-box}',
      // "match started" popup
      '.mp-toast{position:fixed;left:50%;top:38%;transform:translate(-50%,-50%) scale(.85);z-index:1100;background:var(--green-dark,#235244);color:#fff;padding:20px 26px;border-radius:18px;box-shadow:0 14px 40px rgba(0,0,0,.45);text-align:center;min-width:240px;max-width:88vw;opacity:0;pointer-events:none;transition:opacity .25s ease,transform .25s ease;border:3px solid var(--yellow,#f4c842)}',
      '.mp-toast.show{opacity:1;transform:translate(-50%,-50%) scale(1)}',
      '.mp-toast .big{font-size:24px;font-weight:900;letter-spacing:.3px}',
      '.mp-toast .sub{font-size:14px;opacity:.9;margin-top:6px;font-weight:700}',
      '.mp-toast.warn{border-color:#c8443c}',
      // win probability
      '.mp-win{margin-top:10px}',
      '.mp-win-label{font-size:11px;font-weight:800;color:#5a6b64;text-align:center;text-transform:uppercase;letter-spacing:.5px}',
      '.mp-win-bar{height:16px;border-radius:999px;background:#e9c6c2;overflow:hidden;margin:6px 0 4px;border:1px solid #d5ded8}',
      '.mp-win-bar .me{height:100%;background:var(--green,#2f6a5a);transition:width .35s ease}',
      '.mp-win-nums{display:flex;justify-content:space-between;font-size:13px;font-weight:900}',
      '.mp-win-nums .a{color:var(--green-dark,#235244)}',
      '.mp-win-nums .b{color:#9a2b23}',
      '.mp-win-hint{font-size:10.5px;color:#8a978f;text-align:center;margin-top:2px}'
    ].join('\n');
    document.head.appendChild(css);
  }

  function buildDom() {
    if ($('mpFab')) return;
    injectStyles();

    var fab = document.createElement('button');
    fab.id = 'mpFab';
    fab.type = 'button';
    fab.innerHTML = '<span class="dot"></span><span id="mpFabLabel">' + T('Multijoueur', 'Multiplayer') + '</span>';
    fab.addEventListener('click', openPanel);
    document.body.appendChild(fab);

    var back = document.createElement('div');
    back.className = 'mp-backdrop';
    back.id = 'mpBackdrop';
    back.innerHTML = '<div class="mp-sheet" id="mpSheet" role="dialog" aria-modal="true"></div>';
    back.addEventListener('click', function (e) { if (e.target === back) closePanel(); });
    document.body.appendChild(back);
    buildLiveBar();
  }

  // Live score bar: sits between the toolbar and the sheet while a match is on,
  // mirrors both totals in real time, and opens the opponent's full card on tap.
  function buildLiveBar() {
    if ($('mpLiveBar')) return;
    var bar = document.createElement('div');
    bar.id = 'mpLiveBar';
    bar.className = 'mp-live-bar';
    bar.setAttribute('role', 'button');
    bar.innerHTML =
      '<div class="side me" id="mpLiveMe"></div>' +
      '<div class="vs">VS</div>' +
      '<div class="side opp" id="mpLiveOpp"></div>' +
      '<button type="button" class="view" id="mpLiveView"></button>';
    bar.addEventListener('click', openOpponentSheet);
    var card = $('card');
    if (card && card.parentNode) card.parentNode.insertBefore(bar, card);
    else document.body.appendChild(bar);
  }
  function updateLiveBar() {
    var bar = $('mpLiveBar');
    if (!bar) return;
    var live = mmActive && matchPhase === 'playing' && oppData && !oppData.gone;
    bar.classList.toggle('show', !!live);
    if (!live) return;
    var me = readMyScore();
    var og = oppData.grand || 0;
    $('mpLiveMe').innerHTML =
      '<span class="nm">' + esc(myName) + '</span>' +
      '<span class="sc' + (me.grand > og ? ' lead' : '') + '">' + me.grand + '</span>';
    $('mpLiveOpp').innerHTML =
      '<span class="sc' + (og > me.grand ? ' lead' : '') + '">' + og + '</span>' +
      '<span class="nm">' + esc(oppData.name || T('Adversaire', 'Opponent')) + '</span>';
    $('mpLiveView').innerHTML = oppData.disconnected
      ? ui('hourglass') + T('Reconnexion ', 'Reconnecting ') + reconnectLeftSec() + ' s'
      : ui('eye') + T('Voir sa carte', 'View their card');
  }
  function openOpponentSheet() {
    detailsOpen = true;
    openPanel();
    var d = $('mpDetails');
    if (d) {
      d.classList.add('show');
      try { d.scrollIntoView({ block: 'nearest' }); } catch (e) {}
    }
  }

  function openPanel() {
    buildDom();
    $('mpBackdrop').classList.add('show');
    if (mmActive && roomCode && matchPhase === 'playing') renderMatch();
    else if (mmActive && roomCode && matchPhase === 'ready' && oppData && !oppData.gone) renderReady();
    else if (mmActive && roomCode && inviteCode === roomCode && role === 'host') renderWaitingCode(roomCode);
    else if (mmActive && roomCode && role === 'guest') renderSearching(hostOfflineText());
    else if (mmActive && roomCode) renderSearching(T('En attente de l\'adversaire…', 'Waiting for opponent…'));
    else renderLobby();
  }
  function hostOfflineText() {
    return T('L\'hôte n\'est pas en ligne. La partie démarrera dès qu\'il ouvrira l\'app…',
             'The host isn\'t online. The match starts as soon as they open the app…');
  }
  function closePanel() {
    var b = $('mpBackdrop');
    if (b) b.classList.remove('show');
  }

  function nameFromSheet() {
    var el = $('playerName');
    var n = el && el.value ? el.value.trim() : '';
    return n || T('Joueur', 'Player');
  }

  // ── Lobby view ──────────────────────────────────────────────────────────────
  function renderLobby() {
    var s = $('mpSheet');
    if (!s) return;
    myName = nameFromSheet();
    s.innerHTML =
      '<h2>' + T('Jouer en ligne', 'Play online') +
        '<button class="mp-close" id="mpCloseBtn" aria-label="Close">×</button></h2>' +
      '<p class="mp-sub">' + T('Affronte un adversaire et voyez vos feuilles en direct. Les 3 cartes (Yum, Yahtzee, Yamio) comptent — change de mode quand tu veux.',
                               'Race an opponent and watch each other\'s sheet live. All 3 cards (Yum, Yahtzee, Yamio) count — switch mode any time.') + '</p>' +
      '<div class="mp-field"><label>' + T('Ton nom', 'Your name') + '</label>' +
        '<div class="mp-row"><input id="mpName" type="text" maxlength="14" value="' + esc(myName) + '" placeholder="' + T('Joueur', 'Player') + '"></div></div>' +
      '<button class="mp-btn primary" id="mpFindBtn">' + ui('search') + T('Trouver un adversaire', 'Find a match') + '</button>' +
      '<div class="mp-divider">' + T('OU', 'OR') + '</div>' +
      '<button class="mp-btn accent" id="mpCreateBtn">' + ui('plus') + T('Créer un code d\'ami', 'Create a friend code') + '</button>' +
      '<div class="mp-row"><input id="mpCodeInput" type="text" maxlength="5" placeholder="' + T('CODE', 'CODE') + '" autocomplete="off">' +
        '<button class="mp-btn ghost" id="mpJoinBtn" style="width:auto;margin-top:0;padding:12px 16px">' + T('Rejoindre', 'Join') + '</button></div>' +
      '<div class="mp-err" id="mpErr"></div>' +
      '<p class="mp-note">' + T('Astuce : chaque joueur remplit sa propre feuille (6 colonnes). Le total, c\'est la somme des 6 colonnes, comme sur la fiche. Tu peux voir la feuille complète de l\'adversaire en direct.',
                                'Tip: each player fills their own sheet (6 columns). Your score is the sum of all 6 columns, like on the sheet. You can watch your opponent\'s full sheet live.') + '</p>';

    $('mpCloseBtn').addEventListener('click', closePanel);
    $('mpName').addEventListener('input', function () { myName = this.value.trim() || T('Joueur', 'Player'); });
    $('mpFindBtn').addEventListener('click', function () { startFind(); });
    $('mpCreateBtn').addEventListener('click', function () { startCreateCode(); });
    $('mpJoinBtn').addEventListener('click', function () {
      var v = ($('mpCodeInput').value || '').trim().toUpperCase();
      if (v) startJoinCode(v);
    });
  }

  function showErr(msg) {
    var e = $('mpErr');
    if (e) { e.textContent = msg; e.classList.add('show'); }
  }
  function clearErr() {
    var e = $('mpErr');
    if (e) { e.classList.remove('show'); e.textContent = ''; }
  }

  // ── Searching view ──────────────────────────────────────────────────────────
  function renderSearching(text) {
    var s = $('mpSheet');
    if (!s) return;
    s.innerHTML =
      '<h2>' + T('Recherche…', 'Searching…') +
        '<button class="mp-close" id="mpCloseBtn">×</button></h2>' +
      '<div class="mp-center"><div class="mp-spin"></div>' +
      '<div class="mp-status" id="mpSearchText">' + esc(text || T('Recherche d\'un adversaire…', 'Looking for an opponent…')) + '</div></div>' +
      '<button class="mp-btn danger" id="mpCancelBtn">' + T('Annuler', 'Cancel') + '</button>';
    $('mpCloseBtn').addEventListener('click', closePanel);
    $('mpCancelBtn').addEventListener('click', function () { leaveAll(true); renderLobby(); });
  }

  function joinUrl(code) {
    return location.origin + location.pathname + '#join=' + code;
  }
  function renderWaitingCode(code) {
    var s = $('mpSheet');
    if (!s) return;
    var exp = inviteExpiresAt();
    var locale = document.body.classList.contains('lang-en') ? 'en-CA' : 'fr-CA';
    var expTxt = '';
    if (exp) { try { expTxt = new Date(exp).toLocaleDateString(locale, { weekday: 'short', day: 'numeric', month: 'short' }); } catch (e) {} }
    var canShare = typeof navigator.share === 'function';
    s.innerHTML =
      '<h2>' + T('Code d\'ami', 'Friend code') +
        '<button class="mp-close" id="mpCloseBtn">×</button></h2>' +
      '<p class="mp-sub">' + T('Fais scanner ce code QR ou partage le lien. L\'invitation est valide 5 jours : la partie démarre quand ton ami rejoint et que vous êtes tous les deux en ligne.',
                               'Have your friend scan this QR code or share the link. The invite is valid for 5 days: the match starts once your friend joins and you are both online.') + '</p>' +
      '<div class="mp-qr" id="mpQr"><div class="mp-spin"></div></div>' +
      '<div class="mp-code-big" id="mpBigCode">' + esc(code) + '</div>' +
      '<button class="mp-btn accent" id="mpCopyLinkBtn">' + ui('link') + T('Copier le lien', 'Copy link') + '</button>' +
      (canShare ? '<button class="mp-btn ghost" id="mpShareBtn">' + ui('share') + T('Partager l\'invitation', 'Share invite') + '</button>' : '') +
      '<button class="mp-btn ghost" id="mpCopyBtn">' + ui('copy') + T('Copier le code', 'Copy code') + '</button>' +
      '<div class="mp-err" id="mpErr"></div>' +
      '<div class="mp-center"><div class="mp-status">' + T('En attente de l\'adversaire…', 'Waiting for opponent…') +
        (expTxt ? '<br>' + T('Expire ', 'Expires ') + esc(expTxt) : '') + '</div></div>' +
      '<button class="mp-btn danger" id="mpCancelBtn">' + T('Annuler l\'invitation', 'Cancel invite') + '</button>';
    $('mpCloseBtn').addEventListener('click', closePanel);
    var url = joinUrl(code);
    function copy(text, btn) {
      var p = (navigator.clipboard && navigator.clipboard.writeText)
        ? navigator.clipboard.writeText(text) : Promise.reject(new Error('clipboard'));
      p.then(function () {
        var old = btn.innerHTML;
        btn.innerHTML = ui('check') + T('Copié', 'Copied');
        setTimeout(function () { btn.innerHTML = old; }, 1600);
      }).catch(function () { window.prompt(T('Copie ce texte :', 'Copy this text:'), text); });
    }
    $('mpCopyLinkBtn').addEventListener('click', function () { copy(url, this); });
    $('mpCopyBtn').addEventListener('click', function () { copy(code, this); });
    if (canShare) $('mpShareBtn').addEventListener('click', function () {
      navigator.share({
        title: 'Yum',
        text: T('Rejoins ma partie de Yum ! Code : ', 'Join my Yum match! Code: ') + code,
        url: url
      }).catch(function () {});
    });
    $('mpCancelBtn').addEventListener('click', cancelInvite);
    renderQr(url);
  }
  var qrPromise = null;
  function renderQr(text) {
    if (!qrPromise) {
      qrPromise = (window.qrcode ? Promise.resolve() : loadScript('qr.js'))
        .catch(function (e) { qrPromise = null; throw e; });
    }
    qrPromise.then(function () {
      var box = $('mpQr');
      if (!box || !window.qrcode) return;
      var qr = window.qrcode(0, 'M');
      qr.addData(text);
      qr.make();
      box.innerHTML = qr.createSvgTag({ cellSize: 4, margin: 2 });
    }).catch(function () {
      var box = $('mpQr');
      if (box) box.innerHTML = '<div class="mp-sheet-empty">' + esc(text) + '</div>';
    });
  }

  // ── Pending invite persistence (host side) ──────────────────────────────────
  function readInvite() {
    try { var v = JSON.parse(localStorage.getItem(INVITE_KEY)); return (v && v.code) ? v : null; }
    catch (e) { return null; }
  }
  function setInvite(code) {
    inviteCode = code;
    try { localStorage.setItem(INVITE_KEY, JSON.stringify({ code: code, createdAt: now(), mode: mode })); } catch (e) {}
  }
  function forgetInvite() {
    inviteCode = null;
    try { localStorage.removeItem(INVITE_KEY); } catch (e) {}
  }
  function roomExpired(room) {
    return !!(room && room.createdAt && now() - room.createdAt > INVITE_TTL_MS);
  }
  function inviteExpiresAt() {
    var v = readInvite();
    return v ? (v.createdAt || now()) + INVITE_TTL_MS : 0;
  }
  function cancelInvite() {
    var code = inviteCode || roomCode;
    forgetInvite();
    if (db && code) db.ref(ROOMS + '/' + code).remove().catch(function () {});
    leaveAll(true);
    renderLobby();
  }
  // Re-attach to my pending invite room so a friend can reach me whenever the app
  // is open. Called on boot, and after a guest declined / timed out (which tears
  // the room listener down through cancelMatch). Also clears any stale status.
  function resumeInvite(errMsg) {
    var v = readInvite();
    if (!v || mmActive) return;
    if (now() > (v.createdAt || 0) + INVITE_TTL_MS) {
      forgetInvite();
      ensureReady().then(function () { db.ref(ROOMS + '/' + v.code).remove().catch(function () {}); }).catch(function () {});
      return;
    }
    inviteCode = v.code;
    ensureReady().then(function (u) {
      if (!u) throw new Error('auth');
      var ref = db.ref(ROOMS + '/' + v.code);
      return ref.once('value').then(function (snap) {
        var room = snap.val();
        if (!room || room.host !== uid || roomExpired(room)) { forgetInvite(); return; }
        if (mmActive) return;
        myName = nameFromSheet(); mode = room.mode || currentMode();
        mmActive = true; role = 'host'; iAmDone = false; oppData = null;
        if (room.status) ref.child('status').remove().catch(function () {});
        return ref.child('players/' + uid).set(makeSelfPlayer()[uid]).then(function () {
          attachRoom(v.code);
          updateFabState();
          var b = $('mpBackdrop');
          if (b && b.classList.contains('show')) { renderWaitingCode(v.code); if (errMsg) showErr(errMsg); }
        });
      });
    }).catch(function (e) {
      console.warn('[yumcard-mp] resume invite failed:', e);
      mmActive = false; role = null;
    });
  }

  // ── Match / scoreboard view ─────────────────────────────────────────────────
  var detailsOpen = true;
  function detailsToggleLabel() {
    return detailsOpen
      ? T('Masquer la feuille', 'Hide sheet')
      : T('Voir la feuille de l\'adversaire (6 colonnes)', 'Show opponent\'s full sheet (6 columns)');
  }
  function renderMatch() {
    var s = $('mpSheet');
    if (!s) return;
    s.innerHTML =
      '<h2><span id="mpMatchTitle">' + T('Partie en direct', 'Live match') + '</span>' +
        '<button class="mp-close" id="mpCloseBtn">×</button></h2>' +
      '<div class="mp-gameover" id="mpGameOver"></div>' +
      '<div class="mp-status" id="mpMatchStatus"></div>' +
      '<div class="mp-vs" id="mpVs"></div>' +
      '<div class="mp-diff" id="mpDiff"></div>' +
      '<div class="mp-win" id="mpWin"></div>' +
      '<button class="mp-toggle" id="mpDetailsToggle">' + detailsToggleLabel() + '</button>' +
      '<div class="mp-details" id="mpDetails"></div>' +
      '<button class="mp-btn primary" id="mpBackBtn">' + ui('back') + T('Retour à ma carte', 'Back to my card') + '</button>' +
      '<button class="mp-btn primary" id="mpRematchBtn" style="display:none"></button>' +
      '<button class="mp-btn accent" id="mpDoneBtn"></button>' +
      '<button class="mp-btn ghost" id="mpNewBtn">' + ui('search') + T('Nouvel adversaire', 'New opponent') + '</button>' +
      '<button class="mp-btn danger" id="mpLeaveBtn">' + T('Quitter', 'Leave') + '</button>';
    $('mpCloseBtn').addEventListener('click', closePanel);
    $('mpDetailsToggle').addEventListener('click', function () {
      detailsOpen = !detailsOpen;
      $('mpDetails').classList.toggle('show', detailsOpen);
      this.textContent = detailsToggleLabel();
      paintScoreboard();
    });
    $('mpBackBtn').addEventListener('click', closePanel);
    $('mpDetails').addEventListener('click', function (e) {
      var b = e.target.closest('[data-mp-mode]');
      if (!b) return;
      var t = document.querySelector('#modeToggle [data-mode="' + b.getAttribute('data-mp-mode') + '"]');
      if (t) t.click();   // the sheet switches; the modeToggle listener repaints us
    });
    $('mpRematchBtn').addEventListener('click', function () { requestRematch(); });
    $('mpDoneBtn').addEventListener('click', function () { toggleDone(); });
    $('mpNewBtn').addEventListener('click', function () { leaveAll(true); startFind(); });
    $('mpLeaveBtn').addEventListener('click', function () { leaveAll(true); renderLobby(); });
    if (detailsOpen) $('mpDetails').classList.add('show');
    paintScoreboard();
  }

  function paintScoreboard() {
    if (!$('mpVs')) return;
    var me = readMyScore();
    var opp = oppData;
    var meLead = opp && me.grand > opp.grand;
    var oppLead = opp && opp.grand > me.grand;

    var meCard =
      '<div class="mp-card' + (meLead ? ' lead' : '') + '">' +
        (meLead ? '<span class="crown">' + ui('crown') + '</span>' : '') +
        '<div class="who">' + esc(myName) + ' (' + T('toi', 'you') + ')</div>' +
        '<div class="tot">' + me.grand + '</div>' +
        '<div class="sub">' + perModeLine(me.per) + '</div>' +
        (iAmDone ? '<span class="badge done">' + ui('check') + T('Terminé', 'Done') + '</span>' : '') +
      '</div>';

    var oppCard;
    if (opp) {
      oppCard =
        '<div class="mp-card' + (oppLead ? ' lead' : '') + '">' +
          (oppLead ? '<span class="crown">' + ui('crown') + '</span>' : '') +
          '<div class="who">' + esc(opp.name || T('Adversaire', 'Opponent')) + '</div>' +
          '<div class="tot">' + (opp.grand || 0) + '</div>' +
          '<div class="sub">' + perModeLine(opp.per) + '</div>' +
          ((opp.done || opp.filledAll) ? '<span class="badge done">' + ui('check') + T('Terminé', 'Done') + '</span>' : '') +
        '</div>';
    } else {
      oppCard =
        '<div class="mp-card"><div class="who">' + T('Adversaire', 'Opponent') + '</div>' +
        '<div class="tot" style="color:#c3dcd2">—</div>' +
        '<div class="sub">' + T('En attente…', 'Waiting…') + '</div></div>';
    }

    $('mpVs').innerHTML = meCard + '<div class="mid">VS</div>' + oppCard;

    var diff = $('mpDiff');
    if (opp) {
      var d = me.grand - (opp.grand || 0);
      if (d > 0) diff.textContent = T('Tu mènes de ', 'You lead by ') + d;
      else if (d < 0) diff.textContent = T('Tu es derrière de ', 'You trail by ') + (-d);
      else diff.textContent = T('Égalité !', 'Tied!');
    } else diff.textContent = '';

    var over = bothFinished();
    paintWin(me, opp, over);
    var banner = $('mpGameOver');
    if (banner) {
      if (over) {
        var iWin = me.grand > (opp.grand || 0);
        var tie = me.grand === (opp.grand || 0);
        banner.className = 'mp-gameover show ' + (tie ? 'tie' : (iWin ? 'win' : 'lose'));
        banner.innerHTML = tie
          ? ui('tie') + T('Match nul ! ', 'It\'s a tie! ') + me.grand + ' – ' + (opp.grand || 0)
          : (iWin
              ? ui('trophy') + T('Tu gagnes ', 'You win ') + me.grand + ' – ' + (opp.grand || 0) + ' !'
              : ui('frown') + T('Tu perds ', 'You lose ') + me.grand + ' – ' + (opp.grand || 0));
      } else {
        banner.className = 'mp-gameover';
        banner.innerHTML = '';
      }
    }

    var status = $('mpMatchStatus');
    if (status) {
      if (over) {
        status.textContent = '';
      } else if (opp && opp.disconnected) {
        var secs = reconnectLeftSec();
        status.textContent = T((opp.name || 'L\'adversaire') + ' s\'est déconnecté — reconnexion possible encore ' + secs + ' s.',
                               (opp.name || 'Your opponent') + ' disconnected — may reconnect for another ' + secs + ' s.');
      } else if (opp && opp.gone) {
        status.textContent = T('L\'adversaire s\'est déconnecté.', 'Opponent disconnected.');
      } else if (!opp) {
        status.textContent = T('En attente de l\'adversaire…', 'Waiting for opponent to join…');
      } else if (opp && (opp.done || opp.filledAll) && !(iAmDone || me.allFilled)) {
        status.textContent = T('Ton adversaire a terminé. Finis ta feuille !', 'Your opponent finished. Complete your sheet!');
      } else {
        status.textContent = '';
      }
    }

    var doneBtn = $('mpDoneBtn');
    if (doneBtn) {
      doneBtn.style.display = (over || me.allFilled) ? 'none' : 'block';
      doneBtn.innerHTML = iAmDone
        ? T('Annuler « Terminé »', 'Undo "Done"')
        : ui('flag') + T('J\'ai terminé', 'I\'m done');
    }

    // Rematch: offered once there is a live opponent; prominent at game over.
    var reBtn = $('mpRematchBtn');
    if (reBtn) {
      var oppPresent = opp && !opp.gone;
      var myPending = (rematchVotes[uid] || 0) > roundLocal;
      var theirPending = theirVoteValue() > roundLocal;
      // Only offer a rematch once the game is over (or when the opponent asks).
      if (!oppPresent || (!over && !theirPending && !rematchVoted && !myPending)) {
        reBtn.style.display = 'none';
      } else if (rematchVoted || myPending) {
        reBtn.style.display = 'block';
        reBtn.disabled = true;
        reBtn.innerHTML = ui('hourglass') + T('En attente de l\'adversaire…', 'Waiting for opponent…');
      } else if (theirPending) {
        reBtn.style.display = 'block';
        reBtn.disabled = false;
        reBtn.innerHTML = ui('refresh') + T('L\'adversaire veut rejouer — accepter', 'Opponent wants a rematch — accept');
      } else {
        reBtn.style.display = 'block';
        reBtn.disabled = false;
        reBtn.innerHTML = ui('refresh') + T('Revanche (même adversaire)', 'Rematch (same opponent)');
      }
    }

    var newBtn = $('mpNewBtn');
    if (newBtn) newBtn.style.display = over ? 'block' : 'none';

    if (detailsOpen) paintDetails(me, opp);
  }

  // ── Win probability ─────────────────────────────────────────────────────────
  // Each unfilled category contributes its long-run average (and spread) for a
  // player rolling three times for that category; the 63 bonus is added with
  // its probability. The two projected totals are compared with a normal
  // approximation. Rough, but it moves sensibly as sheets fill up.
  var CAT_EV = {
    u1: [2.1, 1.3], u2: [4.2, 2.6], u3: [6.3, 3.9], u4: [8.4, 5.2], u5: [10.5, 6.5], u6: [12.6, 7.8],
    l3k: [15.2, 8.0], l4k: [8.5, 10.0], lfh: [9.2, 12.1], lchance: [22.5, 4.0],
    lss_ya: [18.5, 14.6], lls_ya: [10.6, 17.7], lyahtzee: [2.3, 10.5],
    lss_yum: [9.2, 7.3], lls_yum: [5.3, 8.8], lhr: [22.5, 4.0], lyum: [1.4, 6.3]
  };
  function catEv(rid, m) {
    if (rid === 'lss') return CAT_EV[m === 'yum' ? 'lss_yum' : 'lss_ya'];
    if (rid === 'lls') return CAT_EV[m === 'yum' ? 'lls_yum' : 'lls_ya'];
    return CAT_EV[rid] || [0, 0];
  }
  function normCdf(z) {
    var t = 1 / (1 + 0.2316419 * Math.abs(z));
    var d = 0.3989423 * Math.exp(-z * z / 2);
    var p = d * t * (0.3193815 + t * (-0.3565638 + t * (1.781478 + t * (-1.821256 + t * 1.330274))));
    return z >= 0 ? 1 - p : p;
  }
  function projectSheet(cells, m) {
    var B = m === 'yum' ? 25 : 35;
    var mean = 0, variance = 0;
    for (var c = 1; c <= 6; c++) {
      // upper section (with any ×2) decides the bonus and feeds the total
      var upLeft = 0, colM = 0, colV = 0;
      for (var n = 1; n <= 6; n++) {
        var v = cells['u' + n + '-' + c], k = cellMult(cells, 'u' + n, c, m);
        if (typeof v === 'number') colM += v * k;
        else { var e = catEv('u' + n, m); colM += e[0] * k; colV += e[1] * e[1] * k * k; upLeft++; }
      }
      var pB = upLeft === 0 ? (colM >= 63 ? 1 : 0) : (colV > 0 ? 1 - normCdf((63 - colM) / Math.sqrt(colV)) : (colM >= 63 ? 1 : 0));
      colM += B * pB; colV += B * B * pB * (1 - pB);
      (LOWER_ORDER[m] || LOWER_ORDER.yum).forEach(function (rid) {
        var lk = cellMult(cells, rid, c, m);
        if (rid === 'lybonus') { var yb = cells[rid + '-' + c]; if (typeof yb === 'number') colM += yb * lk; return; }
        var lv = cells[rid + '-' + c];
        if (typeof lv === 'number') colM += lv * lk;
        else { var le = catEv(rid, m); colM += le[0] * lk; colV += le[1] * le[1] * lk * lk; }
      });
      mean += colM; variance += colV;
    }
    return { mean: mean, variance: variance };
  }
  function winProbability(me, opp, over) {
    if (over) return me.grand > (opp.grand || 0) ? 1 : me.grand < (opp.grand || 0) ? 0 : 0.5;
    // Sum the projections of the cards at least one player has started; an
    // untouched card is assumed to stay untouched by both.
    var meM = 0, meV = 0, opM = 0, opV = 0;
    MODES.forEach(function (m) {
      var mc = (me.sheets || {})[m] || {}, oc = (opp.sheets || {})[m] || {};
      if (!Object.keys(mc).length && !Object.keys(oc).length) return;
      var a = projectSheet(mc, m), b = projectSheet(oc, m);
      meM += a.mean; meV += a.variance; opM += b.mean; opV += b.variance;
    });
    var s = Math.sqrt(meV + opV);
    if (s === 0) return meM > opM ? 1 : meM < opM ? 0 : 0.5;
    return normCdf((meM - opM) / s);
  }
  function paintWin(me, opp, over) {
    var box = $('mpWin');
    if (!box) return;
    if (!opp) { box.innerHTML = ''; return; }
    var p = winProbability(me, opp, over);
    var pct = Math.round(p * 100);
    var oppN = esc(opp.name || T('Adversaire', 'Opponent'));
    box.innerHTML =
      '<div class="mp-win-label">' + T('Chances de gagner', 'Chances of winning') + '</div>' +
      '<div class="mp-win-bar"><div class="me" style="width:' + pct + '%"></div></div>' +
      '<div class="mp-win-nums"><span class="a">' + T('Toi', 'You') + ' ' + pct + ' %</span>' +
        '<span class="b">' + oppN + ' ' + (100 - pct) + ' %</span></div>' +
      (over ? '' : '<div class="mp-win-hint">' + T('Estimation selon les cases restantes', 'Estimate based on the remaining boxes') + '</div>');
  }

  // Row order per mode for the full-sheet mirror (upper 1s–6s, then lower rows).
  var LOWER_ORDER = {
    yum: ['l3k', 'l4k', 'lss', 'lls', 'lhr', 'lfh', 'lyum'],
    yahtzee: ['l3k', 'l4k', 'lfh', 'lss', 'lls', 'lyahtzee', 'lchance', 'lybonus']
  };
  LOWER_ORDER.yamio = LOWER_ORDER.yahtzee;
  // Yamio power-up slots: g1/d1 are the free golden die and double points,
  // x1/x2 the extras earned with the 63 bonus and the five lower combos. A slot
  // holds 99 (golden die, a marker) or the 1-based index (u1–u6, then lower
  // rows) of the category whose points count double.
  var POWER_SLOTS = [
    { id: 'g1', icon: 'gold', text: T('Dé doré', 'Golden die') },
    { id: 'd1', icon: 'dbl', text: T('Double points', 'Double points') },
    { id: 'x1', icon: 'bonus', text: T('Extra · boni 63', 'Extra · bonus 63') },
    { id: 'x2', icon: 'combos', text: T('Extra · 5 combos', 'Extra · 5 combos') }
  ];
  // Power-up logos are defined by index.html (window.YUM_ICONS); text fallback.
  function pwIco(name, fallback) {
    var I = window.YUM_ICONS;
    return (I && I[name]) ? I[name] : fallback;
  }
  function cellMult(cells, rid, c, m) {
    if (m !== 'yamio') return 1;
    var idx = ['u1', 'u2', 'u3', 'u4', 'u5', 'u6'].concat(LOWER_ORDER.yamio).indexOf(rid) + 1;
    var mult = 1;
    POWER_SLOTS.forEach(function (s) { if (idx && cells[s.id + '-' + c] === idx) mult *= 2; });
    return mult;
  }
  // Recompute a single column's totals from a whole-sheet cells map, mirroring
  // yum-card's own scoring (upper bonus at 63; 25 for Yum, 35 for Yahtzee).
  function colTotals(cells, c, m) {
    // A doubled category counts twice, including toward the 63 bonus.
    var sub = 0;
    for (var n = 1; n <= 6; n++) {
      var v = cells['u' + n + '-' + c];
      if (typeof v === 'number') sub += v * cellMult(cells, 'u' + n, c, m);
    }
    var bonus = sub >= 63 ? (m === 'yum' ? 25 : 35) : 0;
    var upper = (sub > 0 || bonus > 0) ? sub + bonus : 0;
    var lower = 0;
    LOWER_ORDER[m].forEach(function (rid) {
      var lv = cells[rid + '-' + c];
      if (typeof lv === 'number') lower += lv * cellMult(cells, rid, c, m);
    });
    return { sub: sub, bonus: bonus, upper: upper, lower: lower, grand: upper + lower };
  }
  // Render the opponent's ENTIRE six-column sheet as a compact, scrollable grid.
  function paintDetails(me, opp) {
    var box = $('mpDetails');
    if (!box) return;
    if (!opp) { box.innerHTML = '<div class="mp-sheet-empty">' + T('En attente de l\'adversaire…', 'Waiting for opponent…') + '</div>'; return; }
    var m = currentMode();
    var cells = oppCells();   // the opponent's card for the mode I'm looking at
    var upperRows = ['u1', 'u2', 'u3', 'u4', 'u5', 'u6'];
    var lowerRows = LOWER_ORDER[m];

    function headCells() {
      var h = '<th class="cat"></th>';
      for (var c = 1; c <= 6; c++) h += '<th>' + c + '</th>';
      return h;
    }
    function cellVal(rid, c) {
      var v = cells[rid + '-' + c];
      var x2 = cellMult(cells, rid, c, m) > 1 ? ' ' + pwIco('dbl', '<span class="sx">×2</span>') : '';
      if (v === undefined) return x2;
      return (v === 0 ? '<span class="sx">✗</span>' : v) + x2;
    }
    function bodyRow(rid) {
      var tds = '';
      for (var c = 1; c <= 6; c++) tds += '<td>' + cellVal(rid, c) + '</td>';
      return '<tr><td class="cat">' + esc(labelFor(rid, m)) + '</td>' + tds + '</tr>';
    }
    function computedRow(label, pick, cls) {
      var tds = '';
      for (var c = 1; c <= 6; c++) { var t = colTotals(cells, c, m); tds += '<td>' + (pick(t) || '') + '</td>'; }
      return '<tr class="' + cls + '"><td class="cat">' + label + '</td>' + tds + '</tr>';
    }

    // Card switcher: also switches my own sheet (the app's mode), so the
    // panel always shows the opponent's card for the mode I'm playing.
    var html = '<div class="mp-colsel mp-modesel">' + MODES.map(function (mm) {
      return '<button type="button" data-mp-mode="' + mm + '"' + (mm === m ? ' class="on"' : '') + '>' + modeName(mm).toUpperCase() + '</button>';
    }).join('') + '</div>';
    html += '<div class="mp-sheet-scroll"><table class="mp-mini"><thead><tr>' + headCells() + '</tr></thead><tbody>';
    upperRows.forEach(function (rid) { html += bodyRow(rid); });
    html += computedRow(T('Boni', 'Bonus'), function (t) { return t.bonus; }, 'sum');
    lowerRows.forEach(function (rid) { html += bodyRow(rid); });
    if (m === 'yamio') {
      POWER_SLOTS.forEach(function (p) {
        var tds = '';
        for (var c = 1; c <= 6; c++) {
          var sv = cells[p.id + '-' + c];
          tds += '<td>' + (sv === 99 ? pwIco('gold', '🎲') : (sv > 0 ? pwIco('dbl', '×2') : '')) + '</td>';
        }
        html += '<tr class="sum"><td class="cat">' + pwIco(p.icon, '') + ' ' + p.text + '</td>' + tds + '</tr>';
      });
    }
    html += computedRow(T('TOTAL', 'TOTAL'), function (t) { return t.grand; }, 'grand');
    html += '</tbody></table></div>' +
      '<div class="mp-sheet-cap">' + esc(opp.name || T('Adversaire', 'Opponent')) +
      ' — ' + modeName(m) + ' : ' + ((opp.per && opp.per[m]) ? opp.per[m].grand : 0) +
      ' · ' + T('3 cartes', '3 cards') + ' : ' + (opp.grand || 0) + '</div>' +
      '<div class="mp-note" style="text-align:center;margin-top:4px">' +
        T('Change de mode (YUM / YAHTZEE / YAMIO) pour voir ses autres cartes.',
          'Switch mode (YUM / YAHTZEE / YAMIO) to see their other cards.') + '</div>';
    box.innerHTML = html;
  }

  // ── Score sync ──────────────────────────────────────────────────────────────
  function scoreSig(sc) {
    return sc.grand + '|' + sc.upper + '|' + sc.lower + '|' + JSON.stringify(sc.sheets) +
      '|' + (iAmDone ? 1 : 0) + '|' + (sc.allFilled ? 1 : 0);
  }
  function pushScore() {
    if (!myPlayerRef) return;
    var sc = readMyScore();
    var sig = scoreSig(sc);
    if (sig === lastPushSig) return;
    var since = now() - lastPushAt;
    if (since < SYNC_MIN_MS) {
      if (!pushQueued) {
        pushQueued = true;
        setTimeout(function () { pushQueued = false; pushScore(); }, SYNC_MIN_MS - since + 20);
      }
      return;
    }
    lastPushSig = sig;
    lastPushAt = now();
    // Wire format v3: all three cards. If that ever gets too long for the
    // database, send only the card currently shown.
    var cellsStr = JSON.stringify({ v: 3, s: sc.sheets });
    if (cellsStr.length > 3900) {
      var one = {}; one[currentMode()] = sc.cells;
      cellsStr = JSON.stringify({ v: 3, s: one });
      if (cellsStr.length > 3900) cellsStr = '{}';
    }
    myPlayerRef.update({
      grand: sc.grand, upper: sc.upper, lower: sc.lower,
      cells: cellsStr, done: !!iAmDone, filledAll: !!sc.allFilled,
      lastActiveAt: now()
    }).catch(function () {});
    if ($('mpVs')) paintScoreboard();
    updateFabState();
    evaluateGameOver();
  }
  function startScoreSync() {
    stopScoreSync();
    lastPushSig = null;
    // Trigger on total changes (recompute rewrites #grandRow text on every entry)
    var gr = $('grandRow');
    if (gr && window.MutationObserver) {
      scoreObserver = new MutationObserver(function () { pushScore(); });
      scoreObserver.observe(gr, { childList: true, characterData: true, subtree: true });
    }
    pollTimer = setInterval(pushScore, POLL_MS);
    heartbeatTimer = setInterval(function () {
      if (myPlayerRef) myPlayerRef.update({ lastActiveAt: now() }).catch(function () {});
    }, HEARTBEAT_MS);
    pushScore();
  }
  function stopScoreSync() {
    if (scoreObserver) { try { scoreObserver.disconnect(); } catch (e) {} scoreObserver = null; }
    if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
    if (heartbeatTimer) { clearInterval(heartbeatTimer); heartbeatTimer = null; }
  }
  function toggleDone() {
    iAmDone = !iAmDone;
    lastPushSig = null;
    pushScore();
    paintScoreboard();
  }

  // ── Room membership ─────────────────────────────────────────────────────────
  function attachRoom(code, phase) {
    roomCode = code;
    roomRef = db.ref(ROOMS + '/' + code);
    playersRef = roomRef.child('players');
    myPlayerRef = playersRef.child(uid);
    try { myPlayerRef.onDisconnect().remove(); } catch (e) {}
    // Fresh round + ready state whenever we (re)attach.
    rematchVoted = false; rematchVotes = {}; roundLocal = 0; gameOverShown = false;
    matchPhase = phase || 'ready'; readyAccepted = false; readySawOpp = false; matchCanceled = false;

    if (playersListener) { try { roomRef.off('value', playersListener); } catch (e) {} }
    // Listen on the whole room (players + rematch votes + status) together.
    playersListener = roomRef.on('value', onRoomSnap, function () {});
    // Score sync starts only once both players have accepted (see beginPlaying).
  }

  function onRoomSnap(snap) {
    var room = snap.val() || {};
    var val = room.players || {};
    rematchVotes = room.rematch || {};
    var found = null;
    Object.keys(val).forEach(function (k) { if (k !== uid) found = val[k]; });

    if (found) {
      // Mid-match, a player whose heartbeat stopped is "dropped" (their seat is
      // kept for RECONNECT_MS); an explicit leave removes the entry instead.
      var silent = found.lastActiveAt ? now() - found.lastActiveAt : 0;
      var disc = matchPhase === 'playing' && silent > DROP_MS;
      // v3 payload carries all three cards; an older client sends one card,
      // which we file under the room's mode.
      var parsed = parseCells(found.cells);
      var sheets = (parsed && parsed.v === 3 && parsed.s && typeof parsed.s === 'object') ? parsed.s : null;
      if (!sheets) { sheets = {}; sheets[sameCard(room.mode, 'yahtzee') ? room.mode : 'yum'] = parsed || {}; }
      var per = {};
      MODES.forEach(function (m) { per[m] = sheetTotals(sheets[m] || {}, m); });
      oppData = {
        name: found.name, grand: found.grand || 0, upper: found.upper || 0,
        lower: found.lower || 0, done: !!found.done, filledAll: !!found.filledAll,
        ready: !!found.ready, gone: !disc && silent > OPP_GONE_MS, disconnected: disc,
        leftAt: disc ? found.lastActiveAt + DROP_MS : 0, sheets: sheets, per: per
      };
    } else if (oppData) {
      oppData.gone = true;
    }

    if (matchPhase === 'playing') {
      if (!found && oppData && !gameOverShown) {
        endMatch(T('Ton adversaire a quitté la partie.', 'Your opponent left the match.'));
        return;
      }
      if (oppData && oppData.disconnected) startReconnectWatch(); else stopReconnectWatch();
    }

    // Either side can cancel the pending match via room.status.
    if (!matchCanceled && matchPhase === 'ready' &&
        (room.status === 'canceled' || room.status === 'declined' || room.status === 'timeout')) {
      cancelMatch(room.status === 'timeout'
        ? T('Match annulé — délai dépassé.', 'Match canceled — timed out.')
        : T('L\'adversaire a refusé le match.', 'Opponent declined the match.'));
      return;
    }

    if (matchPhase === 'ready') {
      if (!found) {
        // Opponent gone after we'd already seen them → cancel; otherwise keep waiting.
        if (readySawOpp && !matchCanceled) cancelMatch(T('L\'adversaire est parti.', 'Opponent left.'));
        return;
      }
      readySawOpp = true;
      // Someone answered a pending invite: surface the accept screen even if the
      // panel was closed.
      var bd = $('mpBackdrop');
      if (bd && !bd.classList.contains('show')) bd.classList.add('show');
      var meReady = !!(val[uid] && val[uid].ready);
      var oppReady = !!found.ready;
      if (meReady && oppReady) { beginPlaying(); return; }
      if (!$('mpAcceptBtn')) renderReady();
      updateReadyView(meReady, oppReady);
      updateFabState();
      return;
    }

    // ── playing phase ──
    maybeApplyRematch();
    if ($('mpVs')) paintScoreboard();
    else if (found && $('mpBackdrop') && $('mpBackdrop').classList.contains('show')) renderMatch();
    updateFabState();
    evaluateGameOver();
  }

  function beginPlaying() {
    if (matchPhase === 'playing') return;
    matchPhase = 'playing';
    forgetInvite();   // invite consumed; the room is torn down normally after the match
    clearReadyCountdown();
    armPresence();
    saveMatch();
    startScoreSync();
    // Drop the player onto their sheet (live bar + FAB carry the score) and
    // announce the start on screen.
    closePanel();
    updateFabState();
    showStartToast();
  }
  var toastTimer = null;
  function showToast(big, sub, ms, cls) {
    var t = $('mpToast');
    if (!t) {
      t = document.createElement('div');
      t.id = 'mpToast';
      t.setAttribute('role', 'status');
      document.body.appendChild(t);
    }
    t.className = 'mp-toast' + (cls ? ' ' + cls : '');
    t.innerHTML = '<div class="big">' + big + '</div>' + (sub ? '<div class="sub">' + sub + '</div>' : '');
    void t.offsetWidth; // restart the transition if shown back-to-back
    t.classList.add('show');
    if (toastTimer) clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { t.classList.remove('show'); }, ms || 3000);
  }
  function showStartToast() {
    var oppN = (oppData && oppData.name) || T('Adversaire', 'Opponent');
    showToast(ui('dice') + T('Partie commencée !', 'Match started!'),
      esc(myName) + ' vs ' + esc(oppN) + ' — ' + T('Bonne chance !', 'Good luck!'), 3000);
  }

  // ── Presence, disconnect grace period and rejoin ────────────────────────────
  // While playing, my seat must survive a dropped connection: cancel the
  // onDisconnect removal armed in attachRoom. The heartbeat (lastActiveAt)
  // stopping is what tells the opponent I dropped.
  function armPresence() {
    if (!myPlayerRef) return;
    try { myPlayerRef.onDisconnect().cancel(); } catch (e) {}
    myPlayerRef.update({ lastActiveAt: now() }).catch(function () {});
  }
  function reconnectLeftSec() {
    if (!oppData || !oppData.disconnected) return 0;
    return Math.max(0, Math.ceil((oppData.leftAt + RECONNECT_MS - now()) / 1000));
  }
  function startReconnectWatch() {
    if (reconnectTimer) return;
    var oppN = esc((oppData && oppData.name) || T('L\'adversaire', 'Your opponent'));
    showToast(ui('warn') + T(oppN + ' s\'est déconnecté', oppN + ' disconnected'),
      T('Il a 1 minute pour revenir…', 'They have 1 minute to come back…'), 3500, 'warn');
    reconnectTimer = setInterval(function () {
      if (!mmActive || !oppData || !oppData.disconnected) { stopReconnectWatch(); return; }
      if (reconnectLeftSec() <= 0) {
        endMatch(T(oppN + ' ne s\'est pas reconnecté (1 min).', oppN + ' did not reconnect (1 min).'));
        return;
      }
      if ($('mpVs')) paintScoreboard();
      updateFabState();
    }, 1000);
  }
  function stopReconnectWatch() {
    if (reconnectTimer) { clearInterval(reconnectTimer); reconnectTimer = null; }
  }
  // Close the live match on this client (opponent left / never came back).
  function endMatch(reason) {
    stopReconnectWatch();
    var code = roomCode;
    try { if (myPlayerRef) myPlayerRef.onDisconnect().cancel(); } catch (e) {}
    if (db && code) db.ref(ROOMS + '/' + code).remove().catch(function () {});
    leaveAll(false);
    showToast(ui('exit') + T('Partie fermée', 'Match closed'), reason, 4500, 'warn');
    var b = $('mpBackdrop');
    if (b && b.classList.contains('show')) { renderLobby(); showErr(reason.replace(/<[^>]+>/g, '')); }
  }
  function readMatch() {
    try { var v = JSON.parse(localStorage.getItem(MATCH_KEY)); return (v && v.code) ? v : null; }
    catch (e) { return null; }
  }
  function saveMatch() {
    try { localStorage.setItem(MATCH_KEY, JSON.stringify({ code: roomCode, role: role, at: now() })); } catch (e) {}
  }
  function forgetMatch() {
    try { localStorage.removeItem(MATCH_KEY); } catch (e) {}
  }
  // On boot: if this client dropped out of a live match, rejoin it when the room
  // still exists, the opponent is still there and the grace period has not run out.
  function resumeMatch() {
    var v = readMatch();
    if (!v) return false;
    if (now() - (v.at || 0) > 6 * 60 * 60 * 1000) { forgetMatch(); return false; }
    ensureReady().then(function (u) {
      if (!u) throw new Error('auth');
      var ref = db.ref(ROOMS + '/' + v.code);
      return ref.once('value').then(function (snap) {
        var room = snap.val();
        var players = (room && room.players) || {};
        var me = players[uid];
        var oppKey = Object.keys(players).filter(function (k) { return k !== uid; })[0];
        var closed = !room || !me || !oppKey;
        var late = !!(me && me.lastActiveAt && (now() - me.lastActiveAt > DROP_MS + RECONNECT_MS));
        if (closed || late) {
          forgetMatch();
          if (room) ref.remove().catch(function () {});
          showToast(ui('exit') + T('Partie fermée', 'Match closed'),
            late ? T('Délai de reconnexion dépassé (1 min).', 'Reconnect window expired (1 min).')
                 : T('Ton adversaire a quitté la partie.', 'Your opponent left the match.'), 4500, 'warn');
          return;
        }
        myName = nameFromSheet(); mode = room.mode || currentMode();
        mmActive = true; role = v.role || 'guest'; iAmDone = false; oppData = null;
        attachRoom(v.code, 'playing');
        readyAccepted = true;
        // Don't let a rematch that happened before the drop wipe my sheet now.
        var rv = room.rematch || {};
        roundLocal = Object.keys(rv).reduce(function (m, k) { return Math.max(m, rv[k] || 0); }, 0);
        armPresence();
        saveMatch();
        startScoreSync();
        updateFabState();
        showToast(ui('zap') + T('Reconnecté !', 'Reconnected!'), T('La partie continue.', 'The match goes on.'), 3000);
      });
    }).catch(function (e) {
      console.warn('[yumcard-mp] resume match failed:', e);
      mmActive = false; role = null; matchPhase = null;
    });
    return true;
  }

  // ── Ready-check (both players must accept) ──────────────────────────────────
  function renderReady() {
    var s = $('mpSheet');
    if (!s) return;
    var oppName = (oppData && oppData.name) || T('Adversaire', 'Opponent');
    s.innerHTML =
      '<h2>' + T('Adversaire trouvé !', 'Opponent found!') +
        '<button class="mp-close" id="mpCloseBtn">×</button></h2>' +
      '<p class="mp-sub">' + T('La partie démarre quand vous avez tous les deux appuyé sur « Commencer ». Les 3 cartes comptent : Yum, Yahtzee et Yamio.',
                               'The match starts once you have both tapped "Start". All 3 cards count: Yum, Yahtzee and Yamio.') + '</p>' +
      '<div class="mp-ready">' +
        '<div class="mp-rc"><div class="who">' + esc(myName) + ' (' + T('toi', 'you') + ')</div>' +
          '<div class="chip" id="mpMeChip">' + T('En attente', 'Pending') + '</div></div>' +
        '<div class="mp-rc-vs">VS</div>' +
        '<div class="mp-rc"><div class="who" id="mpOppWho">' + esc(oppName) + '</div>' +
          '<div class="chip" id="mpOppChip">' + T('En attente', 'Pending') + '</div></div>' +
      '</div>' +
      '<div class="mp-ready-count">' + T('Temps restant : ', 'Time left: ') + '<span id="mpReadyCountdown">30s</span></div>' +
      '<button class="mp-btn primary" id="mpAcceptBtn">' + ui('dice') + T('Commencer la partie', 'Start the match') + '</button>' +
      '<button class="mp-btn danger" id="mpDeclineBtn">' + T('Refuser', 'Decline') + '</button>';
    $('mpCloseBtn').addEventListener('click', closePanel);
    $('mpAcceptBtn').addEventListener('click', function () { acceptMatch(); });
    $('mpDeclineBtn').addEventListener('click', function () { declineMatch(); });
    if (!readyTimer) startReadyCountdown();
  }
  function updateReadyView(meReady, oppReady) {
    if (!$('mpAcceptBtn')) return;
    var meChip = $('mpMeChip'), oppChip = $('mpOppChip'), acc = $('mpAcceptBtn'), who = $('mpOppWho');
    if (who && oppData && oppData.name) who.textContent = oppData.name;
    if (meChip) { meChip.textContent = meReady ? T('Prêt ✓', 'Ready ✓') : T('En attente', 'Pending'); meChip.classList.toggle('ready', meReady); }
    if (oppChip) { oppChip.textContent = oppReady ? T('Prêt ✓', 'Ready ✓') : T('En attente', 'Pending'); oppChip.classList.toggle('ready', oppReady); }
    if (acc) {
      acc.disabled = meReady;
      var oppN = esc((oppData && oppData.name) || T('l\'adversaire', 'opponent'));
      acc.innerHTML = meReady
        ? ui('hourglass') + T('En attente que ' + oppN + ' commence…', 'Waiting for ' + oppN + ' to start…')
        : ui('dice') + T('Commencer la partie', 'Start the match');
    }
  }
  function startReadyCountdown() {
    clearReadyCountdown();
    if (!readyDeadline || readyDeadline < now()) readyDeadline = now() + READY_TIMEOUT_MS;
    readyTimer = setInterval(function () {
      var left = Math.max(0, Math.round((readyDeadline - now()) / 1000));
      var el = $('mpReadyCountdown');
      if (el) el.textContent = left + 's';
      if (readyDeadline - now() <= 0) {
        clearReadyCountdown();
        if (matchPhase === 'ready' && !matchCanceled) {
          if (roomRef) roomRef.child('status').set('timeout').catch(function () {});
          cancelMatch(T('Match annulé — délai dépassé.', 'Match canceled — timed out.'));
        }
      }
    }, 500);
  }
  function clearReadyCountdown() { if (readyTimer) { clearInterval(readyTimer); readyTimer = null; } }
  function acceptMatch() {
    if (!myPlayerRef) return;
    readyAccepted = true;
    myPlayerRef.update({ ready: true, lastActiveAt: now() }).catch(function () {});
    updateReadyView(true, oppData && oppData.ready);
  }
  function declineMatch() {
    if (roomRef) roomRef.child('status').set('declined').catch(function () {});
    cancelMatch(T('Tu as refusé le match.', 'You declined the match.'));
  }
  function cancelMatch(msg) {
    if (matchCanceled) return;
    matchCanceled = true;
    clearReadyCountdown();
    leaveAll(true);
    renderLobby();
    showErr(msg);
    if (inviteCode) resumeInvite(msg);
  }

  // Both players finished (each either tapped Done or filled every category).
  function bothFinished() {
    var me = readMyScore();
    var meFin = iAmDone || me.allFilled;
    var oppFin = oppData && !oppData.gone && (oppData.done || oppData.filledAll);
    return !!(meFin && oppFin && oppData);
  }
  function evaluateGameOver() {
    if (!mmActive || !oppData) return;
    // Auto-mark myself done once my sheet is complete, so the opponent's client
    // learns of it even if I never tapped the Done button.
    var me = readMyScore();
    if (me.allFilled && !iAmDone) { iAmDone = true; lastPushSig = null; pushScore(); }
    if (bothFinished() && !gameOverShown) {
      gameOverShown = true;
      if ($('mpVs')) paintScoreboard();
    }
  }

  // ── Rematch (keep the same opponent) ────────────────────────────────────────
  // A round-number handshake, deliberately race-proof: each player writes the
  // round they want to advance TO (roundLocal + 1). When BOTH players' votes
  // reach a round greater than mine, I advance and reset — without deleting any
  // vote, so a fast peer can't clear its vote before I observe agreement. The
  // votes simply become equal to the new round and stop triggering.
  function theirVoteValue() {
    var v = 0;
    Object.keys(rematchVotes || {}).forEach(function (k) {
      if (k !== uid) v = rematchVotes[k] || 0;
    });
    return v;
  }
  function requestRematch() {
    if (!roomRef || !uid) return;
    rematchVoted = true;
    roomRef.child('rematch/' + uid).set(roundLocal + 1).catch(function () {});
    paintScoreboard();
    maybeApplyRematch();
  }
  function maybeApplyRematch() {
    if (!roomRef || !oppData) return;
    var mine = rematchVotes[uid] || 0;
    var theirs = theirVoteValue();
    var target = Math.min(mine, theirs);
    // Both have committed to the same (or a newer) round → advance once.
    if (target > roundLocal) {
      roundLocal = target;
      rematchVoted = false;
      gameOverShown = false;
      iAmDone = false;
      resetMyColumn();
      lastPushSig = null;
      pushScore();
      if ($('mpVs')) paintScoreboard();
    }
  }
  function parseCells(str) {
    if (!str || typeof str !== 'string') return {};
    try { var o = JSON.parse(str); return (o && typeof o === 'object') ? o : {}; }
    catch (e) { return {}; }
  }

  function updateFabState() {
    var label = $('mpFabLabel');
    if (!label) return;
    if (mmActive && matchPhase === 'ready') {
      if (oppData && !oppData.gone) label.textContent = T('Adversaire trouvé', 'Opponent found');
      else if (inviteCode && roomCode === inviteCode) label.textContent = T('Invitation · ', 'Invite · ') + inviteCode;
      else label.textContent = T('En attente', 'Waiting');
    } else if (mmActive && matchPhase === 'playing' && oppData && !oppData.gone) {
      var me = readMyScore();
      if (oppData.disconnected) {
        label.innerHTML = ui('hourglass') + esc(oppData.name || T('Adv.', 'Opp.')) + ' ' + reconnectLeftSec() + ' s';
      } else {
        label.textContent = T('Toi', 'You') + ' ' + me.grand + ' · ' + (oppData.grand || 0) + ' ' +
          (oppData.name || T('Adv.', 'Opp.'));
      }
    } else if (mmActive) {
      label.textContent = T('En partie', 'In match');
    } else {
      label.textContent = T('Multijoueur', 'Multiplayer');
    }
    updateLiveBar();
  }

  // ── Create / join by code ───────────────────────────────────────────────────
  function startCreateCode() {
    clearErr();
    myName = nameFromSheet();
    mode = currentMode();
    renderSearching(T('Connexion…', 'Connecting…'));
    ensureReady().then(function (u) {
      if (!u) throw new Error('auth');
      mmActive = true; role = 'host'; iAmDone = false; oppData = null;
      return createRoom(null);
    }).then(function (code) {
      setInvite(code);
      renderWaitingCode(code);
    }).catch(function (e) {
      console.warn('[yumcard-mp] create failed:', e);
      renderLobby();
      showErr(connectErr(e));
    });
  }

  function createRoom(preferredCode) {
    // Try up to a few random codes (or the preferred/friend one) until we win an
    // empty slot via transaction.
    var attempts = preferredCode ? [preferredCode] : [randCode(), randCode(), randCode(), randCode(), randCode()];
    var i = 0;
    function tryNext() {
      if (i >= attempts.length) throw new Error('no-code');
      var code = attempts[i++];
      var ref = db.ref(ROOMS + '/' + code);
      return ref.transaction(function (curr) {
        if (curr) return undefined; // taken
        // Keep to the existing schema (the rules reject unknown keys); invite
        // expiry is derived from createdAt (see roomExpired).
        return {
          host: uid,
          createdAt: now(),
          mode: wireMode(),
          createdBy: preferredCode ? 'friend' : 'match',
          players: makeSelfPlayer()
        };
      }).then(function (res) {
        if (res && res.committed) { attachRoom(code); return code; }
        return tryNext();
      });
    }
    return Promise.resolve().then(tryNext).catch(function (e) {
      if (isPermErr(e) && enableModeFallback()) { i = 0; return tryNext(); }
      throw e;
    });
  }

  function makeSelfPlayer() {
    var p = {};
    p[uid] = { name: myName.slice(0, 20) || 'Player', uid: uid, joined: now(), lastActiveAt: now(), grand: 0, upper: 0, lower: 0, done: false };
    return p;
  }

  function startJoinCode(code) {
    clearErr();
    myName = nameFromSheet();
    code = code.toUpperCase().replace(/[^A-Z0-9]/g, '');
    if (code.length < 4) { showErr(T('Code invalide.', 'Invalid code.')); return; }
    renderSearching(T('Connexion…', 'Connecting…'));
    ensureReady().then(function (u) {
      if (!u) throw new Error('auth');
      var ref = db.ref(ROOMS + '/' + code);
      return ref.once('value').then(function (snap) {
        if (!snap.exists()) throw new Error('not-found');
        var room = snap.val();
        if (roomExpired(room)) {
          return ref.remove().catch(function () {}).then(function () { throw new Error('expired'); });
        }
        if (room.host === uid) throw new Error('own-room');
        mode = sameCard(room.mode, currentMode()) ? currentMode() : (room.mode || 'yum');
        mmActive = true; role = 'guest'; iAmDone = false; oppData = null;
        var hostHere = !!(room.players && room.players[room.host]);
        return ref.child('players/' + uid).set({
          name: myName.slice(0, 20) || 'Player', uid: uid, joined: now(),
          lastActiveAt: now(), grand: 0, upper: 0, lower: 0, done: false
        }).then(function () {
          if (room.status) ref.child('status').remove().catch(function () {});
          attachRoom(code);
          if (hostHere) renderReady();
          else renderSearching(hostOfflineText());
        });
      });
    }).catch(function (e) {
      console.warn('[yumcard-mp] join failed:', e);
      mmActive = false; role = null;
      renderLobby();
      var m = e && e.message;
      if (m === 'not-found') showErr(T('Aucune partie avec ce code.', 'No match found for that code.'));
      else if (m === 'expired') showErr(T('Cette invitation a expiré (5 jours max).', 'This invite has expired (5 days max).'));
      else if (m === 'own-room') showErr(T('C\'est ta propre invitation.', 'That is your own invite.'));
      else showErr(connectErr(e));
    });
  }

  function maybeSuggestMode(m) {
    // If the opponent's room uses a different mode than the local sheet, nudge.
    if (m && !sameCard(m, currentMode())) {
      var st = $('mpMatchStatus');
      if (st) st.textContent = T('Astuce : ton adversaire joue en mode ' + modeName(m) + '.',
                                 'Tip: your opponent is playing ' + modeName(m) + ' mode.');
    }
  }

  function connectErr(e) {
    var msg = (e && e.message) || '';
    if (/permission|PERMISSION/.test(msg)) {
      return T('Accès refusé par le serveur. Réessaie plus tard.', 'Server denied access. Please try again later.');
    }
    return T('Connexion impossible. Vérifie ta connexion et réessaie.', 'Could not connect. Check your internet and try again.');
  }

  // ── Random matchmaking ──────────────────────────────────────────────────────
  function startFind() {
    clearErr();
    myName = nameFromSheet();
    mode = currentMode();
    renderSearching(T('Connexion…', 'Connecting…'));
    ensureReady().then(function (u) {
      if (!u) throw new Error('auth');
      return findMatch();
    }).catch(function (e) {
      console.warn('[yumcard-mp] find failed:', e);
      leaveAll(false);
      renderLobby();
      showErr(connectErr(e));
    });
  }

  function findMatch() {
    mmActive = true; role = null; inQueue = false; claimInFlight = false;
    offerSeen = false; oppData = null; iAmDone = false;
    clearTimers();
    renderSearching(T('Recherche d\'un adversaire…', 'Looking for an opponent…'));

    return Promise.resolve()
      .then(function () { return db.ref(QUEUE + '/' + uid).remove().catch(function () {}); })
      .then(function () { return db.ref(OFFERS + '/' + uid).remove().catch(function () {}); })
      .then(function () {
        offerRef = db.ref(OFFERS + '/' + uid);
        offerListener = offerRef.on('value', onMyOffer, function () {});
        attachQueueWatcher();
        return tryClaimAny();
      })
      .then(function (claimed) {
        if (!mmActive) return;
        if (!claimed) return joinQueue();
      });
  }

  function attachQueueWatcher() {
    detachQueueWatcher();
    queueRef = db.ref(QUEUE).orderByChild('ts').limitToFirst(QUEUE_LIMIT);
    queueWatcher = queueRef.on('value', onQueueChange, function () {});
  }
  function detachQueueWatcher() {
    if (queueRef && queueWatcher) { try { queueRef.off('value', queueWatcher); } catch (e) {} }
    queueRef = null; queueWatcher = null;
  }
  function detachOfferListener() {
    if (offerRef && offerListener) { try { offerRef.off('value', offerListener); } catch (e) {} }
    offerListener = null;
  }

  function joinQueue() {
    function entry() { return { uid: uid, name: myName.slice(0, 20) || 'Player', ts: now(), mode: wireMode() }; }
    return db.ref(QUEUE + '/' + uid).set(entry())
      .catch(function (e) {
        if (isPermErr(e) && enableModeFallback()) return db.ref(QUEUE + '/' + uid).set(entry());
        throw e;
      })
      .then(function () {
        inQueue = true;
        try { db.ref(QUEUE + '/' + uid).onDisconnect().remove(); } catch (e) {}
        armPromote();
      }).catch(function () {});
  }

  function freshCandidates(all, wantGreater) {
    var t = now();
    return Object.keys(all).map(function (k) { return [k, all[k]]; })
      .filter(function (e) {
        var u = e[0], info = e[1];
        return u !== uid && info && typeof info.ts === 'number' &&
          (t - info.ts) < STALE_MS &&
          (wantGreater ? u > uid : u < uid);
      })
      .sort(function (a, b) { return (a[1].ts || 0) - (b[1].ts || 0); });
  }

  function tryClaimAny() {
    return db.ref(QUEUE).orderByChild('ts').limitToFirst(QUEUE_LIMIT).once('value')
      .then(function (snap) {
        if (!snap || !snap.exists() || !mmActive) return false;
        var cands = freshCandidates(snap.val() || {}, true);
        return claimSeq(cands);
      }).catch(function () { return false; });
  }
  function claimSeq(cands) {
    var i = 0;
    function next() {
      if (i >= cands.length || !mmActive || role) return false;
      var e = cands[i++];
      return tryClaimOne(e[0], e[1]).then(function (ok) { return ok ? true : next(); });
    }
    return Promise.resolve().then(next);
  }

  function onQueueChange(snap) {
    if (!mmActive || role || !inQueue || claimInFlight) return;
    if (!snap || !snap.exists()) return;
    var cands = freshCandidates(snap.val() || {}, true);
    if (!cands.length) return;
    claimInFlight = true;
    claimSeq(cands).then(function () { claimInFlight = false; }, function () { claimInFlight = false; });
  }

  function winOfferSlot(ref) {
    var placeholder = { from: uid, fromName: myName.slice(0, 20) || 'Player', ts: now() };
    return ref.transaction(function (curr) {
      if (curr) return undefined;
      return placeholder;
    }).then(function (res) { return !!(res && res.committed); }, function () { return false; });
  }

  function tryClaimOne(oppUid, oppInfo) {
    if (!mmActive || role || oppUid <= uid) return Promise.resolve(false);
    var oRef = db.ref(OFFERS + '/' + oppUid);
    return winOfferSlot(oRef).then(function (won) {
      if (!won || !mmActive || role) return false;
      return finishClaim(oRef, oppUid, oppInfo);
    });
  }
  function tryClaimPromote(oppUid, oppInfo) {
    if (!mmActive || role || oppUid >= uid) return Promise.resolve(false);
    var oRef = db.ref(OFFERS + '/' + oppUid);
    return winOfferSlot(oRef).then(function (won) {
      if (!won || !mmActive || role) { if (won) oRef.remove().catch(function () {}); return false; }
      return db.ref(OFFERS + '/' + uid).once('value').then(function (mine) {
        if ((mine && mine.exists()) || offerSeen || role || !mmActive) {
          offerSeen = true; oRef.remove().catch(function () {}); return false;
        }
        return finishClaim(oRef, oppUid, oppInfo);
      });
    });
  }

  function finishClaim(oRef, oppUid, oppInfo) {
    clearTimers();
    role = 'host';
    detachOfferListener();
    renderSearching(T('Adversaire trouvé ! Connexion…', 'Opponent found! Connecting…'));
    return createRoom(null).then(function (code) {
      if (!code || !mmActive) { oRef.remove().catch(function () {}); role = null; return false; }
      return oRef.update({ roomCode: code }).then(function () {
        db.ref(QUEUE + '/' + uid).remove().catch(function () {});
        detachQueueWatcher();
        // Ready overlay appears via the room listener once the guest joins.
        renderSearching(T('Adversaire trouvé ! En attente…', 'Opponent found! Waiting…'));
        return true;
      }).catch(function () { oRef.remove().catch(function () {}); return false; });
    }).catch(function () { oRef.remove().catch(function () {}); role = null; return false; });
  }

  function onMyOffer(snap) {
    if (!mmActive || role) return;
    if (!snap || !snap.exists()) { offerSeen = false; return; }
    offerSeen = true;
    var val = snap.val() || {};
    if (val.roomCode) {
      // A seeker created a room for us — join it as guest.
      role = 'guest';
      detachQueueWatcher();
      clearTimers();
      db.ref(QUEUE + '/' + uid).remove().catch(function () {});
      var code = val.roomCode;
      db.ref(ROOMS + '/' + code).child('players/' + uid).set({
        name: myName.slice(0, 20) || 'Player', uid: uid, joined: now(),
        lastActiveAt: now(), grand: 0, upper: 0, lower: 0, done: false
      }).then(function () {
        offerRef.remove().catch(function () {});
        attachRoom(code);
        renderReady();
      }).catch(function (e) {
        console.warn('[yumcard-mp] guest join failed:', e);
        role = null;
      });
    } else {
      // Claimed but no room yet — arm a timer to free the slot if it never comes.
      armOfferWait();
    }
  }

  function armPromote() {
    clearPromote();
    promoteTimer = setTimeout(function () { promoteTimer = null; tryPromote(); }, PROMOTE_AFTER_MS);
  }
  function clearPromote() { if (promoteTimer) { clearTimeout(promoteTimer); promoteTimer = null; } }
  function armOfferWait() {
    if (offerWaitTimer) return;
    offerWaitTimer = setTimeout(function () {
      offerWaitTimer = null;
      if (!mmActive || role) return;
      offerSeen = false;
      db.ref(OFFERS + '/' + uid).remove().catch(function () {});
      if (inQueue) armPromote();
    }, OFFER_WAIT_MS);
  }
  function clearOfferWait() { if (offerWaitTimer) { clearTimeout(offerWaitTimer); offerWaitTimer = null; } }
  function clearTimers() { clearPromote(); clearOfferWait(); }

  function tryPromote() {
    if (!mmActive || role || !inQueue || offerSeen) return;
    db.ref(QUEUE).orderByChild('ts').limitToFirst(QUEUE_LIMIT).once('value').then(function (snap) {
      if (!mmActive || role || !snap || !snap.exists()) { if (mmActive && !role && inQueue) armPromote(); return; }
      var cands = freshCandidates(snap.val() || {}, false); // reversed: we host lower uid
      var i = 0;
      function next() {
        if (i >= cands.length || !mmActive || role || offerSeen) {
          if (mmActive && !role && !offerSeen && inQueue) armPromote();
          return;
        }
        var e = cands[i++];
        tryClaimPromote(e[0], e[1]).then(function (ok) { if (!ok) next(); });
      }
      next();
    }).catch(function () { if (mmActive && !role && inQueue) armPromote(); });
  }

  // ── Teardown ────────────────────────────────────────────────────────────────
  function leaveAll(removeRoomData) {
    stopScoreSync();
    stopReconnectWatch();
    forgetMatch();
    clearTimers();
    clearReadyCountdown();
    detachQueueWatcher();
    detachOfferListener();
    if (roomRef && playersListener) { try { roomRef.off('value', playersListener); } catch (e) {} }
    playersListener = null;

    // A pending friend invite keeps its room (joinable for 5 days); only my player
    // entry goes away so a guest sees the host as offline, not as present.
    var keepRoom = !!(inviteCode && roomCode === inviteCode && matchPhase !== 'playing');
    if (db && uid) {
      db.ref(QUEUE + '/' + uid).remove().catch(function () {});
      db.ref(OFFERS + '/' + uid).remove().catch(function () {});
      if (removeRoomData && roomCode) {
        if (!keepRoom) { try { myPlayerRef && myPlayerRef.onDisconnect().cancel(); } catch (e) {} }
        db.ref(ROOMS + '/' + roomCode + '/rematch/' + uid).remove().catch(function () {});
        db.ref(ROOMS + '/' + roomCode + '/players/' + uid).remove().catch(function () {});
        if (keepRoom) db.ref(ROOMS + '/' + roomCode + '/status').remove().catch(function () {});
        // If we're the host and now alone, drop the room.
        if (role === 'host' && !keepRoom) {
          db.ref(ROOMS + '/' + roomCode + '/players').once('value').then(function (s) {
            var v = s.val() || {};
            if (Object.keys(v).length === 0) db.ref(ROOMS + '/' + roomCode).remove().catch(function () {});
          }).catch(function () {});
        }
      }
    }
    mmActive = false; role = null; inQueue = false; claimInFlight = false;
    offerSeen = false; roomCode = null; roomRef = null; playersRef = null;
    myPlayerRef = null; oppData = null; iAmDone = false; lastPushSig = null;
    rematchVoted = false; rematchVotes = {}; gameOverShown = false;
    matchPhase = null; readyAccepted = false; readySawOpp = false;
    matchCanceled = false; readyDeadline = 0;
    updateFabState();
  }

  // ── Wire up ─────────────────────────────────────────────────────────────────
  function boot() {
    buildDom();
    // Keep the FAB label in the right language if the user toggles it.
    var langToggle = $('langToggle');
    if (langToggle) langToggle.addEventListener('click', function () {
      setTimeout(function () {
        if (!mmActive) { var l = $('mpFabLabel'); if (l) l.textContent = T('Multijoueur', 'Multiplayer'); }
      }, 0);
    });
    // Switching card mid-match: repaint the panel / FAB / live bar for that card
    // (the score push itself is triggered by the sheet's own recompute).
    var modeToggle = $('modeToggle');
    if (modeToggle) modeToggle.addEventListener('click', function () {
      setTimeout(function () {
        if (!mmActive) return;
        if ($('mpVs')) paintScoreboard();
        updateFabState();
      }, 0);
    });
    // Closing / reloading mid-match keeps my seat for RECONNECT_MS (see resumeMatch).
    window.addEventListener('beforeunload', function () {
      if (!(matchPhase === 'playing' && roomCode)) leaveAll(true);
    });
    // Opened from a QR / invite link → join that code right away.
    var jm = (location.hash || '').match(/^#join=([A-Z0-9]{4,8})$/i);
    if (jm) {
      try { history.replaceState(null, '', location.pathname + location.search); } catch (e) {}
      setTimeout(function () { openPanel(); startJoinCode(jm[1]); }, 300);
    } else if (!resumeMatch()) {
      resumeInvite();
    }
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }

  // Expose a tiny hook for debugging/tests.
  window.yumCardMP = {
    open: openPanel,
    // Win estimate between two cells maps (numbers) in mode m — used by the
    // invite-link "opponent's score" popup in index.html.
    winEstimate: function (meCells, oppCells, m) {
      var a = projectSheet(meCells || {}, m), b = projectSheet(oppCells || {}, m);
      var s = Math.sqrt(a.variance + b.variance);
      if (s === 0) return a.mean > b.mean ? 1 : a.mean < b.mean ? 0 : 0.5;
      return normCdf((a.mean - b.mean) / s);
    },
    state: function () {
      return { mmActive: mmActive, role: role, roomCode: roomCode, uid: uid, opp: oppData };
    }
  };
})();
