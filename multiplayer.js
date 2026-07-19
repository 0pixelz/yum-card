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
  var OPP_GONE_MS      = 35 * 1000;   // opponent considered gone after this
  var READY_TIMEOUT_MS = 30 * 1000;   // both players must accept within this window

  // ── Runtime state ──────────────────────────────────────────────────────────
  var db = null, auth = null, uid = null, myName = 'Player';
  var mode = 'yum';

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

  // ── Small helpers ───────────────────────────────────────────────────────────
  function $(id) { return document.getElementById(id); }
  function esc(s) {
    return String(s == null ? '' : s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }
  function now() { return Date.now(); }
  function randCode() {
    var chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // no 0/O/1/I
    var s = '';
    for (var i = 0; i < 5; i++) s += chars[Math.floor(Math.random() * chars.length)];
    return s;
  }
  function currentMode() {
    return document.body.classList.contains('mode-yahtzee') ? 'yahtzee' : 'yum';
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
    if (rowId === 'lss') return m === 'yahtzee' ? ROW_LABELS.lss_ya : ROW_LABELS.lss_yum;
    if (rowId === 'lls') return m === 'yahtzee' ? ROW_LABELS.lls_ya : ROW_LABELS.lls_yum;
    return ROW_LABELS[rowId] || rowId;
  }
  function intOf(el) {
    if (!el) return 0;
    var v = parseInt(el.textContent != null ? el.textContent : el.value, 10);
    return isNaN(v) ? 0 : v;
  }
  // Categories that must carry a value (0 = scratched counts) for a sheet to be
  // "complete". Yahtzee bonus (lybonus) is optional — you only fill it if you
  // actually roll extra Yahtzees — so it is excluded from the completion check.
  var REQUIRED = {
    yum: ['u1', 'u2', 'u3', 'u4', 'u5', 'u6', 'l3k', 'l4k', 'lss', 'lls', 'lhr', 'lfh', 'lyum'],
    yahtzee: ['u1', 'u2', 'u3', 'u4', 'u5', 'u6', 'l3k', 'l4k', 'lfh', 'lss', 'lls', 'lyahtzee', 'lchance']
  };
  // Whole-sheet read: the score is the sum of ALL 6 columns (this matches the
  // total yum-card itself shows on the sheet tabs), and `cells` carries every
  // editable entry across all columns keyed by its input id ("u1-1", "l3k-4", …)
  // so the opponent can mirror the full six-column sheet.
  function readMyScore() {
    var grand = 0, upper = 0, lower = 0;
    var grands = [];
    for (var c = 1; c <= 6; c++) {
      var g = intOf($('grand-' + c));
      grand += g; upper += intOf($('uTotal-' + c)); lower += intOf($('lTotal-' + c));
      grands.push(g);
    }
    var cells = {};
    var inputs = document.querySelectorAll('td.input-cell[data-cell] input');
    for (var i = 0; i < inputs.length; i++) {
      var inp = inputs[i];
      if (inp.value !== '') {
        var v = parseInt(inp.value, 10);
        cells[inp.id] = isNaN(v) ? 0 : v;   // key includes the column, e.g. "u6-3"
      }
    }
    // "Complete" = every required category filled in every one of the 6 columns.
    var req = REQUIRED[currentMode()] || REQUIRED.yum;
    var allFilled = true;
    for (var cc = 1; cc <= 6 && allFilled; cc++) {
      for (var r = 0; r < req.length; r++) {
        if (!cells.hasOwnProperty(req[r] + '-' + cc)) { allFilled = false; break; }
      }
    }
    return { grand: grand, upper: upper, lower: lower, grands: grands, cells: cells, allFilled: allFilled };
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
      '.mp-ready-count span{color:var(--green-dark,#235244);font-weight:900}'
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
  }

  function openPanel() {
    buildDom();
    $('mpBackdrop').classList.add('show');
    if (mmActive && roomCode && matchPhase === 'playing') renderMatch();
    else if (mmActive && roomCode && matchPhase === 'ready' && oppData && !oppData.gone) renderReady();
    else if (mmActive && roomCode) renderSearching(T('En attente de l\'adversaire…', 'Waiting for opponent…'));
    else renderLobby();
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
      '<p class="mp-sub">' + T('Affronte un adversaire et voyez vos feuilles en direct.',
                               'Race an opponent and watch each other\'s sheet live.') + '</p>' +
      '<div class="mp-field"><label>' + T('Ton nom', 'Your name') + '</label>' +
        '<div class="mp-row"><input id="mpName" type="text" maxlength="14" value="' + esc(myName) + '" placeholder="' + T('Joueur', 'Player') + '"></div></div>' +
      '<button class="mp-btn primary" id="mpFindBtn">🔎 ' + T('Trouver un adversaire', 'Find a match') + '</button>' +
      '<div class="mp-divider">' + T('OU', 'OR') + '</div>' +
      '<button class="mp-btn accent" id="mpCreateBtn">➕ ' + T('Créer un code d\'ami', 'Create a friend code') + '</button>' +
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

  function renderWaitingCode(code) {
    var s = $('mpSheet');
    if (!s) return;
    s.innerHTML =
      '<h2>' + T('Code d\'ami', 'Friend code') +
        '<button class="mp-close" id="mpCloseBtn">×</button></h2>' +
      '<p class="mp-sub">' + T('Partage ce code. Quand ton ami le saisit, la partie commence.',
                               'Share this code. When your friend enters it, the match starts.') + '</p>' +
      '<div class="mp-code-big" id="mpBigCode">' + esc(code) + '</div>' +
      '<button class="mp-btn accent" id="mpCopyBtn">📋 ' + T('Copier le code', 'Copy code') + '</button>' +
      '<div class="mp-center"><div class="mp-spin"></div><div class="mp-status">' + T('En attente de l\'adversaire…', 'Waiting for opponent…') + '</div></div>' +
      '<button class="mp-btn danger" id="mpCancelBtn">' + T('Annuler', 'Cancel') + '</button>';
    $('mpCloseBtn').addEventListener('click', closePanel);
    $('mpCopyBtn').addEventListener('click', function () {
      try {
        navigator.clipboard.writeText(code);
        this.textContent = '✓ ' + T('Copié', 'Copied');
      } catch (e) {}
    });
    $('mpCancelBtn').addEventListener('click', function () { leaveAll(true); renderLobby(); });
  }

  // ── Match / scoreboard view ─────────────────────────────────────────────────
  var detailsOpen = false;
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
      '<button class="mp-toggle" id="mpDetailsToggle">' + T('Voir la feuille de l\'adversaire (6 colonnes)', 'Show opponent\'s full sheet (6 columns)') + '</button>' +
      '<div class="mp-details" id="mpDetails"></div>' +
      '<button class="mp-btn primary" id="mpRematchBtn" style="display:none"></button>' +
      '<button class="mp-btn accent" id="mpDoneBtn"></button>' +
      '<button class="mp-btn ghost" id="mpNewBtn">🔎 ' + T('Nouvel adversaire', 'New opponent') + '</button>' +
      '<button class="mp-btn danger" id="mpLeaveBtn">' + T('Quitter', 'Leave') + '</button>';
    $('mpCloseBtn').addEventListener('click', closePanel);
    $('mpDetailsToggle').addEventListener('click', function () {
      detailsOpen = !detailsOpen;
      $('mpDetails').classList.toggle('show', detailsOpen);
      this.textContent = detailsOpen
        ? T('Masquer la feuille', 'Hide sheet')
        : T('Voir la feuille de l\'adversaire (6 colonnes)', 'Show opponent\'s full sheet (6 columns)');
      paintScoreboard();
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
        (meLead ? '<span class="crown">👑</span>' : '') +
        '<div class="who">' + esc(myName) + ' (' + T('toi', 'you') + ')</div>' +
        '<div class="tot">' + me.grand + '</div>' +
        '<div class="sub">' + T('Haut', 'Upper') + ' ' + me.upper + ' · ' + T('Bas', 'Lower') + ' ' + me.lower + '</div>' +
        (iAmDone ? '<span class="badge done">✓ ' + T('Terminé', 'Done') + '</span>' : '') +
      '</div>';

    var oppCard;
    if (opp) {
      oppCard =
        '<div class="mp-card' + (oppLead ? ' lead' : '') + '">' +
          (oppLead ? '<span class="crown">👑</span>' : '') +
          '<div class="who">' + esc(opp.name || T('Adversaire', 'Opponent')) + '</div>' +
          '<div class="tot">' + (opp.grand || 0) + '</div>' +
          '<div class="sub">' + T('Haut', 'Upper') + ' ' + (opp.upper || 0) + ' · ' + T('Bas', 'Lower') + ' ' + (opp.lower || 0) + '</div>' +
          ((opp.done || opp.filledAll) ? '<span class="badge done">✓ ' + T('Terminé', 'Done') + '</span>' : '') +
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
    var banner = $('mpGameOver');
    if (banner) {
      if (over) {
        var iWin = me.grand > (opp.grand || 0);
        var tie = me.grand === (opp.grand || 0);
        banner.className = 'mp-gameover show ' + (tie ? 'tie' : (iWin ? 'win' : 'lose'));
        banner.innerHTML = tie
          ? '🤝 ' + T('Match nul ! ', 'It\'s a tie! ') + me.grand + ' – ' + (opp.grand || 0)
          : (iWin
              ? '🎉 ' + T('Tu gagnes ', 'You win ') + me.grand + ' – ' + (opp.grand || 0) + ' !'
              : '😔 ' + T('Tu perds ', 'You lose ') + me.grand + ' – ' + (opp.grand || 0));
      } else {
        banner.className = 'mp-gameover';
        banner.innerHTML = '';
      }
    }

    var status = $('mpMatchStatus');
    if (status) {
      if (over) {
        status.textContent = '';
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
      doneBtn.textContent = iAmDone
        ? T('Annuler « Terminé »', 'Undo "Done"')
        : '🏁 ' + T('J\'ai terminé', 'I\'m done');
    }

    // Rematch: offered once there is a live opponent; prominent at game over.
    var reBtn = $('mpRematchBtn');
    if (reBtn) {
      var oppPresent = opp && !opp.gone;
      var myPending = (rematchVotes[uid] || 0) > roundLocal;
      var theirPending = theirVoteValue() > roundLocal;
      if (!oppPresent) {
        reBtn.style.display = 'none';
      } else if (rematchVoted || myPending) {
        reBtn.style.display = 'block';
        reBtn.disabled = true;
        reBtn.textContent = '⏳ ' + T('En attente de l\'adversaire…', 'Waiting for opponent…');
      } else if (theirPending) {
        reBtn.style.display = 'block';
        reBtn.disabled = false;
        reBtn.textContent = '🔄 ' + T('L\'adversaire veut rejouer — accepter', 'Opponent wants a rematch — accept');
      } else {
        reBtn.style.display = 'block';
        reBtn.disabled = false;
        reBtn.textContent = '🔄 ' + T('Revanche (même adversaire)', 'Rematch (same opponent)');
      }
    }

    var newBtn = $('mpNewBtn');
    if (newBtn) newBtn.style.display = over ? 'block' : 'none';

    if (detailsOpen) paintDetails(me, opp);
  }

  // Row order per mode for the full-sheet mirror (upper 1s–6s, then lower rows).
  var LOWER_ORDER = {
    yum: ['l3k', 'l4k', 'lss', 'lls', 'lhr', 'lfh', 'lyum'],
    yahtzee: ['l3k', 'l4k', 'lfh', 'lss', 'lls', 'lyahtzee', 'lchance', 'lybonus']
  };
  // Recompute a single column's totals from a whole-sheet cells map, mirroring
  // yum-card's own scoring (upper bonus at 63; 25 for Yum, 35 for Yahtzee).
  function colTotals(cells, c, m) {
    var sub = 0;
    for (var n = 1; n <= 6; n++) { var v = cells['u' + n + '-' + c]; if (typeof v === 'number') sub += v; }
    var bonus = sub >= 63 ? (m === 'yahtzee' ? 35 : 25) : 0;
    var upper = (sub > 0 || bonus > 0) ? sub + bonus : 0;
    var lower = 0;
    LOWER_ORDER[m].forEach(function (rid) { var v = cells[rid + '-' + c]; if (typeof v === 'number') lower += v; });
    return { sub: sub, bonus: bonus, upper: upper, lower: lower, grand: upper + lower };
  }
  // Render the opponent's ENTIRE six-column sheet as a compact, scrollable grid.
  function paintDetails(me, opp) {
    var box = $('mpDetails');
    if (!box) return;
    if (!opp) { box.innerHTML = '<div class="mp-sheet-empty">' + T('En attente de l\'adversaire…', 'Waiting for opponent…') + '</div>'; return; }
    var m = currentMode();
    var cells = opp.cells || {};
    var upperRows = ['u1', 'u2', 'u3', 'u4', 'u5', 'u6'];
    var lowerRows = LOWER_ORDER[m];

    function headCells() {
      var h = '<th class="cat"></th>';
      for (var c = 1; c <= 6; c++) h += '<th>' + c + '</th>';
      return h;
    }
    function cellVal(rid, c) {
      var v = cells[rid + '-' + c];
      if (v === undefined) return '';
      return v === 0 ? '<span class="sx">✗</span>' : v;
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

    var html = '<div class="mp-sheet-scroll"><table class="mp-mini"><thead><tr>' + headCells() + '</tr></thead><tbody>';
    upperRows.forEach(function (rid) { html += bodyRow(rid); });
    html += computedRow(T('Boni', 'Bonus'), function (t) { return t.bonus; }, 'sum');
    lowerRows.forEach(function (rid) { html += bodyRow(rid); });
    html += computedRow(T('TOTAL', 'TOTAL'), function (t) { return t.grand; }, 'grand');
    html += '</tbody></table></div>' +
      '<div class="mp-sheet-cap">' + esc(opp.name || T('Adversaire', 'Opponent')) +
      ' — ' + T('total', 'total') + ' ' + (opp.grand || 0) + '</div>';
    box.innerHTML = html;
  }

  // ── Score sync ──────────────────────────────────────────────────────────────
  function scoreSig(sc) {
    return sc.grand + '|' + sc.upper + '|' + sc.lower + '|' + JSON.stringify(sc.cells) +
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
    var cellsStr = JSON.stringify(sc.cells);
    if (cellsStr.length > 3900) cellsStr = '{}';
    myPlayerRef.update({
      grand: sc.grand, upper: sc.upper, lower: sc.lower,
      cells: cellsStr, done: !!iAmDone, filledAll: !!sc.allFilled,
      lastActiveAt: now()
    }).catch(function () {});
    if ($('mpVs')) paintScoreboard();
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
    pushScore();
  }
  function stopScoreSync() {
    if (scoreObserver) { try { scoreObserver.disconnect(); } catch (e) {} scoreObserver = null; }
    if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
  }
  function toggleDone() {
    iAmDone = !iAmDone;
    lastPushSig = null;
    pushScore();
    paintScoreboard();
  }

  // ── Room membership ─────────────────────────────────────────────────────────
  function attachRoom(code) {
    roomCode = code;
    roomRef = db.ref(ROOMS + '/' + code);
    playersRef = roomRef.child('players');
    myPlayerRef = playersRef.child(uid);
    try { myPlayerRef.onDisconnect().remove(); } catch (e) {}
    // Fresh round + ready state whenever we (re)attach.
    rematchVoted = false; rematchVotes = {}; roundLocal = 0; gameOverShown = false;
    matchPhase = 'ready'; readyAccepted = false; readySawOpp = false; matchCanceled = false;

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
      var gone = found.lastActiveAt && (now() - found.lastActiveAt > OPP_GONE_MS);
      oppData = {
        name: found.name, grand: found.grand || 0, upper: found.upper || 0,
        lower: found.lower || 0, done: !!found.done, filledAll: !!found.filledAll,
        ready: !!found.ready, gone: gone, cells: parseCells(found.cells)
      };
    } else if (oppData) {
      oppData.gone = true;
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
    clearReadyCountdown();
    startScoreSync();
    if ($('mpBackdrop') && $('mpBackdrop').classList.contains('show')) renderMatch();
  }

  // ── Ready-check (both players must accept) ──────────────────────────────────
  function renderReady() {
    var s = $('mpSheet');
    if (!s) return;
    var oppName = (oppData && oppData.name) || T('Adversaire', 'Opponent');
    var modeLbl = (mode === 'yahtzee') ? 'Yahtzee' : 'Yum';
    s.innerHTML =
      '<h2>' + T('Adversaire trouvé !', 'Opponent found!') +
        '<button class="mp-close" id="mpCloseBtn">×</button></h2>' +
      '<p class="mp-sub">' + T('Vous devez accepter tous les deux pour commencer. Mode : ',
                               'You both need to accept to start. Mode: ') + modeLbl + '</p>' +
      '<div class="mp-ready">' +
        '<div class="mp-rc"><div class="who">' + esc(myName) + ' (' + T('toi', 'you') + ')</div>' +
          '<div class="chip" id="mpMeChip">' + T('En attente', 'Pending') + '</div></div>' +
        '<div class="mp-rc-vs">VS</div>' +
        '<div class="mp-rc"><div class="who" id="mpOppWho">' + esc(oppName) + '</div>' +
          '<div class="chip" id="mpOppChip">' + T('En attente', 'Pending') + '</div></div>' +
      '</div>' +
      '<div class="mp-ready-count">' + T('Temps restant : ', 'Time left: ') + '<span id="mpReadyCountdown">30s</span></div>' +
      '<button class="mp-btn primary" id="mpAcceptBtn">✅ ' + T('Accepter', 'Accept') + '</button>' +
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
      acc.textContent = meReady
        ? '⏳ ' + T('En attente de l\'adversaire…', 'Waiting for opponent…')
        : '✅ ' + T('Accepter', 'Accept');
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
      label.textContent = T('Adversaire trouvé', 'Opponent found');
    } else if (mmActive && matchPhase === 'playing' && oppData && !oppData.gone) {
      var me = readMyScore();
      label.textContent = me.grand + ' – ' + (oppData.grand || 0);
    } else if (mmActive) {
      label.textContent = T('En partie', 'In match');
    } else {
      label.textContent = T('Multijoueur', 'Multiplayer');
    }
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
        return {
          host: uid,
          createdAt: now(),
          mode: mode,
          createdBy: preferredCode ? 'friend' : 'match',
          players: makeSelfPlayer()
        };
      }).then(function (res) {
        if (res && res.committed) { attachRoom(code); return code; }
        return tryNext();
      });
    }
    return Promise.resolve().then(tryNext);
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
        mode = snap.val().mode || 'yum';
        mmActive = true; role = 'guest'; iAmDone = false; oppData = null;
        return ref.child('players/' + uid).set({
          name: myName.slice(0, 20) || 'Player', uid: uid, joined: now(),
          lastActiveAt: now(), grand: 0, upper: 0, lower: 0, done: false
        }).then(function () {
          attachRoom(code);
          renderReady();
        });
      });
    }).catch(function (e) {
      console.warn('[yumcard-mp] join failed:', e);
      mmActive = false; role = null;
      renderLobby();
      if (e && e.message === 'not-found') showErr(T('Aucune partie avec ce code.', 'No match found for that code.'));
      else showErr(connectErr(e));
    });
  }

  function maybeSuggestMode(m) {
    // If the opponent's room uses a different mode than the local sheet, nudge.
    if (m && m !== currentMode()) {
      var st = $('mpMatchStatus');
      if (st) st.textContent = T('Astuce : ton adversaire joue en mode ' + (m === 'yahtzee' ? 'Yahtzee' : 'Yum') + '.',
                                 'Tip: your opponent is playing ' + (m === 'yahtzee' ? 'Yahtzee' : 'Yum') + ' mode.');
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
    return db.ref(QUEUE + '/' + uid).set({ uid: uid, name: myName.slice(0, 20) || 'Player', ts: now(), mode: mode })
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
          (t - info.ts) < STALE_MS && ((info.mode || 'yum') === mode) &&
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
    clearTimers();
    clearReadyCountdown();
    detachQueueWatcher();
    detachOfferListener();
    if (roomRef && playersListener) { try { roomRef.off('value', playersListener); } catch (e) {} }
    playersListener = null;

    if (db && uid) {
      db.ref(QUEUE + '/' + uid).remove().catch(function () {});
      db.ref(OFFERS + '/' + uid).remove().catch(function () {});
      if (removeRoomData && roomCode) {
        try { myPlayerRef && myPlayerRef.onDisconnect().cancel(); } catch (e) {}
        db.ref(ROOMS + '/' + roomCode + '/rematch/' + uid).remove().catch(function () {});
        db.ref(ROOMS + '/' + roomCode + '/players/' + uid).remove().catch(function () {});
        // If we're the host and now alone, drop the room.
        if (role === 'host') {
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
    window.addEventListener('beforeunload', function () { leaveAll(true); });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }

  // Expose a tiny hook for debugging/tests.
  window.yumCardMP = {
    open: openPanel,
    state: function () {
      return { mmActive: mmActive, role: role, roomCode: roomCode, uid: uid, opp: oppData };
    }
  };
})();
