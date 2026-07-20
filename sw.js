// ─── yum-card service worker ────────────────────────────────────────────────
// Makes the score sheet installable and usable offline (solo play). Strategy:
//   • HTML / JS / CSS  → network-first, fall back to cache  (so online players
//     always get the latest deploy; offline still loads the app)
//   • icons / manifest → cache-first, refreshed in the background
//   • cross-origin (Firebase SDK, RTDB) → not intercepted; online multiplayer
//     naturally needs the network.
// Bump CACHE when you want to force-evict old cached shells.

const CACHE = 'yumcard-v1';
const SHELL = [
  './',
  './index.html',
  './dice-3d-throw.js',
  './multiplayer.js',
  './manifest.json',
  './icons/icon-192.png',
  './icons/icon-512.png',
  './icons/maskable-512.png',
  './icons/apple-touch-icon.png'
];

self.addEventListener('install', (e) => {
  e.waitUntil(
    caches.open(CACHE).then((c) => c.addAll(SHELL)).then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', (e) => {
  e.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

self.addEventListener('message', (e) => {
  if (e.data === 'skipWaiting') self.skipWaiting();
});

self.addEventListener('fetch', (e) => {
  const req = e.request;
  if (req.method !== 'GET') return;

  const url = new URL(req.url);
  // Let cross-origin requests (gstatic Firebase SDK, RTDB, reCAPTCHA) go straight
  // to the network — they must not be served from cache.
  if (url.origin !== self.location.origin) return;

  const isAsset = /\.(png|jpg|jpeg|gif|svg|ico|webp|json|webmanifest)$/i.test(url.pathname);

  if (isAsset) {
    // cache-first, refresh in background
    e.respondWith(
      caches.match(req).then((hit) => {
        const net = fetch(req).then((res) => {
          if (res && res.ok) {
            const copy = res.clone();
            caches.open(CACHE).then((c) => c.put(req, copy));
          }
          return res;
        }).catch(() => hit);
        return hit || net;
      })
    );
    return;
  }

  // navigations + html/js/css: network-first, fall back to cache, then app shell
  e.respondWith(
    fetch(req).then((res) => {
      if (res && res.ok) {
        const copy = res.clone();
        caches.open(CACHE).then((c) => c.put(req, copy));
      }
      return res;
    }).catch(() =>
      caches.match(req).then((hit) => hit || caches.match('./index.html'))
    )
  );
});
