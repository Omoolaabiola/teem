// TEEM Service Worker - Offline PWA Support v16
const CACHE_NAME = 'teem-concession-v16';
const PRECACHE = [
  './',
  './index.html',
  './style.css',
  './app.js',
  './cloud/config.js',
  './assets/embedded_images.js',
  './assets/jspdf.umd.min.js',
  './assets/teem_logo_standalone.png',
  './assets/teem_logo_light.png',
  './assets/icon-192.png',
  './assets/icon-512.png',
  './manifest.json',
  './version.json'
];

self.addEventListener('install', event => {
  event.waitUntil(
    caches.open(CACHE_NAME)
      // Cache each file on its own. One missing file used to make addAll()
      // reject and the whole service worker never install, which silently
      // killed offline support.
      .then(cache => Promise.all(
        PRECACHE.map(url => cache.add(url).catch(() => null))
      ))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', event => {
  event.waitUntil(
    caches.keys()
      .then(keys => Promise.all(keys.filter(k => k !== CACHE_NAME).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

// Network-first with offline cache fallback; never cache live Supabase or Google Apps Script sync endpoints.
self.addEventListener('fetch', event => {
  if (event.request.method !== 'GET') return;
  const reqUrl = event.request.url || '';
  if (reqUrl.indexOf('supabase.co') !== -1 || reqUrl.indexOf('script.google.com') !== -1 || reqUrl.indexOf('googleusercontent.com') !== -1) {
    return;
  }
  event.respondWith(
    fetch(event.request)
      .then(response => {
        if (response && response.ok) {
          const copy = response.clone();
          caches.open(CACHE_NAME).then(cache => cache.put(event.request, copy)).catch(() => {});
        }
        return response;
      })
      .catch(() => caches.match(event.request).then(cached => cached || caches.match('./index.html')))
  );
});
