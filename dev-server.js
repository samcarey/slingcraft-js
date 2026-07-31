#!/usr/bin/env node
// Dev server: static files, no caching, live-reload on file change.
// Usage: node dev-server.js [port]
const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');

const ROOT = __dirname;
const PORT = Number(process.argv[2]) || 8080;
// Tests run against a server that must not reload out from under them while
// game.js is being edited. DEV_RELOAD=0 serves plain files.
const RELOAD = process.env.DEV_RELOAD !== '0';

const MIME = {
    '.html': 'text/html; charset=utf-8',
    '.js': 'text/javascript; charset=utf-8',
    '.css': 'text/css; charset=utf-8',
    '.json': 'application/json; charset=utf-8',
    '.png': 'image/png',
    '.jpg': 'image/jpeg',
    '.svg': 'image/svg+xml',
    '.ico': 'image/x-icon',
    '.wasm': 'application/wasm',
};

// Injected into index.html: reconnecting SSE client that reloads on change.
const RELOAD_SNIPPET = `
<script>
(function () {
    let es;
    const connect = () => {
        es = new EventSource('/__reload');
        es.onmessage = (e) => { if (e.data === 'reload') location.reload(); };
        es.onerror = () => { es.close(); setTimeout(connect, 500); };
    };
    connect();
})();
</script>
`;

const clients = new Set();

function broadcastReload() {
    for (const res of clients) res.write('data: reload\n\n');
}

// Coalesce bursty fs events (editors write in several syscalls).
let reloadTimer = null;
function scheduleReload(file) {
    clearTimeout(reloadTimer);
    reloadTimer = setTimeout(() => {
        console.log(`  ↻ ${file} changed — reloading ${clients.size} client(s)`);
        broadcastReload();
    }, 60);
}

if (RELOAD) fs.watch(ROOT, { recursive: true }, (_event, filename) => {
    if (!filename) return;
    if (filename.startsWith('.git') || filename.startsWith('node_modules')) return;
    if (/(\.swp|~|\.tmp)$/.test(filename)) return;
    scheduleReload(filename);
});

const server = http.createServer((req, res) => {
    const url = new URL(req.url, `http://${req.headers.host}`);

    if (url.pathname === '/__reload') {
        res.writeHead(200, {
            'Content-Type': 'text/event-stream',
            'Cache-Control': 'no-cache',
            Connection: 'keep-alive',
            'X-Accel-Buffering': 'no',
        });
        res.write('retry: 500\n\n');
        clients.add(res);
        req.on('close', () => clients.delete(res));
        return;
    }

    let pathname = decodeURIComponent(url.pathname);
    if (pathname.endsWith('/')) pathname += 'index.html';

    const filePath = path.join(ROOT, pathname);
    // Block traversal outside the project root.
    if (!filePath.startsWith(ROOT)) {
        res.writeHead(403).end('Forbidden');
        return;
    }

    fs.readFile(filePath, (err, data) => {
        if (err) {
            res.writeHead(404, { 'Content-Type': 'text/plain' }).end('Not found');
            return;
        }
        const ext = path.extname(filePath).toLowerCase();
        const headers = {
            'Content-Type': MIME[ext] || 'application/octet-stream',
            'Cache-Control': 'no-store, no-cache, must-revalidate',
        };
        if (ext === '.html' && RELOAD) {
            const html = data.toString().replace(/<\/body>/i, `${RELOAD_SNIPPET}</body>`);
            res.writeHead(200, headers).end(html);
        } else {
            res.writeHead(200, headers).end(data);
        }
    });
});

function lanAddresses() {
    return Object.values(os.networkInterfaces())
        .flat()
        .filter((i) => i && i.family === 'IPv4' && !i.internal)
        .map((i) => i.address);
}

server.listen(PORT, '0.0.0.0', () => {
    console.log(`\nSlingCraft dev server (live-reload on)\n`);
    console.log(`  local:   http://localhost:${PORT}`);
    for (const addr of lanAddresses()) {
        console.log(`  phone:   http://${addr}:${PORT}`);
    }
    console.log('');
});
