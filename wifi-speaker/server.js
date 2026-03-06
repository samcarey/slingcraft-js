const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;

const MIME_TYPES = {
  '.html': 'text/html',
  '.css': 'text/css',
  '.js': 'application/javascript',
  '.json': 'application/json',
  '.png': 'image/png',
  '.svg': 'image/svg+xml',
};

// Simple static file server
const server = http.createServer((req, res) => {
  let filePath = req.url === '/' ? '/index.html' : req.url;
  filePath = path.join(__dirname, 'public', filePath);

  const ext = path.extname(filePath);
  const contentType = MIME_TYPES[ext] || 'application/octet-stream';

  fs.readFile(filePath, (err, data) => {
    if (err) {
      res.writeHead(404);
      res.end('Not found');
      return;
    }
    res.writeHead(200, { 'Content-Type': contentType });
    res.end(data);
  });
});

// WebSocket signaling server for WebRTC
const wss = new WebSocketServer({ server });

// Room management: each room has a sender and a receiver
const rooms = new Map();

wss.on('connection', (ws) => {
  let currentRoom = null;
  let currentRole = null;

  ws.on('message', (data) => {
    let msg;
    try {
      msg = JSON.parse(data);
    } catch {
      return;
    }

    switch (msg.type) {
      case 'join': {
        const roomId = msg.room;
        const role = msg.role; // 'sender' or 'receiver'

        if (!rooms.has(roomId)) {
          rooms.set(roomId, { sender: null, receiver: null });
        }

        const room = rooms.get(roomId);
        room[role] = ws;
        currentRoom = roomId;
        currentRole = role;

        // Notify the peer that someone joined
        const peerRole = role === 'sender' ? 'receiver' : 'sender';
        const peer = room[peerRole];

        ws.send(JSON.stringify({ type: 'joined', role, room: roomId }));

        if (peer && peer.readyState === 1) {
          // Both sides are connected, notify them
          ws.send(JSON.stringify({ type: 'peer-joined', peerRole }));
          peer.send(JSON.stringify({ type: 'peer-joined', peerRole: role }));
        }
        break;
      }

      case 'offer':
      case 'answer':
      case 'ice-candidate': {
        // Forward signaling messages to the peer
        if (!currentRoom || !rooms.has(currentRoom)) break;
        const room = rooms.get(currentRoom);
        const peerRole = currentRole === 'sender' ? 'receiver' : 'sender';
        const peer = room[peerRole];
        if (peer && peer.readyState === 1) {
          peer.send(JSON.stringify(msg));
        }
        break;
      }
    }
  });

  ws.on('close', () => {
    if (currentRoom && rooms.has(currentRoom)) {
      const room = rooms.get(currentRoom);
      room[currentRole] = null;

      // Notify peer of disconnect
      const peerRole = currentRole === 'sender' ? 'receiver' : 'sender';
      const peer = room[peerRole];
      if (peer && peer.readyState === 1) {
        peer.send(JSON.stringify({ type: 'peer-left', peerRole: currentRole }));
      }

      // Clean up empty rooms
      if (!room.sender && !room.receiver) {
        rooms.delete(currentRoom);
      }
    }
  });
});

server.listen(PORT, () => {
  console.log(`WiFi Speaker server running at http://localhost:${PORT}`);
  console.log(`Open http://localhost:${PORT} in your browser to get started.`);
});
