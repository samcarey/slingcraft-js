/**
 * Shared WebSocket signaling client for WebRTC connection setup.
 * Used by both sender.html and receiver.html.
 */
function createSignaling(room, role) {
  const protocol = location.protocol === 'https:' ? 'wss:' : 'ws:';
  const wsUrl = protocol + '//' + location.host;
  let ws = null;
  let reconnectTimer = null;

  const sig = {
    // Override these in caller
    onStatus: () => {},
    onPeerJoined: () => {},
    onPeerLeft: () => {},
    onOffer: () => {},
    onAnswer: () => {},
    onIceCandidate: () => {},

    send(msg) {
      if (ws && ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify(msg));
      }
    }
  };

  function connect() {
    ws = new WebSocket(wsUrl);

    ws.onopen = () => {
      sig.onStatus('Connected to server. Joining room\u2026', 'status-waiting');
      ws.send(JSON.stringify({ type: 'join', room, role }));
    };

    ws.onmessage = (e) => {
      let msg;
      try {
        msg = JSON.parse(e.data);
      } catch {
        return;
      }

      switch (msg.type) {
        case 'joined':
          sig.onStatus('Waiting for ' + (role === 'sender' ? 'receiver' : 'sender') + '\u2026', 'status-waiting');
          break;
        case 'peer-joined':
          sig.onPeerJoined();
          break;
        case 'peer-left':
          sig.onPeerLeft();
          break;
        case 'offer':
          sig.onOffer(msg.offer);
          break;
        case 'answer':
          sig.onAnswer(msg.answer);
          break;
        case 'ice-candidate':
          sig.onIceCandidate(msg.candidate);
          break;
      }
    };

    ws.onclose = () => {
      sig.onStatus('Disconnected. Reconnecting\u2026', 'status-error');
      scheduleReconnect();
    };

    ws.onerror = () => {
      ws.close();
    };
  }

  function scheduleReconnect() {
    if (reconnectTimer) return;
    reconnectTimer = setTimeout(() => {
      reconnectTimer = null;
      connect();
    }, 2000);
  }

  connect();
  return sig;
}
