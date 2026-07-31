# slingcraft-js

Orbital transfer game. Pick a squadron, pick a destination, and the game searches for a
transfer trajectory through the n-body field.

[Web Demo](https://samcarey.github.io/slingcraft-js/)

No build step — `index.html` loads `game.js` directly as a classic script.

## Development

```sh
npm run dev          # serves on :8081 with live reload on file change
```

The dev server binds all interfaces, so the same URL works from a phone on the same
network — which is the intended way to try touch controls and the mobile layout.

## Tests

```sh
npm test             # full suite, mobile emulation (iPhone 13 + iPhone SE)
npm run test:headed  # watch it drive the browser
```

Playwright starts its own server on :8177; `npm test` clears that port first. Every
scenario runs against a touchscreen mobile viewport, since that is the target device.
Screenshots and traces are written to a temp directory outside the repo — set
`SLINGCRAFT_SHOTS` to put them somewhere browsable.

The suite is CPU-bound rather than IO-bound: each page propagates 18k prediction frames
before transfers are possible, so it runs 2 workers and allows generous per-test
timeouts. A full run takes 10–15 minutes.

## Layout of the code

| File | Contents |
| --- | --- |
| `game.js` | Everything: simulation, transfer search, rendering, UI |
| `transfer-worker.js` | Trajectory search, off the main thread |
| `index.html` | Markup and all styling |
| `dev-server.js` | Static file server with live reload |

Two parts of `game.js` are worth reading before changing them:

- **Display layout and space warp** (banner comment, ~line 294) — the display
  exaggerates body sizes and compresses the distance between them, then warps space to
  match so trajectories and grid lines stay consistent with the exaggerated picture. The
  stability properties it maintains (no fold-over, no body ever crossing another, rigid
  panning) are easy to break by accident; the comments there say which invariant each
  piece exists to protect.
- **`advanceTimeline()`** — maintains the prediction buffer, the shared timeline that
  body motion, craft trajectories and time scrubbing all read from.
