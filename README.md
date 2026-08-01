# slingcraft-js

Orbital transfer game. Drag from a body you have craft on to where you want them, and
the game searches for a transfer trajectory through the n-body field.

[Web Demo](https://samcarey.github.io/slingcraft-js/)

No build step — `index.html` loads `game.js` directly as a classic script.

## Playing

The map is the whole interface; there is no transfer menu.

The usual flow is one uninterrupted press: **hold a planet until it lights up, then —
without lifting — drag to another planet and release.** That plans a transfer between
the two and opens the launch-window controls.

| Gesture | What it does |
| --- | --- |
| Tap a body | Select it — shows its craft count and lets you build more |
| Hold a body | Selects it under your finger, before you lift |
| Drag from a **selected** body with craft | Plan a transfer to whatever you release on |
| Drag from anywhere else | Pan |
| Tap empty sky | Deselect, and let the view auto-fit again |
| Pinch | Zoom |

Selection is the gate: dragging off a body you have not selected pans, so the map stays
draggable everywhere. Holding is how you get through that gate mid-gesture, without
having to tap and press again. A selected body with no craft also pans, because there
is nothing there to send — tap it to see its count and build some. Release over empty
space to cancel. The star is never a destination.

### The to-scale view

The map you play on lies about size and distance so the system is readable at all (see
"Display layout and space warp" below). The 📏 button, left of the clock, eases that
away over a second and shows the system as the simulation actually holds it: true radii,
true separations, straight grid. Press it again to come back.

It is a viewing mode, not a game mode — the simulation, the transfer search and every
gesture behave identically in it. Bodies keep their finger-sized tap targets even when
drawn at well under a pixel, so the map stays playable when it is honest.

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

Three parts of `game.js` are worth reading before changing them:

- **Display layout and space warp** (banner comment, above `getDisplayLayout`) — the
  display exaggerates body sizes and compresses the distance between them, then warps
  space to match so trajectories and grid lines stay consistent with the exaggerated
  picture. The stability properties it maintains (no fold-over, no body ever crossing
  another, rigid panning) are easy to break by accident; the comments there say which
  invariant each piece exists to protect. `trueScale` (see the "True-scale toggle"
  banner just above it) is how much of the whole scheme is switched off — the drawn
  radius and the laid-out position both retreat on that one number, and the warp
  flattens to the identity on its own as they converge.
- **Transfer drag gesture** (banner comment above `bodyCanSend`) — decides which press
  becomes a pan, which becomes a selection, and which becomes a transfer. Mouse and
  touch both route through `pressOnMap`/`moveOnMap`/`releaseOnMap` so the two input
  paths cannot drift apart; change the rules there, not in the four event handlers.
- **`advanceTimeline()`** — maintains the prediction buffer, the shared timeline that
  body motion, craft trajectories and time scrubbing all read from.
