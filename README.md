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
| Drag across the plotted routes | Pick one, and read off how long it takes |
| Tap a rocket still waiting to launch | Reopen its launch controls to change or cancel it |
| Drag from anywhere else | Pan |
| Tap empty sky | Deselect, and let the view auto-fit again |
| Pinch | Zoom |

Selection is the gate: dragging off a body you have not selected pans, so the map stays
draggable everywhere. Holding is how you get through that gate mid-gesture, without
having to tap and press again. A selected body with no craft also pans, because there
is nothing there to send — tap it to see its count and build some. Release over empty
space to cancel. The star is never a destination.

### Craft

Craft sitting at a body are just a number beside it, with the body's name written under
the number. There is nothing else to draw: a parked fleet is held to be at no particular
point on its orbit, and can cast off from wherever suits. A squadron — a thing with a
position, drawn as a rocket trailing its path — exists only between two bodies. Arriving,
it stops being one and its craft join the destination's total.

The rocket carries the whole fleet's number on its hull, angled with it, and points where
that fleet is going. Between being launched and actually leaving it stands on the rim of
its origin, bobbing along its own nose; when the launch moment comes it stops bobbing and
starts down the path. Whatever is on the rocket is not also beside the body — the number
there is the craft still free to be sent somewhere.

### Where the planets will be

Bodies draw their future orbits, but only while there is a reason to ask: as long as
something is in the air, or a route is being chosen, every body's path is drawn from
where it is now out to the moment those craft arrive — and then it stops. All the lines
end at the same moment, so the picture reads as one question: where will everything be
when they get there. With nothing flying and nothing being planned, the map is clear.

They are dashed, which keeps them a different kind of line from a craft's flight — those
are solid, and they are the ones being decided about. The dashes are counted from the
arrival end, so they stay put on the curve as time eats the near end away.

A flight takes over an hour of game time, so watching one land means running the clock
forward. Craft that have landed at the moment you are looking at can be sent straight on
from there, without waiting for the present to catch up: what a body will let you drag is
always the number drawn beside it.

### Choosing a transfer

Planning a transfer draws every workable way of getting there, all at once, as a fan of
routes leaving the origin. Each is a different **release angle**: which way round the
orbit the craft let go, and its own colour, so you can follow one strand through a
crossing. Drag a finger across them to pick one; the chosen route comes forward at full
strength while the rest stay translucent behind it, and a label rides alongside it — in
the same colour — with the flight time. The quickest route is picked for you to begin
with, so releasing without dragging sends the craft the fast way.

All of them leave at the moment the clock is showing, and planning a transfer sets that
clock ten minutes ahead of the present — you are choosing a launch that is still coming,
not one going past while you decide. The readout counts it down, and if it reaches you
while the controls are still up it is pushed out ten minutes again, so there is always a
window left to reach. Opening a transfer with the clock already further out than that
leaves it where you put it.

A rocket stands on the origin the whole time you are choosing, pointing down whichever
route is picked and carrying whatever number the slider is on. It is the transfer as it
would be if you launched it now, so pressing Launch changes what it is and not where it is.

Launching does not send the craft off there and then — they leave at the moment you chose,
and the clock goes back to where it was so you can watch them wait for it. Move the wheel
yourself while choosing and it stays where you left it instead.

Until it goes, the decision is still yours: tap the waiting rocket, or the path it is going
to fly, and the launch controls come back with the same route, the same moment and the same
number. Send fewer, send more, or cancel and keep them all. Reopening unmakes the launch
while you are deciding, so the craft are home and free until you press Launch again.

Move the time wheel and the whole fan is worked out again for the new moment — so the
wheel is how you hunt for a good window, and the fan is how you choose within it. Some
moments offer a dozen routes, some none at all; if the readout says there is no route,
try the clock. Winding the clock all the way back to the present is allowed and sticks:
the lead is put back when time catches up with the launch, not when you go to meet it.

While you are choosing, the map takes itself over: it eases into the to-scale view below,
and the camera frames the two bodies and whichever route is currently picked. A route is a
shape — how far out it swings, how much of the system it crosses — and the playing view
lies about exactly the quantities that shape is made of, so this is the one moment worth
being honest for. It holds still under a finger sweeping the fan and re-frames when you
lift. Launch or cancel and both the scale and the view you had come back; pinch or pan at
any point and the map is yours again for the rest of that transfer.

### The to-scale view

The map you play on lies about size and distance so the system is readable at all (see
"Display layout and space warp" below). The 📏 button, left of the clock, eases that
away over a second and shows the system as the simulation actually holds it: true radii,
true separations, straight grid. Press it again to come back.

It is a viewing mode, not a game mode — the simulation, the transfer search and every
gesture behave identically in it. Bodies keep their finger-sized tap targets even when
drawn at well under a pixel, so the map stays playable when it is honest.

Planning a transfer turns it on by itself and turns it off again afterwards. Pressing the
button while planning takes that decision back off the game: whatever you set it to is
what it stays.

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

A page is ready to plan transfers as soon as it loads — the 18k-frame prediction buffer
is built in one go on the first frame, a few milliseconds — so a full run is about three
and a half minutes, most of it browser startup and the deliberate waits in the gesture
tests. It runs 2 workers and allows generous per-test timeouts.

`g.waitForTrajectories()` moves the clock forward when the moment in view has no launch
window, which is what the readout tells a player to do. Prefer it to `waitForScan()`
unless the test is specifically about the no-route case: a test that assumes the opening
moment has a window is really depending on how long its own setup took, and will be
stranded the next time that changes.

Anything that has to land where a player's finger could actually reach uses
`g.dragReal()`, which drives real touch through the browser's input pipeline.
`g.dragTouch()` dispatches synthetic events straight at the SVG, which skips hit-testing
and will happily "touch" a point covered by a panel — fine for the body-to-body gestures,
useless for the route fan.

## Layout of the code

| File | Contents |
| --- | --- |
| `game.js` | Everything: simulation, transfer search, rendering, UI |
| `transfer-worker.js` | The release-angle sweep, sharded across the worker pool |
| `index.html` | Markup and all styling |
| `dev-server.js` | Static file server with live reload |

Four parts of `game.js` are worth reading before changing them:

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
- **Transfer search** (banner comment above `initWorkerPool`) — sweeps release angles at
  one moment rather than launch times across many, which is what makes a scan cheap
  enough to redo whenever the time wheel moves. It pairs with **Craft at a body** (banner
  above `bodyDisplayCraftCount`): the search assumes a parked fleet has no orbital phase,
  and that section is what makes sure nothing stores one. Changing either alone will make
  the game assert two contradictory things about where craft are.
- **`advanceTimeline()`** — maintains the prediction buffer, the shared timeline that
  body motion, craft trajectories and time scrubbing all read from. The first fill is
  deliberately unbudgeted: everything drawn is fitted to the extent of the orbits in the
  buffer, so filling it gradually means framing a picture that is still growing.

`transfer-worker.js` carries its own reasoning at the top, and two constants there set
the whole character of the search: `ANGLE_SECTORS` (how many distinguishable routes a fan
offers, and what a scan costs) and `POST_OPTIMIZATION_THRESHOLD` (what counts as arriving
at all). The optimizer minimises arrival time subject to that threshold — see the weights
above `objective`.
