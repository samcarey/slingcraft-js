// SlingCraft - JavaScript Version (SVG Rendering)
// A space simulation with N-body gravitational physics

// In-app log buffer (viewable in Build Info → Logs tab)
const _logBuffer = [];
const _LOG_MAX = 500;
const _origConsoleLog = console.log;
console.log = function(...args) {
    _origConsoleLog.apply(console, args);
    const line = args.map(a => typeof a === 'string' ? a : JSON.stringify(a)).join(' ');
    _logBuffer.push(line);
    if (_logBuffer.length > _LOG_MAX) _logBuffer.shift();
};

const svg = document.getElementById('game-svg');
const gridLayer = document.getElementById('grid-layer');
const trajectoriesLayer = document.getElementById('trajectories-layer');
const bodiesLayer = document.getElementById('bodies-layer');
const uiLayer = document.getElementById('ui-layer');
const defs = svg.querySelector('defs');


// Constants
const G = 50.0; // Gravitational constant
const MIN_DISTANCE = 10; // Minimum distance to prevent singularities
const DENSITY = 0.00075; // Default density for mass calculation

// Prediction constants
const PREDICTION_TIME = 1800; // Predict 1800 minutes ahead
const PREDICTION_DT = 0.1; // Fixed timestep for prediction (minutes)
const PREDICTION_FRAMES = Math.ceil(PREDICTION_TIME / PREDICTION_DT);
const MAX_CRAFT_PREDICTION_FRAMES = Math.ceil(PREDICTION_FRAMES / 4); // Craft trajectories predict quarter as far
const PREDICTION_DT_DECIMALS = Math.max(0, -Math.floor(Math.log10(PREDICTION_DT))); // Display precision derived from timestep
const MAX_TRAJECTORY_POINTS = 400; // Max points to render for solid portion
const MAX_CATCHUP_FRAMES = 100; // Max frames to simulate per render frame

// Craft constants
const CRAFT_ORBITAL_ALTITUDE = 5;  // Simulation units above body surface
const CRAFT_ACCELERATION = 2.5;    // Tunable acceleration magnitude
const CRAFT_COUNT_GAP_PX = 5;      // Space between a body's rim and its craft total
const BODY_LABEL_DROP_PX = 4;      // How far the name hangs below the body's centre line

// Body display sizing
// Bodies are drawn at an exaggerated radius when zoomed out so every one stays visible
// and finger-tappable, then relax to their true size as the zoom makes them big enough.
const BODY_MIN_SCREEN_RADIUS = 10.5; // px: no body ever draws smaller than this
const BODY_SIZE_SPREAD = 3;         // largest exaggerated body = 3x the smallest
const BODY_SIZE_BLEND = 8;          // smooth-max sharpness; higher = tighter knee at the crossover
const BODY_TAP_MIN_RADIUS = 22;     // px: hit-test floor (44px tap diameter, the iOS minimum)
const BODY_TAP_SLOP = 6;            // px: extra forgiveness outside the drawn edge

// A squadron is drawn as a rocket, sized off the smallest a body is ever allowed to draw
// so it reads as a craft beside a planet without competing with one — a little under the
// smallest disc on the map. A fixed screen size, like every other icon here: it says how
// many craft and which way they are going, not how big they are.
const ROCKET_LENGTH_PX = 0.8 * 2 * BODY_MIN_SCREEN_RADIUS;
const ROCKET_WIDTH_PX = 0.52 * ROCKET_LENGTH_PX;
const ROCKET_BOB_PERIOD_MS = 1700; // one full back-and-forth while it waits to go
const ROCKET_BOB_FRACTION = 0.10;  // peak-to-peak travel, as a fraction of the length
const ROCKET_TAP_RADIUS = 11;      // px: how close a tap has to land to count as on it
const ROCKET_HEADING_FRAMES = 4;   // path frames either side used to read off the heading

// How far the pointer may travel and still count as a tap rather than a pan. Move
// further than this and the press pans the view and selects nothing, so a drag
// that happens to start on a body does not select it.
const CLICK_SLOP_PX = 5;            // px: mouse, which lands where you aim it
const TAP_SLOP_PX = 12;             // px: finger, which rolls a little on release

// Hold a body this long and it selects under your finger, without lifting.
const TRANSFER_HOLD_MS = 350;

// Display layout + space warp (see "Display layout and space warp" section)
const BODY_GAP_PX = 0.6 * BODY_TAP_MIN_RADIUS; // px: min gap between drawn discs (~13px)
const LOG_RADIAL_WINDOW = 90; // px: radial slack that maps 1:1 before log compression
const WARP_SIGMA_MULT = 2;          // bump falloff radius = this x the body's drawn radius
const WARP_SCALE_CAP = 3.5;         // max magnification a bump exerts on passing curves;
                                    // the full drawn/true ratio (up to ~20x for moons at
                                    // wide zoom) would kick tangentially passing
                                    // trajectories into huge perpendicular lobes, and
                                    // past ~6 even the rational profile's decay ring
                                    // would fold (parallel grid lines crossing)
const WARP_FLOW_STEPS = 20;         // integration steps for the diffeomorphic flow; each
                                    // step's gradients shrink ~1/K, keeping every step
                                    // injective so the composition cannot fold
const WARP_SIGMA_PER_PUSH = 0.5;    // bump width floor as a fraction of its travel, so
                                    // per-step velocity stays small next to bump reach
                                    // (travel budget = 0.3*sigma*steps must exceed 1x)
const TRUE_SCALE_EASE_MS = 1000;    // full toggle between the two views; a reversal
                                    // mid-flight takes proportionally less

// Framing the route being chosen (see "Choosing a transfer, at true scale")
const TRANSFER_FIT_PAD_PX = 20;      // clear space kept around the framed route
const TRANSFER_FIT_EASE = 0.18;      // per-frame fraction of the remaining distance
const TRANSFER_FIT_STEPS = 4;        // fixed-point passes per solve; one is exact once the
                                     // warp has flattened, the rest carry the morph across
const TRANSFER_FIT_SAMPLES = 64;     // points off the chosen route the fit measures
const GRID_WARP_SAMPLE_PX = 48;     // base px between grid-line samples (flat regions)
const GRID_FLATNESS_PX = 0.5;       // subdivide while the true curve deviates from the
                                    // drawn chord by more than this
const GRID_SUBDIV_DEPTH = 7;        // halving limit: 48px base -> ~0.4px finest

// Planet lore, shown in the selected-body panel
const planetLore = {
    'Sol': {
        desc: 'An ancient stellar furnace at the heart of the system. Its gravitational well anchors all orbital paths.',
        stats: 'Classification: G-type Main Sequence'
    },
    'Ember': {
        desc: 'A scorched inner world where molten rivers carve canyons through basalt plains. Once a thriving mining colony before the Great Flare.',
        stats: 'Surface: Volcanic basalt'
    },
    'Terra': {
        desc: 'The blue marble — cradle of the first spacefarers. Its orbital dockyards still echo with the hum of ion drives.',
        stats: 'Biome: Oceanic temperate'
    },
    'Luna': {
        desc: 'Terra\'s pale companion, pocked with craters that hide subterranean vaults of pre-war archives.',
        stats: 'Surface: Regolith plains'
    },
    'Gaia': {
        desc: 'A verdant giant wrapped in chlorophyll clouds. Its forests span continents and its roots reach the mantle.',
        stats: 'Biome: Hyper-temperate'
    },
    'Aria': {
        desc: 'Gaia\'s inner moon, where crystalline caves resonate with harmonic frequencies. Monks once meditated here for decades.',
        stats: 'Surface: Crystalline'
    },
    'Nyx': {
        desc: 'The dark outer moon of Gaia, perpetually in shadow. Its surface hides frozen methane lakes and smuggler outposts.',
        stats: 'Surface: Frozen methane'
    }
};

// Game state
let bodies = [];
let squadrons = []; // In-flight or planned-transfer craft groups
let selectedBody = null;
let selectedSquadron = null;
let hoveredBody = null;
let bodyInfoExpanded = false;
const SIM_SPEED = 0.1 / 6; // 0.1 sim-minutes per 6 real seconds
let lastTime = 0;

// Transfer drag: the gesture that plans a transfer. Drag off a body that is
// already selected and has craft, then release on another body.
let transferDrag = null;          // { source, x, y, target } while a drag is in flight
let transferHoldTimer = null;     // pending press-and-hold that would select under the finger
let fanDrag = false;              // finger is sweeping across the fan of candidate transfers
let fanDragBody = null;           // body the sweep started on top of, if any — see releaseOnMap
// Time scrub state - offset in frames into the prediction buffer for viewing future positions
let timeViewOffset = 0; // 0 = current time, positive = looking into future
let timeScrubPanelOpen = false;
// 15 degrees of wheel rotation per single timestep. Module scope because the clock is
// now moved from outside the wheel's own handlers too, and the ring has to turn by the
// same amount however the time was set.
const FRAMES_PER_RADIAN = 6 / (Math.PI / 12);
// Kills a coasting fling. Filled in by init() once the wheel's momentum state exists;
// until then there is nothing spinning to stop.
let stopWheelCoast = () => {};
// Transfer planning state. The fan of candidate release angles and the worker pool that
// finds it live together under the "Transfer search" banner further down.
let transferState = 'none'; // 'none', 'searching', 'ready'
let transferSourceBody = null;
let transferDestinationBody = null;
let transferQtyTouched = false; // true once the player has moved the quantity slider this search
// The view while a transfer is being chosen — see "Choosing a transfer, at true scale"
// above fitTransferSelection.
let scaleBeforeTransfer = null;   // trueScaleOn as the player had it, or null when not planning
let cameraBeforeTransfer = null;  // where they were looking, to give back afterwards
let transferViewReleased = false; // player has moved the view by hand, so the fit lets go
let viewRestore = null;           // {x, y, zoom} the camera is easing back to, or null
// The clock is borrowed the same way: a transfer sets it forward to the launch lead, so it
// owes the moment it took. Both are buffer frames and both are kept pointing at the same
// physical moment as the buffer shifts, exactly as timeViewOffset is.
let clockBeforeTransfer = null;   // where the clock was before a transfer moved it, or null
let clockSetByTransfer = -1;      // the moment it was moved to; -1 when nothing is owed

// Scheduled transfers - tracks pending launches (squadron already exists)
// Each: { squadron, sourceBody, destBody }
// The squadron has launchFrame>0 and its full trajectory in trajectoryBuffer.
let scheduledTransfers = [];

// CPU benchmark state
let benchmarkEnabled = true;
let benchmarkLastReportTime = 0;
let benchmarkTotalWorkTime = 0;
let benchmarkFrameCount = 0;

// Cached SVG dimensions (avoids layout-thrashing getBoundingClientRect calls)
let svgWidth = svg.getBoundingClientRect().width;
let svgHeight = svg.getBoundingClientRect().height;
window.addEventListener('resize', () => {
    const rect = svg.getBoundingClientRect();
    svgWidth = rect.width;
    svgHeight = rect.height;
});

// Camera/view state
let camera = {
    x: 0,
    y: 0,
    zoom: 1
};

// Zoom limits
const MIN_ZOOM = 0.02;
const MAX_ZOOM = 5;

// Drag state for panning
let isDragging = false;
let dragStart = { x: 0, y: 0 };
let cameraStart = { x: 0, y: 0 };

// Touch state for pinch-to-zoom
let touchState = {
    active: false,
    lastTouches: [],
    lastPinchDist: 0,
    lastPinchCenter: { x: 0, y: 0 }
};

// Auto-fit state - paused when user manually pans/zooms
let isAutoFitPaused = false;

// Track whether we're actively following the selected craft's trajectory
let isTrackingSelectedSquadron = false;

// Prediction state
// predictionBuffer[frameIndex][bodyIndex] = {x, y, vx, vy}
let predictionBuffer = [];
let predictionTimeAccum = 0; // Accumulated time for popping frames
let sampleOffset = 0; // Offset for consistent trajectory sampling

// SVG namespace
const SVG_NS = 'http://www.w3.org/2000/svg';
// What is written beside a body — its craft total and its name — lives in the topmost
// layer rather than inside the body's own group.
//
// A body draws its own children in order, but bodies are siblings — so writing belonging
// to one body sat under every body, trajectory and squadron drawn after it, and the number
// the player is actually reading was the thing most likely to be buried. Up here nothing on
// the map can cover it. Contrast against whatever it lands on comes from the outline in the
// CSS, not from layering.
//
// The name goes here too, not just the number: the two are stacked into one block now, and
// a block whose top half can never be covered and whose bottom half can would read as
// broken rather than as layered.
const bodyAnnotations = document.createElementNS(SVG_NS, 'g');
uiLayer.appendChild(bodyAnnotations);

// --- True-scale toggle ---------------------------------------------------
// The display normally tells two lies at once: it draws bodies far larger than they are
// and pulls them far closer together than they are (see "Display layout and space warp").
// `trueScale` is how much of that is switched off — 0 is the readable schematic, 1 is the
// honest picture, where radii and separations are both exactly what the simulation uses.
//
// It is ONE number because the two lies have to retreat together. Shrink the discs while
// the layout still holds them apart and the system reads as a set of pinpricks parked at
// schematic distances, which is a third picture that is true to nothing. Both the drawn
// radius and the laid-out position lerp on this same value, and the warp needs no case of
// its own: it is built to carry true positions to display positions, so as those converge
// it flattens to the identity on its own.
let trueScale = 0;
let trueScaleOn = false;
let trueScaleAnim = null;   // {from, to, t0, ms} while easing, else null

// Ease the toggle forward. Duration scales with the distance left to travel, so a full
// switch takes TRUE_SCALE_EASE_MS and a change of mind partway across comes back at the
// same speed instead of crawling.
function setTrueScale(on, timestamp) {
    if (on === trueScaleOn) return;
    trueScaleOn = on;
    const to = on ? 1 : 0;
    trueScaleAnim = { from: trueScale, to, t0: timestamp, ms: TRUE_SCALE_EASE_MS * Math.abs(to - trueScale) };
    document.getElementById('true-scale-btn').classList.toggle('active', on);
}

function advanceTrueScale(timestamp) {
    if (!trueScaleAnim) return;
    const { from, to, t0, ms } = trueScaleAnim;
    const u = ms > 0 ? Math.min(1, (timestamp - t0) / ms) : 1;
    // Cubic ease-in-out: starts and ends at rest, so neither end of the transition
    // looks like the picture was yanked.
    const e = u < 0.5 ? 4 * u * u * u : 1 - Math.pow(-2 * u + 2, 3) / 2;
    trueScale = from + (to - from) * e;
    if (u >= 1) { trueScale = to; trueScaleAnim = null; }
}

// --- Body display sizing -------------------------------------------------
// Every body gets an "exaggerated" screen radius: a fixed ladder that puts the smallest
// body at BODY_MIN_SCREEN_RADIUS and the largest at BODY_SIZE_SPREAD x that, spaced
// logarithmically so the true ordering of sizes stays readable after compression.
// The drawn radius is a smooth maximum of that ladder value and the body's true screen
// size, so a body grows continuously past its exaggerated size as you zoom in and no
// body ever snaps between regimes.
let bodyRadiusRange = null;

function getBodyRadiusRange() {
    if (bodyRadiusRange && bodyRadiusRange.count === bodies.length) return bodyRadiusRange;
    let min = Infinity, max = -Infinity;
    for (const b of bodies) {
        if (b.radius < min) min = b.radius;
        if (b.radius > max) max = b.radius;
    }
    bodyRadiusRange = { count: bodies.length, min, max };
    return bodyRadiusRange;
}

// Fixed, zoom-independent target size for a body in the exaggerated regime.
function bodyExaggeratedRadius(body) {
    const range = getBodyRadiusRange();
    if (!isFinite(range.min) || range.max <= range.min) return BODY_MIN_SCREEN_RADIUS;
    // Position of this body in the size ladder, 0 = smallest, 1 = largest
    const t = Math.log(body.radius / range.min) / Math.log(range.max / range.min);
    return BODY_MIN_SCREEN_RADIUS * Math.pow(BODY_SIZE_SPREAD, t);
}

// Radius the body is actually drawn at, in screen pixels.
function bodyScreenRadius(body) {
    const trueRadius = body.radius * camera.zoom;
    if (trueScale >= 1) return trueRadius;
    const floorRadius = bodyExaggeratedRadius(body);
    // Smooth max: ~= floorRadius when zoomed out, ~= trueRadius once zoomed in, with a
    // rounded transition instead of a kink. Monotonic in both zoom and body size, so
    // bodies never reorder and nothing pops as the camera moves.
    const k = BODY_SIZE_BLEND;
    const exaggerated = Math.pow(Math.pow(floorRadius, k) + Math.pow(trueRadius, k), 1 / k);
    // Lerped, not blended geometrically: a moon's true radius can be a hundredth of its
    // exaggerated one, and a geometric path would collapse it to a speck in the first
    // fifth of the transition and then have nothing left to animate.
    return exaggerated + (trueRadius - exaggerated) * trueScale;
}

// --- Display layout and space warp ---------------------------------------
// Everything below is display-only. Physics, prediction and the transfer search all run
// on true world coordinates; this section decides where those coordinates get DRAWN.
//
// The problem: a real system is mostly empty space. At any zoom that shows two planets
// at once, the bodies themselves are sub-pixel; at any zoom that shows a body, its
// neighbours are off-screen. So the display exaggerates body sizes and compresses the
// distances between them — and then bends space itself to match, so trajectories and
// grid stay consistent with the exaggerated picture instead of floating free of it.
//
// Three stages, recomputed whenever the camera or any body moves:
//
//   1. Layout (hierarchical polar) — each body keeps its TRUE ANGLE around its layout
//      parent (moon around planet, planet around star); only the radial distance is
//      remapped: logarithmic beyond a linear window, then pushed out as far as disc
//      clearance demands. Since no step ever chooses an angle and every radius is a
//      max() of continuous functions, the layout is a continuous function of zoom and
//      time — bodies cannot swap sides, and a moon cannot leave its planet.
//
//   2. Anchor — the polar tree is built relative to the root, so it is translated to
//      keep whatever the camera is looking at in place. Frozen during panning.
//
//   3. Warp — a screen-space diffeomorphism carrying true positions to display
//      positions, built as a flow so it provably cannot fold. Grid lines and
//      trajectories are computed at their true physical positions and then pushed
//      through it, so they bend exactly as much as the display lies and no more.
//
// Numerically verified over zoom sweeps x the full viewport: zero fold-overs, zero
// disc-clearance violations, no discontinuity in body placement under pan/zoom/time.
let displayLayoutCache = null;
let layoutAnchor = null; // {sig, wx, wy} view anchor, held fixed while panning (stage 2)
let displayGapScale = 1; // 1 = the full BODY_GAP_PX; fitAllBodies lowers it when the
                         // current alignment cannot fit on screen at any zoom

// Bump falloff profile. A rational tail, NOT a Gaussian: the fold-over hazard of a
// magnification bump is its decay ring, where space must compress to pay for the
// inflation inside. A Gaussian's steep shoulder compresses at -0.446*(scale-1) per px
// (folds at scale 3.2); this profile's worst compression is -0.185*(scale-1), fold-free
// per bump to scale ~6, and it is cheaper than exp() too.
function bumpG(d2, s2) {
    if (d2 > 25 * s2) return 0;
    const a = 1 + d2 / s2;
    return 1 / (a * a);
}

// Builds (and caches) the display layout and the warp field for the current frame.
// Returns {entries, flow, map}: one entry per body carrying its true screen position
// p, its display position q and its drawn radius; the flow that maps p -> q; and a
// body -> entry lookup.
function getDisplayLayout() {
    const n = bodies.length;
    // Cache key: everything the layout depends on. The first two slots are the camera
    // pan, and ONLY those two — the anchor step below reuses the rest of the key to
    // tell "the camera panned" (anchor holds) from "zoom or bodies moved" (re-anchor).
    const key = new Array(7 + 2 * n);
    key[0] = camera.x; key[1] = camera.y;
    key[2] = camera.zoom; key[3] = displayGapScale;
    key[4] = svgWidth; key[5] = svgHeight;
    key[6] = trueScale;
    for (let i = 0; i < n; i++) { key[7 + 2 * i] = bodies[i].x; key[8 + 2 * i] = bodies[i].y; }
    const cached = displayLayoutCache;
    if (cached && cached.key.length === key.length && cached.key.every((v, i) => v === key[i])) {
        return cached;
    }

    const entries = bodies.map(b => {
        const s = worldToScreen(b.x, b.y);
        const drawnR = bodyScreenRadius(b);
        return {
            body: b,
            px: s.x, py: s.y,              // true screen position (bump centre)
            qx: s.x, qy: s.y,              // display position (filled in below)
            drawnR,
            scale: Math.min(WARP_SCALE_CAP, drawnR / Math.max(b.radius * camera.zoom, 1e-9)),
            sigma: drawnR * WARP_SIGMA_MULT
        };
    });

    // Fully to scale: display position IS true position, so there is nothing for the
    // layout to choose and nothing for the warp to correct. Returning an empty flow
    // makes warpScreenPoint the identity, which is both exact and free — the general
    // path below converges to the same answer, it just pays a 7x7 solve x 20 steps to
    // arrive at zero.
    if (trueScale >= 1) {
        displayLayoutCache = {
            key, entries, flow: { steps: [], lam: [], sig2: [] },
            map: new Map(entries.map(e => [e.body, e]))
        };
        return displayLayoutCache;
    }

    // Clamp each bump's reach below the distance to the nearest HEAVIER body, so a
    // moon's bump never covers its planet's centre. Without this, two bodies a few px
    // apart on screen but laid out far apart make the warp's per-step solve
    // ill-conditioned, and the field oscillates violently between them. With it, a
    // planet's wide bump carries its moons rigidly while each moon's narrow bump does
    // only local correction.
    for (const e of entries) {
        let lim = Infinity;
        for (const o of entries) {
            if (o.body.mass <= e.body.mass || o === e) continue;
            const d = Math.hypot(e.px - o.px, e.py - o.py);
            if (d < lim) lim = d;
        }
        e.sigma = Math.max(6, Math.min(e.sigma, 0.7 * lim));
    }

    // STAGE 1: HIERARCHICAL POLAR LAYOUT.
    //
    // Each body's display position is its parent's, plus the TRUE direction to it,
    // times a radius. Only the radius is chosen, never the direction — that is what
    // makes the layout stable: bodies cannot swap sides during a conjunction and a
    // moon cannot be separated from its planet, because "beside its planet, in the
    // real direction" is the only position the scheme can express. Every radius is a
    // max() of functions continuous in zoom and body position, so the whole layout is
    // a continuous function of its inputs, with no equilibria to hop between.
    //
    // (Solvers that pick positions freely — pairwise relaxation, a half-plane QP —
    // were tried first and both teleported bodies across their neighbours during
    // conjunctions. Do not reintroduce one without checking that failure mode.)
    //
    // Clearance is per-DISC, not per-bounding-circle: a subtree is treated as its
    // actual members at their actual offsets, so a planet may sit close to the star
    // when its moons happen to hang on the far side, instead of always reserving a
    // worst-case annulus. That is what lets every gap collapse to the minimum when
    // fully zoomed out, rather than to a fat schematic ring.
    const gap = BODY_GAP_PX * displayGapScale;
    {
        const emap = new Map(entries.map(e => [e.body, e]));
        let root = entries[0];
        for (const e of entries) if (e.body.mass > root.body.mass) root = e;
        for (const e of entries) {
            e.layoutParent = e.body.displayParent ? emap.get(e.body.displayParent)
                : (e === root ? null : root);
            e.kids = [];
        }
        for (const e of entries) if (e.layoutParent) e.layoutParent.kids.push(e);
        // Static sibling order: snapshot the original orbital radius once per body,
        // so "inner vs outer" (who yields to whom) never swaps mid-flight
        for (const e of entries) {
            if (e.layoutParent && e.body._layoutOrbKey === undefined) {
                e.body._layoutOrbKey = Math.hypot(e.body.x - e.layoutParent.body.x,
                                                  e.body.y - e.layoutParent.body.y);
            }
        }

        // Minimum R along a child's ray u so that a subtree member carried at
        // offset b from an obstacle clears it by `need`: |u*R + b| >= need. Inside
        // the corridor (perp < need) that is exact circle geometry (outer root);
        // outside it the requirement FADES DOWN A LINEAR RAMP instead of switching
        // off, so a body sitting nearer the parent than an obstacle is eased
        // outward as the obstacle's corridor closes in on it — never teleported
        // the instant an overlap first appears.
        const RAMP = 3;
        const reqAlong = (ux, uy, bx, by, need) => {
            const along = -(bx * ux + by * uy);
            const perp = Math.sqrt(Math.max(0, bx * bx + by * by - along * along));
            return perp < need
                ? along + Math.sqrt(need * need - perp * perp)
                : along - RAMP * (perp - need);
        };

        const solveRadii = (pe) => {
            const kids = pe.kids;
            for (const k of kids) solveRadii(k);
            kids.sort((a, b) => a.body._layoutOrbKey - b.body._layoutOrbKey);
            for (let i = 0; i < kids.length; i++) {
                const c = kids[i];
                const wx = c.body.x - pe.body.x, wy = c.body.y - pe.body.y;
                const wd = Math.hypot(wx, wy) || 1;
                c.ux = wx / wd; c.uy = wy / wd;
                // LOG RADIAL MAP: the true screen distance passes through unchanged
                // while within LOG_RADIAL_WINDOW px of this pair's clearance minimum
                // (local geometry reads true), then grows only logarithmically — far
                // context compresses toward the parent instead of flying off-screen.
                // Slope is 1 at the handoff, so the mapping is C1-smooth in zoom.
                const t = wd * camera.zoom;
                const m0 = pe.drawnR + c.drawnR + gap;
                let R = t <= m0 ? t
                    : m0 + LOG_RADIAL_WINDOW * Math.log(1 + (t - m0) / LOG_RADIAL_WINDOW);
                for (const m of c.members) {
                    // ...pushed out until every subtree member clears the parent disc...
                    R = Math.max(R, reqAlong(c.ux, c.uy, m.ox, m.oy,
                        pe.drawnR + m.drawnR + gap));
                    // ...and every member of every statically-inner sibling
                    for (let j = 0; j < i; j++) {
                        const s = kids[j];
                        for (const o of s.members) {
                            R = Math.max(R, reqAlong(c.ux, c.uy,
                                m.ox - (s.ux * s.R + o.ox), m.oy - (s.uy * s.R + o.oy),
                                m.drawnR + o.drawnR + gap));
                        }
                    }
                }
                c.R = R;
            }
            // This subtree as its parent will see it: every disc at its offset
            pe.members = [{ ox: 0, oy: 0, drawnR: pe.drawnR }];
            for (const c of kids) {
                for (const m of c.members) {
                    pe.members.push({ ox: c.ux * c.R + m.ox, oy: c.uy * c.R + m.oy, drawnR: m.drawnR });
                }
            }
        };
        const place = (pe) => {
            for (const c of pe.kids) {
                c.qx = pe.qx + c.ux * c.R;
                c.qy = pe.qy + c.uy * c.R;
                place(c);
            }
        };
        solveRadii(root);
        root.qx = root.px; root.qy = root.py;
        place(root);

        // STAGE 2: ANCHOR. The tree above is positioned relative to the root, so on
        // its own, zooming into a distant planet would slide the whole compressed
        // system toward the star. Translating the layout so that bodies near the
        // viewport centre keep their true positions fixes that (a rigid translation,
        // so it cannot disturb any clearance).
        //
        // The anchor is held FIXED (in world units) while the camera only PANS.
        // Panning has to move the picture rigidly: if the anchor were recomputed as
        // the viewport slid, the warp field would visibly re-bend the grid under a
        // drag that should just be moving the view. It recomputes only when zoom or
        // body positions change — when lines are re-bending anyway — which is also
        // when focus hands off to wherever the camera has since moved.
        //
        // sig is the cache key minus the two camera-pan slots, so "the key changed
        // but sig did not" is exactly "the camera panned".
        const sig = key.slice(2);
        const same = layoutAnchor && layoutAnchor.sig.length === sig.length
            && layoutAnchor.sig.every((v, i) => v === sig[i]);
        if (!same) {
            const cx = svgWidth / 2, cy = svgHeight / 2;
            const FOCUS_PX = 150; // weighting softness: bodies within ~this many px
                                  // of centre share the anchor, so it hands off
                                  // smoothly rather than snapping between bodies
            let dx = 0, dy = 0, wsum = 0;
            for (const e of entries) {
                const ddx = e.px - cx, ddy = e.py - cy;
                const w = 1 / (ddx * ddx + ddy * ddy + FOCUS_PX * FOCUS_PX);
                dx += w * (e.px - e.qx); dy += w * (e.py - e.qy); wsum += w;
            }
            // Stored in world units so the pan-frozen anchor stays put on screen
            layoutAnchor = { sig, wx: dx / wsum / camera.zoom, wy: dy / wsum / camera.zoom };
        }
        const ax = layoutAnchor.wx * camera.zoom, ay = layoutAnchor.wy * camera.zoom;
        for (const e of entries) { e.qx += ax; e.qy += ay; }

        // STAGE 2b: RETREAT TOWARD TRUE SCALE. Draw the layout back along the straight
        // line to where each body actually is. Stage 3 then has correspondingly less to
        // do — it is defined as "carry p to q", so shrinking q - p shrinks the warp with
        // it, and the grid unbends at exactly the rate the bodies converge. The trip is
        // fold-free the whole way for the same reason the endpoint is: every intermediate
        // q is a valid target the flow can reach, just a less displaced one.
        if (trueScale > 0) {
            const keep = 1 - trueScale;
            for (const e of entries) {
                e.qx = e.px + (e.qx - e.px) * keep;
                e.qy = e.py + (e.qy - e.py) * keep;
            }
        }
    }

    // STAGE 3: WARP, built as a DIFFEOMORPHIC FLOW.
    //
    // The warp has to carry each true position p to its display position q while
    // staying injective everywhere: the moment it folds, grid lines that started
    // parallel cross each other on screen, which reads as the space tearing.
    //
    // A one-shot displacement field cannot promise that — push hard enough and some
    // decay ring always folds. So instead of applying the bumps as a displacement,
    // treat them as a VELOCITY field and integrate it over WARP_FLOW_STEPS small
    // steps. Each step's gradients are ~1/K of the total, small enough to keep that
    // step injective, and a composition of injective maps is injective. Parallel
    // lines can then crowd arbitrarily close but can never cross, no matter how hard
    // the layout pushes.
    //
    // Per step, bump translations come from a small n x n solve so each body's
    // tracked position closes its remaining distance to target evenly, landing on q
    // after K steps. Magnification compounds instead of adding: each step scales
    // local space by scale^(1/K). Bump centres ride along with their bodies, so a
    // bump can carry a body arbitrarily far without the body escaping it.
    {
        // Widen bumps to match their travel: pushing farther than the bump's own reach
        // needs steep per-step velocities, eating the injectivity margin
        for (const e of entries) {
            const push = Math.hypot(e.qx - e.px, e.qy - e.py);
            e.sigma = Math.max(e.sigma, WARP_SIGMA_PER_PUSH * push);
        }

        const K = WARP_FLOW_STEPS;
        const lam = entries.map(e => Math.pow(e.scale, 1 / K) - 1);
        const sig2 = entries.map(e => e.sigma * e.sigma);
        const steps = [];
        const yx = entries.map(e => e.px);
        const yy = entries.map(e => e.py);

        for (let m = 0; m < K; m++) {
            const remaining = K - m;
            // Solve bump amplitudes so the velocity at each tracked centre equals its
            // per-step target (remaining gap spread over remaining steps), accounting
            // for what the other bumps' magnification terms already contribute there
            const A = [], bxr = new Array(n).fill(0), byr = new Array(n).fill(0);
            for (let i = 0; i < n; i++) {
                const row = new Array(n);
                let rx = (entries[i].qx - yx[i]) / remaining;
                let ry = (entries[i].qy - yy[i]) / remaining;
                for (let j = 0; j < n; j++) {
                    const dx = yx[i] - yx[j], dy = yy[i] - yy[j];
                    const g = bumpG(dx * dx + dy * dy, sig2[j]);
                    // Strong ridge: two bodies sharing a screen pixel make identical
                    // rows, and an exact solve would answer with huge cancelling
                    // velocities that fold within one step. Damped velocities just
                    // land softly; later steps close whatever gap remains.
                    row[j] = g + (i === j ? 0.03 : 0);
                    rx -= g * lam[j] * dx;
                    ry -= g * lam[j] * dy;
                }
                A.push(row); bxr[i] = rx; byr[i] = ry;
            }
            for (let col = 0; col < n; col++) {
                let piv = col;
                for (let r = col + 1; r < n; r++) if (Math.abs(A[r][col]) > Math.abs(A[piv][col])) piv = r;
                [A[col], A[piv]] = [A[piv], A[col]];
                [bxr[col], bxr[piv]] = [bxr[piv], bxr[col]];
                [byr[col], byr[piv]] = [byr[piv], byr[col]];
                const p = A[col][col] || 1e-9;
                for (let r = col + 1; r < n; r++) {
                    const f = A[r][col] / p;
                    if (f === 0) continue;
                    for (let c = col; c < n; c++) A[r][c] -= f * A[col][c];
                    bxr[r] -= f * bxr[col];
                    byr[r] -= f * byr[col];
                }
            }
            const ax = new Array(n), ay = new Array(n);
            for (let i = n - 1; i >= 0; i--) {
                let sx = bxr[i], sy = byr[i];
                for (let c = i + 1; c < n; c++) { sx -= A[i][c] * ax[c]; sy -= A[i][c] * ay[c]; }
                const p = A[i][i] || 1e-9;
                ax[i] = sx / p;
                ay[i] = sy / p;
            }

            // Injectivity cap: a step stays fold-free only while its velocities are
            // small next to the bump widths. Clamp; the shortfall carries forward.
            for (let j = 0; j < n; j++) {
                const mag = Math.hypot(ax[j], ay[j]);
                const lim = 0.3 * entries[j].sigma;
                if (mag > lim) { ax[j] *= lim / mag; ay[j] *= lim / mag; }
            }

            const step = { cx: yx.slice(), cy: yy.slice(), ax, ay };
            steps.push(step);

            // Advance the tracked centres through the ACTUAL step field (the ridge
            // makes velocities inexact; the next step's targets absorb the drift)
            const nx = new Array(n), ny = new Array(n);
            for (let i = 0; i < n; i++) {
                const p = applyFlowStep(step, lam, sig2, yx[i], yy[i]);
                nx[i] = p.x; ny[i] = p.y;
            }
            for (let i = 0; i < n; i++) { yx[i] = nx[i]; yy[i] = ny[i]; }
        }

        displayLayoutCache = {
            key, entries, flow: { steps, lam, sig2 },
            map: new Map(entries.map(e => [e.body, e]))
        };
    }
    return displayLayoutCache;
}

// One integration step of the flow field applied to a point
function applyFlowStep(step, lam, sig2, x0, y0) {
    let dxSum = 0, dySum = 0;
    const m = step.cx.length;
    for (let j = 0; j < m; j++) {
        const dx = x0 - step.cx[j], dy = y0 - step.cy[j];
        const g = bumpG(dx * dx + dy * dy, sig2[j]);
        if (g === 0) continue;
        dxSum += g * (step.ax[j] + lam[j] * dx);
        dySum += g * (step.ay[j] + lam[j] * dy);
    }
    return { x: x0 + dxSum, y: y0 + dySum };
}

// Warp a point from true screen space into display screen space (integrate the flow).
function warpScreenPoint(sx, sy) {
    const flow = getDisplayLayout().flow;
    let x = sx, y = sy;
    for (const step of flow.steps) {
        const p = applyFlowStep(step, flow.lam, flow.sig2, x, y);
        x = p.x; y = p.y;
    }
    return { x, y };
}

// World coordinates -> warped display position. Use this for anything drawn on the map.
function displayTransform(wx, wy) {
    const s = worldToScreen(wx, wy);
    return warpScreenPoint(s.x, s.y);
}

// Trajectories are downsampled before drawing; at true scale the skipped detail is
// sub-pixel, but inside a magnification bump it can be tens of pixels, and the coarse
// polyline tears into long chords. Subdivide any segment the warp stretches well past
// its true screen length, pulling intermediate frames from the full-resolution buffer.
function pushWarpedSegment(out, getWorld, f0, s0, w0, f1, s1, w1, depth) {
    if (depth > 0 && f1 - f0 > 1) {
        const trueLen = Math.hypot(s1.x - s0.x, s1.y - s0.y);
        const warpLen = Math.hypot(w1.x - w0.x, w1.y - w0.y);
        if (warpLen > trueLen * 1.75 + 8) {
            const fm = (f0 + f1) >> 1;
            const pm = getWorld(fm);
            const sm = worldToScreen(pm.x, pm.y);
            const wm = warpScreenPoint(sm.x, sm.y);
            pushWarpedSegment(out, getWorld, f0, s0, w0, fm, sm, wm, depth - 1);
            pushWarpedSegment(out, getWorld, fm, sm, wm, f1, s1, w1, depth - 1);
            return;
        }
    }
    out.push({ screen: w1, frame: f1 });
}

// Turn a sorted list of coarse frame samples into warped screen points, subdivided
// where the warp demands it. getWorld(frame) returns the true world position.
function warpSampledTrajectory(frames, getWorld) {
    const out = [];
    let prevF = null, prevS = null, prevW = null;
    for (const f of frames) {
        const p = getWorld(f);
        const s = worldToScreen(p.x, p.y);
        const w = warpScreenPoint(s.x, s.y);
        if (prevF === null) out.push({ screen: w, frame: f });
        else pushWarpedSegment(out, getWorld, prevF, prevS, prevW, f, s, w, 4);
        prevF = f; prevS = s; prevW = w;
    }
    return out;
}

// Screen position a body is drawn at (its layout position; the warp is exact there).
function bodyScreenPos(body) {
    const e = getDisplayLayout().map.get(body);
    if (!e) return worldToScreen(body.x, body.y);
    return { x: e.qx, y: e.qy };
}

// Radius within which a tap counts as hitting this body.
function bodyTapRadius(body) {
    return Math.max(bodyScreenRadius(body) + BODY_TAP_SLOP, BODY_TAP_MIN_RADIUS);
}

// Screen position for a squadron dot. Every squadron is in flight, out where the warp is
// well behaved, so the warped position is used directly. (This used to pin an orbiting
// dot to its body's drawn rim, because at wide zoom the warp's local gradients could
// fling a two-pixel orbit clear of the disc it belonged to. Parked craft are a number on
// the body now, so there is no such dot to rescue.)
function squadronScreenPos(craft) {
    const pos = craft.getPosition();
    return displayTransform(pos.x, pos.y);
}

// Body class
class CelestialBody {
    constructor(x, y, radius, color, name) {
        this.x = x;
        this.y = y;
        this.vx = 0;
        this.vy = 0;
        this.radius = radius;
        this.color = color;
        this.name = name;
        // Craft parked here, as a plain total. Not a list of squadrons and not a position:
        // parked craft are held to be at no particular orbital phase, so there is nothing
        // to track but how many there are. See the "Transfer search" banner.
        this.craftCount = 0;
        this.isStar = false;   // the one star is marked in initBodies; it is not a transfer destination

        // Mass based on volume and density
        this.mass = DENSITY * (4/3) * Math.PI * Math.pow(radius, 3);

        // SVG elements (created when body is added to scene)
        this.group = null;
        this.glowElement = null;
        this.circleElement = null;
        this.labelElement = null;
        this.trajectoryPath = null;
    }

    get kineticEnergy() {
        const speed = Math.sqrt(this.vx * this.vx + this.vy * this.vy);
        return 0.5 * this.mass * speed * speed;
    }

    get speed() {
        return Math.sqrt(this.vx * this.vx + this.vy * this.vy);
    }

    createElements() {
        // Create group for this body
        this.group = document.createElementNS(SVG_NS, 'g');
        this.group.setAttribute('class', 'body-group');

        // Create glow effect (radial gradient)
        const gradientId = `glow-${this.name}`;
        const gradient = document.createElementNS(SVG_NS, 'radialGradient');
        gradient.setAttribute('id', gradientId);
        gradient.innerHTML = `
            <stop offset="25%" stop-color="${this.color}" stop-opacity="0.125"/>
            <stop offset="100%" stop-color="${this.color}" stop-opacity="0"/>
        `;
        defs.appendChild(gradient);

        // Create glow circle
        this.glowElement = document.createElementNS(SVG_NS, 'circle');
        this.glowElement.setAttribute('class', 'body-glow');
        this.glowElement.setAttribute('fill', `url(#${gradientId})`);
        this.group.appendChild(this.glowElement);

        // Create main circle
        this.circleElement = document.createElementNS(SVG_NS, 'circle');
        this.circleElement.setAttribute('class', 'body-circle');
        this.circleElement.setAttribute('fill', this.color);
        this.circleElement.style.stroke = `color-mix(in srgb, ${this.color} var(--outline-planet-pct), var(--outline-mix))`;
        this.circleElement.dataset.bodyName = this.name;
        this.group.appendChild(this.circleElement);

        // The name, set beneath the craft total and left-aligned with it. In the shared top
        // layer, not this body's group — see bodyAnnotations.
        this.labelElement = document.createElementNS(SVG_NS, 'text');
        this.labelElement.setAttribute('class', 'body-label');
        this.labelElement.setAttribute('text-anchor', 'start');
        this.labelElement.textContent = this.name;
        this.labelElement.dataset.bodyName = this.name;
        bodyAnnotations.appendChild(this.labelElement);

        // How many craft are parked here. This is the whole depiction of a fleet at rest —
        // there is no dot, because a dot would have to sit somewhere on the orbit and so
        // would claim a phase the craft do not have.
        //
        // This goes in the top layer, not this body's group — see craftCountNumbers.
        this.craftCountElement = document.createElementNS(SVG_NS, 'text');
        this.craftCountElement.setAttribute('class', 'body-craft-count');
        this.craftCountElement.setAttribute('text-anchor', 'start');
        // Alphabetic baseline, so the y below is the BOTTOM of the digits. Digits have no
        // descenders, which makes the baseline and the bottom of the number the same line.
        this.craftCountElement.setAttribute('dominant-baseline', 'alphabetic');
        this.craftCountElement.dataset.bodyName = this.name;
        bodyAnnotations.appendChild(this.craftCountElement);

        bodiesLayer.appendChild(this.group);

        // Create trajectory path for solid portion (in trajectories layer)
        this.trajectoryPath = document.createElementNS(SVG_NS, 'path');
        this.trajectoryPath.setAttribute('class', 'trajectory-path body-trajectory');
        // Mix planet color with theme trajectory-mix color for visibility
        const strokeColor = `color-mix(in srgb, ${this.color} 70%, var(--trajectory-mix))`;
        this.trajectoryPath.style.stroke = strokeColor;
        this.trajectoryPath.style.opacity = '0.24';
        trajectoriesLayer.appendChild(this.trajectoryPath);
    }

    updateElements() {
        const screen = bodyScreenPos(this);
        const screenRadius = bodyScreenRadius(this);

        // Update glow
        this.glowElement.setAttribute('cx', screen.x);
        this.glowElement.setAttribute('cy', screen.y);
        this.glowElement.setAttribute('r', screenRadius * 2);

        // Update main circle
        this.circleElement.setAttribute('cx', screen.x);
        this.circleElement.setAttribute('cy', screen.y);
        this.circleElement.setAttribute('r', screenRadius);

        // Update selection/hover state via CSS classes
        this.circleElement.classList.toggle('selected', this === selectedBody);
        this.circleElement.classList.toggle('hovered', this === hoveredBody && this !== selectedBody);
        // Lit up while a transfer drag is hovering it as the destination
        this.circleElement.classList.toggle('drag-target', !!transferDrag && transferDrag.target === this);

        // Craft total and name, both set out to the right of the disc at a fixed distance
        // from its rim, so they keep the same gap from the edge at every zoom rather than
        // being flung outward as the body grows.
        //
        // The two stack about the body's centre line. The number's baseline sits ON it —
        // digits have no descenders, so the baseline is the bottom of the number and it
        // rises out of the middle of the body — and the name hangs just below. With no
        // craft to show, the name has nothing to hang from and centres on the line instead.
        //
        // (Moons used to label above or below their disc depending on which way they lay
        // from their parent, to keep the name off the planet. That rule went with the move
        // to the right-hand side, where the name is clear of both.)
        const annotationX = screen.x + screenRadius + CRAFT_COUNT_GAP_PX;
        const count = bodyDisplayCraftCount(this);

        if (this.craftCountElement) {
            if (count > 0) {
                this.craftCountElement.style.display = '';
                this.craftCountElement.textContent = count;
                this.craftCountElement.setAttribute('x', annotationX);
                this.craftCountElement.setAttribute('y', screen.y);
            } else {
                this.craftCountElement.style.display = 'none';
            }
        }

        this.labelElement.setAttribute('x', annotationX);
        this.labelElement.setAttribute('y', count > 0 ? screen.y + BODY_LABEL_DROP_PX : screen.y);
        this.labelElement.setAttribute('dominant-baseline', count > 0 ? 'hanging' : 'central');
    }

    removeElements() {
        if (this.group) {
            this.group.remove();
        }
        // These live in the shared top layer, so they do not go with the group.
        if (this.craftCountElement) {
            this.craftCountElement.remove();
            this.craftCountElement = null;
        }
        if (this.labelElement) {
            this.labelElement.remove();
            this.labelElement = null;
        }
        if (this.trajectoryPath) {
            this.trajectoryPath.remove();
        }
        // Remove glow gradient from defs
        const gradient = defs.querySelector(`#glow-${this.name}`);
        if (gradient) {
            gradient.remove();
        }
    }
}

// --- The squadron rocket -------------------------------------------------------
//
// Every squadron on the map is drawn as one rocket carrying the whole number, whether it
// is waiting at its origin for a scheduled launch or already out on its trajectory. One
// icon for both, because it is one fleet either way: the launch is the moment it starts
// moving, not the moment it starts existing.
//
// Two things are always true of it. It points where the craft are going — the heading is
// taken from the drawn path in screen space, never from world velocity, because the
// display warp bends the curve and a heading off the raw velocity would not lie along the
// line under it. And it carries the count on its hull, angled with it, so the number and
// the direction are one glyph instead of two things to associate.
//
// Waiting, it bobs along its own axis. That is the whole difference between "scheduled"
// and "under way" as far as the map is concerned, so it is the only thing the drawing has
// to say: motion in place means not yet gone.

// Outline of a rocket of length `len`, nose pointing +x, centred on the origin — so the
// group transform is a plain translate+rotate and the hull needs no offset of its own.
function rocketPathD(len) {
    const h = len / 2;
    const w = ROCKET_WIDTH_PX / 2;
    const fin = 1.9 * w;      // how far the fins stand off the barrel
    const tail = -0.34 * len; // where the barrel ends and the fins carry on past it
    return [
        `M ${h} 0`,
        `Q ${0.30 * len} ${-w} ${0.06 * len} ${-w}`,
        `L ${-0.20 * len} ${-w}`,
        `L ${-0.40 * len} ${-fin}`,
        `L ${-h} ${-fin}`,
        `L ${tail} ${-w}`,
        `L ${tail} ${w}`,
        `L ${-h} ${fin}`,
        `L ${-0.40 * len} ${fin}`,
        `L ${-0.20 * len} ${w}`,
        `Q ${0.30 * len} ${w} ${h} 0`,
        'Z',
    ].join(' ');
}

// One rocket: hull plus the count written along it.
function createRocketElements(layer) {
    const group = document.createElementNS(SVG_NS, 'g');
    group.setAttribute('class', 'craft-rocket');
    const hull = document.createElementNS(SVG_NS, 'path');
    hull.setAttribute('class', 'rocket-hull');
    hull.setAttribute('d', rocketPathD(ROCKET_LENGTH_PX));
    const count = document.createElementNS(SVG_NS, 'text');
    count.setAttribute('class', 'rocket-count');
    count.setAttribute('text-anchor', 'middle');
    count.setAttribute('dominant-baseline', 'central');
    count.setAttribute('x', 0);
    count.setAttribute('y', 0);
    group.appendChild(hull);
    group.appendChild(count);
    layer.appendChild(group);
    return { group, hull, count };
}

// Put a rocket somewhere, pointing somewhere, carrying a number.
//
// `bob` is the waiting state: a slide back and forth along the heading, so the movement is
// unmistakably along the axis it will leave on rather than a wobble in place.
function placeRocket(rocket, x, y, heading, count, bob) {
    let ox = 0, oy = 0;
    if (bob) {
        const phase = (performance.now() / ROCKET_BOB_PERIOD_MS) * 2 * Math.PI;
        const along = Math.sin(phase) * ROCKET_BOB_FRACTION * ROCKET_LENGTH_PX / 2;
        ox = along * Math.cos(heading);
        oy = along * Math.sin(heading);
    }
    const deg = heading * 180 / Math.PI;
    rocket.group.setAttribute('transform', `translate(${x + ox} ${y + oy}) rotate(${deg})`);
    rocket.group.style.display = '';
    const text = count > 0 ? String(count) : '';
    rocket.count.textContent = text;
    // Sized to stay on the hull. Three digits is a lot of fleet for a 17px rocket, so it
    // gives up some size rather than hanging off the ends.
    rocket.count.style.fontSize = `${text.length >= 3 ? 7 : 9}px`;
    // Along the hull either way, but never standing on its head: a rocket flying leftwards
    // gets its number turned over inside the already-rotated frame, which leaves the digits
    // on the same axis and the right way up on screen.
    rocket.count.setAttribute('transform', Math.cos(heading) < 0 ? 'rotate(180)' : '');
}

function hideRocket(rocket) {
    if (rocket) rocket.group.style.display = 'none';
}

// The first two points of a path that are far enough apart to be a direction.
//
// "The next sample along" is not reliably one: at true scale, where every transfer is
// planned, the first frames of a flight are a fraction of a pixel from the launch point,
// and a heading off those two is noise. `at(i)` returns the i'th point in screen space.
function pathStartHeading(len, at) {
    const p0 = at(0);
    const limit = Math.min(len, 64);
    for (let i = 1; i < limit; i++) {
        const p = at(i);
        if (Math.hypot(p.x - p0.x, p.y - p0.y) > 0.5) return { p0, p1: p };
    }
    return { p0, p1: at(Math.max(1, limit - 1)) };
}

// Where a rocket sits while it waits at its origin, and which way it points.
//
// Both come off the path it is about to fly: the rim point it stands on is the one facing
// where that path begins, and the heading is the direction the path sets off in. `p0` and
// `p1` are the first two screen points of the trajectory.
function parkedRocketPose(body, p0, p1) {
    const c = bodyScreenPos(body);
    let heading = Math.atan2(p1.y - p0.y, p1.x - p0.x);
    if (!isFinite(heading)) heading = 0;
    // Which way the launch point lies from the centre. A launch point sitting exactly on
    // the drawn centre — a body compressed to nothing at this zoom — has no direction to
    // give, so the heading stands in for it and the rocket leaves along its own nose.
    const dx = p0.x - c.x, dy = p0.y - c.y;
    const out = Math.hypot(dx, dy) < 1e-6 ? heading : Math.atan2(dy, dx);
    const r = bodyScreenRadius(body);
    return { x: c.x + r * Math.cos(out), y: c.y + r * Math.sin(out), heading };
}

// Squadron - a group of craft in flight, or scheduled to depart.
//
// A squadron exists only between two bodies. Craft at rest are a number on their body
// (see "Craft at a body"), so there is no orbiting state here: a squadron is created at
// launch and destroyed on arrival, when its craft join the destination's total.
class Squadron {
    constructor(sourceBody, count = 1, orbitalAltitude = CRAFT_ORBITAL_ALTITUDE) {
        this.count = count; // How many craft in this squadron
        this.orbitalAltitude = orbitalAltitude;
        this.releaseAngle = 0; // where on the source body's circle this one cast off

        // Position and velocity (always kept in sync by syncToViewFrame)
        const orbitRadius = sourceBody.radius + orbitalAltitude;
        this.x = sourceBody.x + orbitRadius;
        this.y = sourceBody.y;
        this.vx = 0;
        this.vy = 0;

        // Acceleration phase
        this.isAccelerating = false;
        this.accelerationMagnitude = CRAFT_ACCELERATION;
        this.accelerationDirection = { x: 0, y: 0 }; // normalized
        this.escapeVelocity = 0; // set at launch
        this.launchedFromBody = null; // body we launched from (for escape velocity check)

        // Correction boost tracking
        this.flightFrame = 0; // frames since launch
        this.isCorrecting = false; // currently applying correction boost
        this.correctionParams = null; // {angle, duration, startFrame} or null if no correction

        // Transfer tracking
        this.destinationBody = null; // target body for transfer (null if no transfer)
        this.insertionFrame = 0; // frame at which orbit insertion occurs (end of trajectory)
        this.sourceBody = null; // body this squadron launches from (for pre-launch tracking)
        this.launchFrame = 0; // frames until launch (0 = already under way)

        // Visual element
        this.element = null;

        // Trajectory elements (like CelestialBody)
        this.trajectoryPath = null;

        // Trajectory prediction buffer (used after launch, like body predictionBuffer)
        // Array of {x, y, vx, vy, isAccelerating} states
        this.trajectoryBuffer = [];

        // Display count (adjusted for scheduled transfers during time scrub)
        this._displayCount = count;
        // Which of the three things this squadron is at the moment being viewed: still
        // waiting at its origin, out on its trajectory, or arrived and no longer drawn.
        // Set by syncToViewFrame; the rocket and the hit test both read it.
        this._displayPhase = 'pending';
        // Where the rocket was last drawn, for hit-testing a tap against it.
        this._rocketScreen = null;
        // Where each craft aboard was taken from, so a launch can be unmade exactly if it
        // is reopened before it goes. Filled in at schedule time.
        this.drawnFrom = null;
    }

    // Get current position (always from x/y, which are set by syncToViewFrame)
    getPosition() {
        return { x: this.x, y: this.y };
    }

    // Get current speed (relative to launch body for escape velocity check)
    getSpeed() {
        return Math.sqrt(this.vx * this.vx + this.vy * this.vy);
    }

    // Create SVG element for rendering
    createElements() {
        // The whole squadron, count and heading together — see "The squadron rocket".
        this.rocket = createRocketElements(bodiesLayer);
        this.element = this.rocket.group;

        // Create trajectory hit area (invisible, wider path for easier clicking)
        this.trajectoryHitArea = document.createElementNS(SVG_NS, 'path');
        this.trajectoryHitArea.setAttribute('class', 'craft-trajectory-hit-area');
        this.trajectoryHitArea.setAttribute('stroke', 'transparent');
        this.trajectoryHitArea.setAttribute('stroke-width', '15'); // 3x wider than visible
        this.trajectoryHitArea.setAttribute('fill', 'none');
        // Store reference to craft for click handling
        this.trajectoryHitArea._craft = this;
        trajectoriesLayer.appendChild(this.trajectoryHitArea);

        // Create trajectory path (visible portion)
        this.trajectoryPath = document.createElementNS(SVG_NS, 'path');
        this.trajectoryPath.setAttribute('class', 'trajectory-path craft-trajectory');
        trajectoriesLayer.appendChild(this.trajectoryPath);

        // Create correction arrow (hidden by default)
        this.correctionArrow = document.createElementNS(SVG_NS, 'line');
        this.correctionArrow.setAttribute('stroke', 'red');
        this.correctionArrow.setAttribute('stroke-width', '3');
        this.correctionArrow.setAttribute('marker-end', 'url(#correction-arrowhead)');
        this.correctionArrow.style.display = 'none';
        this.correctionArrow.style.pointerEvents = 'none';
        bodiesLayer.appendChild(this.correctionArrow);

        // Create correction trajectory overlay (red dotted line)
        this.correctionOverlay = document.createElementNS(SVG_NS, 'path');
        this.correctionOverlay.setAttribute('stroke', 'red');
        this.correctionOverlay.setAttribute('stroke-width', '4');
        this.correctionOverlay.setAttribute('stroke-dasharray', '8,4');
        this.correctionOverlay.setAttribute('fill', 'none');
        this.correctionOverlay.style.display = 'none';
        // Both burn markers are decoration drawn on top of the path they describe. Left
        // hit-testable they answer instead of it, and a tap meant for the trajectory —
        // which is how a launch still waiting is reopened — lands on nothing.
        this.correctionOverlay.style.pointerEvents = 'none';
        trajectoriesLayer.appendChild(this.correctionOverlay);
    }

    // Where the rocket stands while it waits for its launch moment, and which way it aims.
    // Null when there is nothing yet to aim along — the source is gone, or the flight has
    // not been worked out.
    waitingPose() {
        const buf = this.trajectoryBuffer;
        if (!this.sourceBody || buf.length < 2) return null;
        const { p0, p1 } = pathStartHeading(buf.length, (i) => displayTransform(buf[i].x, buf[i].y));
        return parkedRocketPose(this.sourceBody, p0, p1);
    }

    // Where it is under way, pointing down the stretch of path it is on. The heading comes
    // off two screen points either side of it rather than off vx/vy: the display warp bends
    // the drawn curve away from the true velocity, and the nose has to follow the line the
    // player can actually see.
    flyingPose() {
        const here = squadronScreenPos(this);
        const buf = this.trajectoryBuffer;
        let heading = null;
        if (buf.length > 1) {
            const idx = Math.min(
                Math.max(Math.round(timeViewOffset) - Math.max(0, this.launchFrame), 0),
                buf.length - 1);
            const a = buf[Math.max(idx - ROCKET_HEADING_FRAMES, 0)];
            const b = buf[Math.min(idx + ROCKET_HEADING_FRAMES, buf.length - 1)];
            const pa = displayTransform(a.x, a.y);
            const pb = displayTransform(b.x, b.y);
            if (Math.hypot(pb.x - pa.x, pb.y - pa.y) > 1e-6) {
                heading = Math.atan2(pb.y - pa.y, pb.x - pa.x);
            }
        }
        if (heading === null) heading = Math.atan2(this.vy, this.vx);
        return { x: here.x, y: here.y, heading };
    }

    // Update SVG element position and state
    updateElements() {
        if (!this.element) return;

        // Use display count when set (adjusted by syncToViewFrame for scrub position)
        const displayCount = this._displayCount !== undefined ? this._displayCount : this.count;
        // Waiting at its origin for a launch that has not come round yet. Still a fleet
        // with a number and a direction, so it is drawn — it is only the movement along
        // the trajectory that has not started. See "The squadron rocket".
        const waiting = this._displayPhase === 'pending' && this.count > 0;

        // Nothing of this squadron is drawn at the viewed moment: it has arrived and become
        // part of a body's total.
        //
        // EVERY piece has to go, not just the rocket. The burn arrow is set further down,
        // past this return, so leaving it out here stranded it: a squadron still burning on
        // the last frame of its flight kept a red arrow pinned to the map for the rest of
        // time, pointing out of a craft that was no longer anywhere.
        if (displayCount <= 0 && !waiting) {
            this.element.style.display = 'none';
            if (this.correctionArrow) this.correctionArrow.style.display = 'none';
            this._rocketScreen = null;
            return;
        }

        // Where it is and which way it faces. Waiting, both come off the launch end of the
        // path; under way, off the stretch of path it is on.
        const pose = waiting ? this.waitingPose() : this.flyingPose();
        if (!pose) {
            this.element.style.display = 'none';
            if (this.correctionArrow) this.correctionArrow.style.display = 'none';
            this._rocketScreen = null;
            return;
        }
        placeRocket(this.rocket, pose.x, pose.y, pose.heading,
                    waiting ? this.count : displayCount, waiting);
        this._rocketScreen = { x: pose.x, y: pose.y };

        const screen = waiting ? pose : squadronScreenPos(this);

        // Toggle free class for blinking animation (only during acceleration)
        this.element.classList.toggle('free', this.isAccelerating);

        // Every squadron is in transit, by definition.
        const inTransit = true;
        this.element.classList.add('in-transit');
        this.element.style.cursor = 'pointer';

        // Toggle selected class
        const isSelected = (selectedSquadron === this);
        this.element.classList.toggle('selected', isSelected);

        // Also update trajectory path classes
        if (this.trajectoryPath) {
            this.trajectoryPath.classList.toggle('in-transit', inTransit);
            this.trajectoryPath.classList.toggle('selected', isSelected);
        }

        // Update hit area classes
        if (this.trajectoryHitArea) {
            this.trajectoryHitArea.classList.toggle('in-transit', inTransit);
        }

        // Show correction arrow during correction phase
        if (this.correctionArrow) {
            if (this.isCorrecting && this.correctionParams) {
                const arrowLength = 30; // pixels
                const angle = this.correctionParams.angle;
                const endX = screen.x + arrowLength * Math.cos(angle);
                const endY = screen.y + arrowLength * Math.sin(angle);

                this.correctionArrow.setAttribute('x1', screen.x);
                this.correctionArrow.setAttribute('y1', screen.y);
                this.correctionArrow.setAttribute('x2', endX);
                this.correctionArrow.setAttribute('y2', endY);
                this.correctionArrow.style.display = 'block';
            } else {
                this.correctionArrow.style.display = 'none';
            }
        }
    }

    // Remove SVG elements
    removeElements() {
        if (this.element) {
            this.element.remove();
            this.element = null;
        }
        this.rocket = null;
        if (this.trajectoryHitArea) {
            this.trajectoryHitArea.remove();
            this.trajectoryHitArea = null;
        }
        if (this.trajectoryPath) {
            this.trajectoryPath.remove();
            this.trajectoryPath = null;
        }
        if (this.correctionArrow) {
            this.correctionArrow.remove();
            this.correctionArrow = null;
        }
        if (this.correctionOverlay) {
            this.correctionOverlay.remove();
            this.correctionOverlay = null;
        }
    }

}

// --- Craft at a body -----------------------------------------------------------
//
// Craft parked at a body are a number on the body and nothing else. A squadron is a
// thing in flight; the moment it arrives it stops being one and becomes part of the
// destination's total.
//
// This is not just bookkeeping tidiness. The transfer search assumes craft may cast off
// from any point on their orbit, so a parked fleet has no phase — and anything that
// stored one, a position, an angle, a drawn dot, would be asserting a fact the search
// contradicts. Keeping only the count makes the two agree by construction.

// What to draw beside a body at the moment being viewed — which is exactly what can be
// sent from it, so it is the same question and the same answer.
//
// It did not use to be. A squadron waiting on a scheduled launch was added back to its
// origin's number, because it was physically still sitting there and nothing else on the
// map depicted it — but it could not be sent, so the number invited a drag it then
// refused. The rocket depicts it now (see "The squadron rocket"), and adding it back here
// as well would draw the same craft twice, side by side. So the body's number went back to
// meaning the one thing it can mean: the craft still free to go somewhere.
function bodyDisplayCraftCount(body, viewFrame) {
    let count = getSendableCraftAtBody(body, viewFrame);

    // A transfer being chosen is not committed, but it is already drawn: the preview
    // rocket standing on this body carries the number on the slider. Same rule again —
    // shown once — so what is left beside the body is what stays behind, which is exactly
    // what the slider says in words while the player moves it.
    if (transferIsPlanning() && body === transferSourceBody && highlightedFanEntry()) {
        count -= parseInt(transferQtySlider.value, 10) || 0;
    }

    return Math.max(0, count);
}

// Kept as a name because the info panel and tests speak in these terms.
function getEffectiveCraftAtBody(body, viewFrame) {
    return bodyDisplayCraftCount(body, viewFrame);
}

// How many craft at `body` can be sent onward, leaving at `viewFrame`.
//
// Every transfer departs at the moment on the clock, so "how many are here" is a question
// about that moment and not about the present. A squadron inbound to this body counts once
// the viewed moment is past its arrival: it is standing on the body by then, and can be
// chained straight onto a new trip. One still in the air does not, and neither does one
// waiting on its own launch here — those craft are drawn on their rocket, not on the body.
function getSendableCraftAtBody(body, viewFrame) {
    const frame = viewFrame !== undefined ? viewFrame : Math.round(timeViewOffset);
    let count = body.craftCount;

    for (const craft of squadrons) {
        if (craft.count <= 0) continue;
        if (craft.destinationBody !== body) continue;
        if (frame - craft.launchFrame >= craft.trajectoryBuffer.length) count += craft.count;
    }

    return Math.max(0, count);
}

function addCraftToOrbit(body, count) {
    body.craftCount += count;
    return body.craftCount;
}

// Initialize bodies
// Create a moon orbiting a parent body
// angle: orbital position in radians (0 = right, PI/2 = below, PI = left, 3PI/2 = above)
function createMoon(parent, orbitalRadius, angle, radius, color, name, mass) {
    // Calculate position relative to parent
    const offsetX = orbitalRadius * Math.cos(angle);
    const offsetY = orbitalRadius * Math.sin(angle);
    const x = parent.x + offsetX;
    const y = parent.y + offsetY;

    const moon = new CelestialBody(x, y, radius, color, name);
    moon.mass = mass;
    // Display-only: a moon is drawn in its parent's local frame, so it stays outside the
    // parent's exaggerated disc instead of being swallowed by it. See bodyScreenPos().
    moon.displayParent = parent;

    // Calculate orbital velocity (perpendicular to radius vector)
    const orbitalSpeed = Math.sqrt(G * parent.mass / orbitalRadius);
    // Velocity is perpendicular to position offset (90 degrees ahead)
    moon.vx = parent.vx - orbitalSpeed * Math.sin(angle);
    moon.vy = parent.vy + orbitalSpeed * Math.cos(angle);

    moon.createElements();
    return moon;
}

function initBodies() {
    // Remove old body elements
    for (const body of bodies) {
        body.removeElements();
    }
    bodies = [];

    // Remove old squadron elements
    for (const squad of squadrons) {
        squad.removeElements();
    }
    squadrons = [];

    // Central large body (like a star/planet)
    const central = new CelestialBody(0, 0, 80, '#ffaa44', 'Sol');
    central.mass = 18000;
    central.isStar = true;   // marked, not inferred from index: it is not a transfer destination
    central.createElements();
    bodies.push(central);

    // Ember - inner planet orbiting Sol
    const ember = new CelestialBody(332.5, 0, 15, '#dd6644', 'Ember');
    ember.mass = 20;
    const emberDist = 332.5;
    ember.vy = Math.sqrt(G * central.mass / emberDist);
    ember.createElements();
    bodies.push(ember);

    // Terra - orbiting Sol
    const terra = new CelestialBody(778.4, 0, 25, '#4488ff', 'Terra');
    terra.mass = 75;
    const terraDist = 778.4;
    terra.vy = Math.sqrt(G * central.mass / terraDist);
    terra.createElements();
    bodies.push(terra);

    // Luna - moon of Terra
    const luna = createMoon(terra, 25, -Math.PI / 2, 10, '#aaaaaa', 'Luna', 1.67);
    bodies.push(luna);

    // Gaia - orbiting Sol
    const gaia = new CelestialBody(-1353.8, 0, 35, '#88ff88', 'Gaia');
    gaia.mass = 384;
    const gaiaDist = 1353.8;
    gaia.vy = -Math.sqrt(G * central.mass / gaiaDist);
    gaia.createElements();
    bodies.push(gaia);

    // Aria - inner moon of Gaia
    const aria = createMoon(gaia, 70, Math.PI / 4, 7, '#bbddbb', 'Aria', 0.415);
    bodies.push(aria);

    // Nyx - outer moon of Gaia
    const nyx = createMoon(gaia, 84, -Math.PI / 3, 5, '#99bb99', 'Nyx', 0.21);
    bodies.push(nyx);

    // Create initial orbiting squadron at Ember
    addCraftToOrbit(ember, 5);
}

// Calculate gravitational acceleration
function calculateGravity(body, otherBodies) {
    let ax = 0;
    let ay = 0;

    for (const other of otherBodies) {
        if (other === body) continue;

        const dx = other.x - body.x;
        const dy = other.y - body.y;
        const distSq = dx * dx + dy * dy;
        const dist = Math.sqrt(distSq);

        // Prevent singularities
        const safeDist = Math.max(dist, MIN_DISTANCE);

        // F = G * m1 * m2 / r^2, a = F/m1 = G * m2 / r^2
        const acceleration = G * other.mass / (safeDist * safeDist);

        // Direction
        ax += acceleration * (dx / dist);
        ay += acceleration * (dy / dist);
    }

    return { ax, ay };
}

// Calculate system energies
function calculateEnergies() {
    let kinetic = 0;
    let potential = 0;

    for (const body of bodies) {
        kinetic += body.kineticEnergy;
    }

    // Potential energy between all pairs
    for (let i = 0; i < bodies.length; i++) {
        for (let j = i + 1; j < bodies.length; j++) {
            const b1 = bodies[i];
            const b2 = bodies[j];
            const dx = b2.x - b1.x;
            const dy = b2.y - b1.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            // U = -G * m1 * m2 / r
            potential -= G * b1.mass * b2.mass / Math.max(dist, MIN_DISTANCE);
        }
    }

    return { kinetic, potential, total: kinetic + potential };
}

// Advance timeline - manages the prediction buffer and advances the "present" marker.
// Does NOT set body/craft positions; that's done by syncToViewFrame().
function advanceTimeline(dt) {
    const masses = getBodyMasses();

    // Building the buffer from cold is not a catch-up, and is not budgeted like one.
    // MAX_CATCHUP_FRAMES exists to bound the work of a running simulation topping its buffer
    // back up a frame at a time; spending it on the first fill turns a ten-millisecond job into
    // a three-second one. Those three seconds are not merely a wait — the view is fitted to the
    // bounding box of the orbits *so far*, and a box growing one arc at a time is a box whose
    // centre swings about, so the map wanders back and forth while the orbits draw themselves
    // in behind it. Nothing on screen can be right until the whole buffer exists, so build all
    // of it before drawing any of it.
    const catchupBudget = predictionBuffer.length === 0 ? PREDICTION_FRAMES : MAX_CATCHUP_FRAMES;

    // Accumulate time and pop frames from front as present advances
    predictionTimeAccum += dt * SIM_SPEED;
    while (predictionTimeAccum >= PREDICTION_DT && predictionBuffer.length > 0) {
        // Pop the front frame (present advances by one tick)
        predictionBuffer.shift();

        // Advance squadron state for this tick
        const squadronsToRemove = [];
        for (const craft of squadrons) {
            if (craft.launchFrame > 0 || craft.trajectoryBuffer.length === 0) continue;

            // Pop craft trajectory buffer (synced with body buffer)
            craft.trajectoryBuffer.shift();
            craft.flightFrame++;

            // End of the trajectory is the arrival. A squadron exists only in flight, so
            // arriving means ceasing to be one: the craft join the destination's total
            // and the squadron is destroyed. There is no orbiting state to fall back to.
            if (craft.trajectoryBuffer.length === 0 && craft.destinationBody) {
                const destBody = craft.destinationBody;

                if (craft.count > 0) {
                    destBody.craftCount += craft.count;
                }

                if (selectedSquadron === craft) {
                    selectedSquadron = null;
                    selectedBody = destBody;
                    isTrackingSelectedSquadron = false;
                }

                craft.removeElements();
                squadronsToRemove.push(craft);
            }
        }

        // Remove destroyed squadrons
        for (const sq of squadronsToRemove) {
            const idx = squadrons.indexOf(sq);
            if (idx !== -1) squadrons.splice(idx, 1);
        }

        // The fan on screen describes a physical moment, not a buffer index; keep it
        // pointing at the same moment now that the buffer has moved under it.
        updateFanOnShift();

        // What a transfer owes the clock is a physical moment too, so it shifts with
        // everything else. Before the offset itself, so that a re-arm below can set the
        // two to the same number and have them stay equal — that equality is how the
        // handback tells its own doing from the player's.
        if (clockBeforeTransfer !== null && clockBeforeTransfer > 0) clockBeforeTransfer--;
        if (clockSetByTransfer > 0) clockSetByTransfer--;

        // Decrement time view offset so we keep looking at the same physical moment
        if (timeViewOffset > 0) {
            timeViewOffset = Math.max(0, timeViewOffset - 1);

            // The launch moment has caught up with the present while the player is still
            // picking a route and a number of craft. Push it back out to the lead the
            // transfer opened on instead of letting it go by — see TRANSFER_LEAD_MINUTES.
            // Only here, where the clock arrived on its own: a player who scrubs down to
            // the present themselves has said what they want, and is left there.
            if (timeViewOffset === 0 && transferIsPlanning()) {
                setTimeViewOffset(TRANSFER_LEAD_FRAMES);
                clockSetByTransfer = TRANSFER_LEAD_FRAMES;
            }
        }

        // Process transit squadrons: decrement launchFrame for pending launches
        for (let i = scheduledTransfers.length - 1; i >= 0; i--) {
            const entry = scheduledTransfers[i];
            const transit = entry.squadron;
            transit.launchFrame--;

            if (transit.launchFrame <= 0) {
                // Launch time reached — squadron transitions to active transit
                transit.launchFrame = 0;
                transit.sourceBody = null;

                // Set initial position/velocity from first trajectory frame
                if (transit.trajectoryBuffer.length > 0) {
                    const firstFrame = transit.trajectoryBuffer[0];
                    transit.x = firstFrame.x;
                    transit.y = firstFrame.y;
                    transit.vx = firstFrame.vx;
                    transit.vy = firstFrame.vy;
                    transit.isAccelerating = firstFrame.isAccelerating !== undefined ? firstFrame.isAccelerating : true;

                    // Set escape velocity for prograde acceleration
                    const body = entry.sourceBody;
                    const orbitRadius = body.radius + CRAFT_ORBITAL_ALTITUDE;
                    transit.escapeVelocity = Math.sqrt(2 * G * body.mass / orbitRadius);
                    transit.launchedFromBody = body;
                    const speed = transit.getSpeed();
                    if (speed > 0) {
                        transit.accelerationDirection = { x: transit.vx / speed, y: transit.vy / speed };
                    }
                }

                // Auto-select craft if its origin body was selected
                if (selectedBody === entry.sourceBody) {
                    selectedBody = null;
                    selectedSquadron = transit;
                    isTrackingSelectedSquadron = true;
                }

                console.log(`[Transit] Launched ${transit.count} from ${entry.sourceBody.name} to ${entry.destBody.name}, trajLen=${transit.trajectoryBuffer.length}`);

                // Remove from scheduled list
                scheduledTransfers.splice(i, 1);
            }
        }

        predictionTimeAccum = Math.max(0, predictionTimeAccum - PREDICTION_DT);
        // Adjust sample offset to maintain consistent trajectory sampling
        // Decrement so we sample the same physical frames as buffer shifts
        sampleOffset = (sampleOffset - 1 + SAMPLE_INTERVAL) % SAMPLE_INTERVAL;
    }

    // Add new predictions to maintain buffer (see catchupBudget above)
    let framesAdded = 0;
    while (predictionBuffer.length < PREDICTION_FRAMES && framesAdded < catchupBudget) {
        // Always extend from the last state in buffer
        const lastState = predictionBuffer.length > 0
            ? predictionBuffer[predictionBuffer.length - 1]
            : getBodyStates();

        const nextState = simulateStep(lastState, masses, PREDICTION_DT);
        predictionBuffer.push(nextState);
        framesAdded++;
    }
}

// Sync all body and craft state to the currently viewed frame.
// This is the SINGLE place where body/craft positions get set.
// When timeViewOffset=0 (present), state comes from frame 0 of the buffer.
// When timeViewOffset>0 (future), state comes from that future frame.
function syncToViewFrame() {
    if (predictionBuffer.length === 0) return;

    const viewFrame = Math.round(timeViewOffset);
    const frameIndex = Math.min(Math.max(viewFrame, 0), predictionBuffer.length - 1);

    // Set body positions from the viewed frame
    const state = predictionBuffer[frameIndex];
    for (let i = 0; i < bodies.length; i++) {
        bodies[i].x = state[i].x;
        bodies[i].y = state[i].y;
        bodies[i].vx = state[i].vx;
        bodies[i].vy = state[i].vy;
    }

    // Set craft positions for the viewed frame. Every squadron is in flight — craft at
    // rest are a number on their body, and have no position to place.
    for (const craft of squadrons) {
        if (craft.trajectoryBuffer.length > 0) {
            // How far into its own flight this squadron is at the viewed moment. Not
            // clamped to the end of the buffer: running off the end is how the arrival
            // gets noticed below, and clamping instead parked the dot on the destination
            // while bodyDisplayCraftCount was already counting it there.
            const trajIdx = frameIndex - craft.launchFrame;

            if (trajIdx < 0) {
                // Before launch. Drawn as a rocket standing on its origin — these craft
                // are committed to this trip and no longer part of the body's total, so
                // the rocket is the only place the player sees them.
                craft.isAccelerating = false;
                craft.isCorrecting = false;
                craft._displayCount = 0;
                craft._displayPhase = 'pending';
            } else if (trajIdx >= 0 && trajIdx < craft.trajectoryBuffer.length) {
                // In transit: position along trajectory
                const futurePos = craft.trajectoryBuffer[trajIdx];
                craft.x = futurePos.x;
                craft.y = futurePos.y;
                craft.vx = futurePos.vx;
                craft.vy = futurePos.vy;
                craft.isAccelerating = futurePos.isAccelerating;
                craft._displayCount = craft.count;
                craft._displayPhase = 'flight';

                if (craft.correctionParams) {
                    const params = craft.correctionParams;
                    const viewFlightFrame = craft.flightFrame + trajIdx;
                    craft.isCorrecting = viewFlightFrame >= params.startFrame &&
                                         viewFlightFrame < params.startFrame + params.duration;
                } else {
                    craft.isCorrecting = false;
                }
            } else if (craft.destinationBody) {
                // Past arrival. Nothing is drawn: these craft have joined the destination's
                // total by this moment, and bodyDisplayCraftCount adds them there. Drawing
                // a rocket as well would show the same craft twice.
                craft.isAccelerating = false;
                craft.isCorrecting = false;
                craft._displayCount = 0;
                craft._displayPhase = 'arrived';
            } else {
                // Already launched, past end of trajectory buffer
                const craftFrame = craft.trajectoryBuffer.length - 1;
                const futurePos = craft.trajectoryBuffer[craftFrame];
                craft.x = futurePos.x;
                craft.y = futurePos.y;
                craft.vx = futurePos.vx;
                craft.vy = futurePos.vy;
                craft.isAccelerating = futurePos.isAccelerating;
                craft._displayCount = craft.count;
                craft._displayPhase = 'flight';
                if (craft.correctionParams) {
                    const params = craft.correctionParams;
                    const viewFlightFrame = craft.flightFrame + craftFrame;
                    craft.isCorrecting = viewFlightFrame >= params.startFrame &&
                                         viewFlightFrame < params.startFrame + params.duration;
                } else {
                    craft.isCorrecting = false;
                }
            }
        }
    }
}

// Extend craft trajectory buffers to maintain prediction length.
function extendCraftBuffers() {
    for (const craft of squadrons) {
        if (!craft.destinationBody) {
            // Extend buffer to match predictionBuffer length (regular launch only)
            const craftMaxFrames = Math.min(predictionBuffer.length, MAX_CRAFT_PREDICTION_FRAMES);
            while (craft.trajectoryBuffer.length < craftMaxFrames && predictionBuffer.length > 0) {
                const lastState = craft.trajectoryBuffer.length > 0
                    ? craft.trajectoryBuffer[craft.trajectoryBuffer.length - 1]
                    : { x: craft.x, y: craft.y, vx: craft.vx, vy: craft.vy, isAccelerating: craft.isAccelerating };

                const frameIndex = craft.trajectoryBuffer.length;
                const flightFrameAtStep = craft.flightFrame + frameIndex;
                if (frameIndex < predictionBuffer.length) {
                    const bodyStates = predictionBuffer[frameIndex];
                    const nextState = simulateCraftStep(craft, lastState, bodyStates, flightFrameAtStep);
                    craft.trajectoryBuffer.push(nextState);
                }
            }
        }
        // For transfer flights (craft.destinationBody set), trajectory buffer
        // is pre-computed and truncated at insertion - don't extend it
    }
}

// Simulate one step forward for craft trajectory buffer extension
// flightFrameAtStep: the flight frame number for this step (for correction boost)
function simulateCraftStep(craft, lastState, bodyStates, flightFrameAtStep = -1) {
    const launchBodyIndex = bodies.indexOf(craft.launchedFromBody);

    let ax = 0;
    let ay = 0;

    // Calculate gravity from all bodies
    for (let i = 0; i < bodyStates.length; i++) {
        const bodyState = bodyStates[i];
        const dx = bodyState.x - lastState.x;
        const dy = bodyState.y - lastState.y;
        const distSq = dx * dx + dy * dy;
        const dist = Math.sqrt(distSq);
        const safeDist = Math.max(dist, MIN_DISTANCE);

        const mass = bodies[i].mass;
        const acceleration = G * mass / (safeDist * safeDist);
        ax += acceleration * (dx / dist);
        ay += acceleration * (dy / dist);
    }

    // Apply craft acceleration if in escape acceleration phase
    let isAccelerating = lastState.isAccelerating;
    if (isAccelerating && launchBodyIndex >= 0) {
        const launchBodyState = bodyStates[launchBodyIndex];
        const dx = lastState.x - launchBodyState.x;
        const dy = lastState.y - launchBodyState.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        const accelDirX = -craft.orbitalDirection * dy / dist;
        const accelDirY = craft.orbitalDirection * dx / dist;

        ax += CRAFT_ACCELERATION * accelDirX;
        ay += CRAFT_ACCELERATION * accelDirY;

        const relVx = lastState.vx - launchBodyState.vx;
        const relVy = lastState.vy - launchBodyState.vy;
        const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
        if (relSpeed >= 1.1 * craft.escapeVelocity) {
            isAccelerating = false;
        }
    }

    // Apply correction boost if in correction phase
    if (craft.correctionParams && flightFrameAtStep >= 0) {
        const params = craft.correctionParams;
        if (flightFrameAtStep >= params.startFrame &&
            flightFrameAtStep < params.startFrame + params.duration) {
            ax += CRAFT_ACCELERATION * Math.cos(params.angle);
            ay += CRAFT_ACCELERATION * Math.sin(params.angle);
        }
    }

    const vx = lastState.vx + ax * PREDICTION_DT;
    const vy = lastState.vy + ay * PREDICTION_DT;

    return {
        x: lastState.x + vx * PREDICTION_DT,
        y: lastState.y + vy * PREDICTION_DT,
        vx,
        vy,
        isAccelerating
    };
}

//
// Craft parked at a body have no orbital phase (see "Craft at a body"). They cast off
// from wherever on the circle suits them, so the question the search answers is not
// "when should we leave?" but "which way should we let go, right now?".
//
// That inverts what the search sweeps. It used to walk forward through launch frames,
// deriving the release angle from each one, which meant the player was really choosing a
// time to wait until. Now the launch moment is fixed — it is whatever the time wheel is
// showing — and the sweep runs around the release circle instead. Every viable angle is
// drawn on the map at once, and the player drags a finger across the fan to pick one.
//
// The two halves need each other. Sweeping angles at a single moment only makes sense if
// phase is free, and drawing a parked fleet without a dot only makes sense if nothing
// depends on where it sits. Change one back and the other stops being honest.
//
// A scan is cheap enough — tens of milliseconds spread over the worker pool — that
// moving the time wheel simply runs another one. See ANGLE_OPTIMIZE_BUDGET in
// transfer-worker.js for what fixes that cost.

// Release angles sampled around the circle. Only the most promising ANGLE_OPTIMIZE_BUDGET
// of them get the expensive burn optimization, so raising this widens the net the cheap
// pass casts without changing what the scan costs.
const FAN_ANGLE_COUNT = 360;

// How long the viewed moment must hold still before a scrub triggers a fresh scan.
// Spinning the wheel crosses hundreds of frames; without this every one would queue work
// that the next frame invalidates.
const FAN_RESCAN_QUIET_MS = 120;

// How near a finger has to come to a trajectory, in screen px, to pick it up.
const FAN_PICK_RADIUS_PX = 44;

// A scan needs enough buffer ahead of the launch moment to see a transfer through.
// Must match the worker's own cap, or a committed flight would be cut at a different
// point from the one that was searched.
const MAX_TRANSFER_FRAMES = Math.ceil(200 / PREDICTION_DT);
const FAN_MIN_BUFFER_FRAMES = MAX_TRANSFER_FRAMES + 100;

let workerPool = [];               // Array of web workers
let workerPoolReady = false;       // Whether all workers hold the current prediction buffer
let workerReadyCount = 0;
let workerBufferShifts = 0;        // buffer shifts since the workers were last primed
let workerPrimePending = false;

// The fan. One entry per viable release angle, sorted by arrival, each:
//   { releaseAngle, arrivalOffset, error, burn:{start,duration,angle}, path:[{x,y}] }
let transferFan = [];
let fanHighlight = -1;             // index into transferFan the player is on, -1 for none
let fanLaunchFrame = -1;           // buffer frame the current fan launches from
let fanScanGeneration = 0;         // bumped per scan so stale shard results are dropped
let fanScanPending = 0;            // shards still working
let fanScanStartedAt = 0;
let fanScanElapsedMs = 0;          // wall time of the last completed scan, for the info bar
let fanScanSlowestShardMs = 0;     // worst shard's own time, to tell compute from overhead
let fanScanQueuedFrame = -1;       // frame we intend to scan once the view settles
let fanScanQueuedAt = 0;
let fanHasScanned = false;         // true once one scan has completed for this transfer

function initWorkerPool() {
    const numWorkers = navigator.hardwareConcurrency || 4;
    workerPool = [];

    for (let i = 0; i < numWorkers; i++) {
        const worker = new Worker('transfer-worker.js');
        worker.onmessage = (e) => handleWorkerMessage(i, e);
        worker.onerror = (e) => {
            console.error('Worker', i, 'uncaught error:', e.message, e.filename, e.lineno);
            if (fanScanPending > 0) fanScanPending--;
        };
        workerPool.push(worker);
    }

    workerPoolReady = false;
    workerReadyCount = 0;
}

// Hand every worker the current prediction buffer. Scans cannot start until they all
// acknowledge, because a shard integrating against a stale buffer would return
// trajectories that do not match the ones beside them in the same fan.
//
// This copies the whole buffer to every worker, so it is deliberately driven by demand
// rather than by the clock: workers are re-primed when a scan is about to need them and
// the buffer has moved since last time, not on every shift. Scans only happen when the
// player starts a transfer or moves the time wheel, so in practice this is rare.
function primeWorkers() {
    if (workerPool.length === 0) return;
    const bodiesMasses = bodies.map(b => b.mass);
    workerPoolReady = false;
    workerReadyCount = 0;
    workerBufferShifts = 0;
    for (const worker of workerPool) {
        worker.postMessage({ type: 'init', predictionBuffer, bodiesMasses });
    }
}

// True when the workers can be trusted to integrate against the same buffer the main
// thread is showing. Kicks off a prime if not, and returns false until it lands.
function workersAreCurrent() {
    if (workerPoolReady && workerBufferShifts === 0) return true;
    if (!workerPrimePending) {
        workerPrimePending = true;
        primeWorkers();
    }
    return false;
}

function handleWorkerMessage(workerIndex, e) {
    const msg = e.data;

    if (msg.type === 'error') {
        console.error('Worker', workerIndex, 'error:', msg.error, msg.stack);
        if (fanScanPending > 0) fanScanPending--;
        return;
    }

    if (msg.type === 'ready') {
        workerReadyCount++;
        if (workerReadyCount >= workerPool.length) {
            workerPoolReady = true;
            workerPrimePending = false;
        }
        return;
    }

    if (msg.type !== 'result') return;

    // Drop anything from a scan the player has already moved on from.
    if (msg.generation !== fanScanGeneration) return;

    for (const r of msg.results) {
        transferFan.push(r);
    }
    fanScanSlowestShardMs = Math.max(fanScanSlowestShardMs, msg.elapsedMs || 0);

    if (fanScanPending > 0) fanScanPending--;

    if (fanScanPending === 0) {
        finishFanScan();
    }
}

function finishFanScan() {
    // Earliest arrival first: the fan reads as a ranked list, and the default pick is the
    // quickest way there.
    transferFan.sort((a, b) => a.arrivalOffset - b.arrivalOffset);
    fanScanElapsedMs = performance.now() - fanScanStartedAt;
    fanHasScanned = true;

    fanHighlight = transferFan.length > 0 ? 0 : -1;

    if (transferState === 'searching') {
        transferState = 'ready';
    }

    console.log(`[Fan] ${transferSourceBody?.name}->${transferDestinationBody?.name} ` +
        `launch=${(fanLaunchFrame * PREDICTION_DT).toFixed(1)}m: ` +
        `${transferFan.length} viable in ${fanScanElapsedMs.toFixed(0)}ms ` +
        `(slowest shard ${fanScanSlowestShardMs.toFixed(0)}ms of ${workerPool.length})`);

    updateTransferPanel();
}

// Start a scan of the whole release circle for a launch at `launchFrame`.
function startFanScan(launchFrame) {
    if (!transferSourceBody || !transferDestinationBody) return;
    if (workerPool.length === 0 || !workerPoolReady) return;

    const sourceBodyIndex = bodies.indexOf(transferSourceBody);
    const destBodyIndex = bodies.indexOf(transferDestinationBody);
    if (sourceBodyIndex < 0 || destBodyIndex < 0) return;
    if (launchFrame < 0 || launchFrame >= predictionBuffer.length) return;

    const orbitRadius = transferSourceBody.radius + CRAFT_ORBITAL_ALTITUDE;

    const params = {
        launchFrame,
        sourceBodyIndex,
        destBodyIndex,
        destBodyRadius: transferDestinationBody.radius,
        orbitRadius,
        orbitalSpeed: Math.sqrt(G * transferSourceBody.mass / orbitRadius),
        escapeVelocity: Math.sqrt(2 * G * transferSourceBody.mass / orbitRadius),
        // Prograde. The release angle already covers every direction you can leave in;
        // reversing the orbit as well would only mirror the fan.
        orbitalDirection: 1,
    };

    fanScanGeneration++;
    transferFan = [];
    fanHighlight = -1;
    fanLaunchFrame = launchFrame;
    fanScanPending = workerPool.length;
    fanScanStartedAt = performance.now();
    fanScanSlowestShardMs = 0;
    fanScanQueuedFrame = -1;

    for (let i = 0; i < workerPool.length; i++) {
        workerPool[i].postMessage({
            type: 'scan',
            generation: fanScanGeneration,
            params,
            shardIndex: i,
            shardCount: workerPool.length,
            angleCount: FAN_ANGLE_COUNT,
        });
    }
}

// Called every frame while a transfer is being planned. Decides when the fan on screen no
// longer matches the moment being viewed, and re-scans once the view has settled.
function updateTransferSearch() {
    if (!transferIsPlanning()) return;
    if (!transferSourceBody || !transferDestinationBody) {
        resetTransferState();
        return;
    }
    if (predictionBuffer.length < FAN_MIN_BUFFER_FRAMES) return;

    const viewFrame = Math.round(timeViewOffset);

    // The fan still describes the moment on screen: nothing to do. Note that a buffer
    // shift moves BOTH timeViewOffset and fanLaunchFrame down together, so time simply
    // passing never looks like a scrub.
    if (viewFrame === fanLaunchFrame && fanScanPending === 0) return;

    if (fanScanPending > 0) return;   // let the in-flight scan land first

    // Wait for the wheel to stop before spending a scan on a frame the player is
    // sweeping past.
    const now = performance.now();
    if (fanScanQueuedFrame !== viewFrame) {
        fanScanQueuedFrame = viewFrame;
        fanScanQueuedAt = now;
        return;
    }
    if (now - fanScanQueuedAt < FAN_RESCAN_QUIET_MS) return;

    if (!workersAreCurrent()) return;   // priming; the next frame will get here again

    startFanScan(viewFrame);
}

// How a transfer's length is written, everywhere it appears. One function so the
// readout and the label on the curve cannot disagree about the same number.
function formatTransferDuration(frames) {
    const minutes = frames * PREDICTION_DT;
    if (minutes < 60) return `${minutes.toFixed(1)}m`;
    return `${Math.floor(minutes / 60)}h ${Math.round(minutes % 60)}m`;
}

// --- The fan on screen ---------------------------------------------------------
//
// One SVG path per viable release angle, drawn from a pool that grows to the widest fan
// seen and is then reused. Fans are re-scanned whenever the time wheel moves, so building
// and discarding elements per scan would churn the DOM for no reason.

const fanLayer = document.createElementNS(SVG_NS, 'g');
fanLayer.setAttribute('class', 'transfer-fan');
trajectoriesLayer.appendChild(fanLayer);

const fanPathPool = [];

// The duration readout that rides alongside whichever trajectory the finger is on.
const fanLabelGroup = document.createElementNS(SVG_NS, 'g');
fanLabelGroup.setAttribute('class', 'fan-label');
fanLabelGroup.style.display = 'none';
const fanLabelBg = document.createElementNS(SVG_NS, 'rect');
fanLabelBg.setAttribute('rx', '4');
const fanLabelText = document.createElementNS(SVG_NS, 'text');
fanLabelText.setAttribute('text-anchor', 'middle');
fanLabelText.setAttribute('dominant-baseline', 'central');
fanLabelGroup.appendChild(fanLabelBg);
fanLabelGroup.appendChild(fanLabelText);
uiLayer.appendChild(fanLabelGroup);

// The rocket for a transfer that has been chosen but not yet committed. Nothing exists to
// carry it yet — a Squadron is only made at Launch — so the fan owns one, standing on the
// origin exactly where the real one will and carrying the number currently on the slider.
// It is how "this many, this way, from here" is answered before anything is signed for.
//
// Built on first use, not here: the bodies are added to this layer by init(), and one made
// at load time would sit under every disc on the map instead of over the one it belongs to.
let previewRocket = null;
function getPreviewRocket() {
    if (!previewRocket) {
        previewRocket = createRocketElements(bodiesLayer);
        previewRocket.group.classList.add('preview');
    }
    return previewRocket;
}

// Hue for the i'th of n routes, spread evenly around the wheel.
//
// The fan is sorted by arrival time, and routes that arrive at similar times generally lie
// near each other on screen — so spreading by index is also spreading by position, which
// is where the telling-apart actually has to happen. Spread over the count rather than a
// fixed step, so a fan of three gets three widely separated colours instead of three
// neighbours off the same end of the wheel.
//
// Starts at 20deg (warm) and runs the long way round, which keeps the first few routes —
// the quick ones, the ones most likely to be taken — clear of the blue the accent colour
// and the grid already use.
function fanHue(i, n) {
    return Math.round(20 + (360 * i) / Math.max(1, n));
}

function fanPathElement(i) {
    while (fanPathPool.length <= i) {
        const p = document.createElementNS(SVG_NS, 'path');
        p.setAttribute('class', 'fan-path');
        p.setAttribute('fill', 'none');
        fanLayer.appendChild(p);
        fanPathPool.push(p);
    }
    return fanPathPool[i];
}

function clearFanElements() {
    for (const p of fanPathPool) {
        p.setAttribute('d', '');
        p.style.display = 'none';
    }
    fanLabelGroup.style.display = 'none';
    hideRocket(previewRocket);
}

// The rocket standing on the origin while a route is being chosen. It follows the same
// pose rule the real one will once it exists, read off the highlighted route's own screen
// polyline — so pressing Launch changes what it is, not where it is or where it points.
function updatePreviewRocket() {
    const entry = highlightedFanEntry();
    const pts = entry && entry._screen;
    if (!transferSourceBody || !pts || pts.length < 2) {
        hideRocket(previewRocket);
        return;
    }
    const { p0, p1 } = pathStartHeading(pts.length, (i) => pts[i]);
    const pose = parkedRocketPose(transferSourceBody, p0, p1);
    const count = parseInt(transferQtySlider.value, 10) || 0;
    placeRocket(getPreviewRocket(), pose.x, pose.y, pose.heading, count, true);
}

// Redraw the whole fan. Called once per frame from updateTrajectories, which is also
// where the screen polylines used for finger-picking get cached onto each entry.
function updateTransferFan() {
    const active = transferIsPlanning() && transferFan.length > 0;
    if (!active) {
        clearFanElements();
        return;
    }

    for (let i = 0; i < transferFan.length; i++) {
        const entry = transferFan[i];
        const pts = fanScreenPath(entry);
        entry._screen = pts;

        const el = fanPathElement(i);
        if (pts.length < 2) {
            el.setAttribute('d', '');
            el.style.display = 'none';
            continue;
        }

        let d = `M ${pts[0].x} ${pts[0].y}`;
        for (let j = 1; j < pts.length; j++) d += ` L ${pts[j].x} ${pts[j].y}`;
        el.setAttribute('d', d);
        el.style.display = '';
        el.style.setProperty('--fan-hue', fanHue(i, transferFan.length));
        el.classList.toggle('highlighted', i === fanHighlight);
    }

    for (let i = transferFan.length; i < fanPathPool.length; i++) {
        fanPathPool[i].setAttribute('d', '');
        fanPathPool[i].style.display = 'none';
    }

    updateFanLabel();
    updatePreviewRocket();
}

// The hovering duration label. It sits at the point of the highlighted trajectory nearest
// the finger, so it tracks the part of the curve being interrogated rather than parking at
// one end of it.
function updateFanLabel() {
    const entry = highlightedFanEntry();
    if (!entry || !entry._screen || entry._screen.length < 2) {
        fanLabelGroup.style.display = 'none';
        return;
    }

    const pts = entry._screen;
    let anchor = pts[Math.floor(pts.length / 2)];
    if (fanPointer) {
        let bestDist = Infinity;
        for (const p of pts) {
            const d = Math.hypot(p.x - fanPointer.x, p.y - fanPointer.y);
            if (d < bestDist) { bestDist = d; anchor = p; }
        }
    }

    fanLabelText.textContent = formatTransferDuration(entry.arrivalOffset);

    // Border in the highlighted route's own colour. With a dozen curves on screen the
    // label needs to say which one it is describing, and matching the outline says it
    // without a leader line.
    fanLabelGroup.style.setProperty('--fan-hue', fanHue(fanHighlight, transferFan.length));

    // Offset up and right of the curve so the finger does not cover the number it just
    // asked for.
    const lx = anchor.x + FAN_LABEL_OFFSET_PX;
    const ly = anchor.y - FAN_LABEL_OFFSET_PX;
    fanLabelText.setAttribute('x', lx);
    fanLabelText.setAttribute('y', ly);

    const box = fanLabelText.getBBox();
    fanLabelBg.setAttribute('x', box.x - 6);
    fanLabelBg.setAttribute('y', box.y - 3);
    fanLabelBg.setAttribute('width', box.width + 12);
    fanLabelBg.setAttribute('height', box.height + 6);

    fanLabelGroup.style.display = '';
}

const FAN_LABEL_OFFSET_PX = 22;

// Where the finger is while dragging over the fan, in SVG coordinates. Null when not
// dragging, which parks the label at the middle of the highlighted curve.
let fanPointer = null;

// Screen polyline for one fan entry, warped to match the display. Recomputed per frame:
// the camera, the warp and the bodies all move, and a cached path would lag them.
function fanScreenPath(entry) {
    const path = entry.path;
    if (!path || path.length < 2) return [];
    const frames = [];
    for (let i = 0; i < path.length; i++) frames.push(i);
    return warpSampledTrajectory(frames, i => path[Math.min(i, path.length - 1)]).map(p => p.screen);
}

// Which trajectory is the finger on? Nearest by distance to the drawn polyline rather
// than DOM hit-testing: the curves converge near both bodies, and a hit test would hand
// back whichever happened to be painted last instead of the one actually closest.
function fanEntryAt(screenX, screenY, radius = FAN_PICK_RADIUS_PX) {
    let best = -1;
    let bestDist = radius;

    for (let i = 0; i < transferFan.length; i++) {
        const pts = transferFan[i]._screen;
        if (!pts || pts.length < 2) continue;
        for (let j = 1; j < pts.length; j++) {
            const d = distanceToSegment(screenX, screenY, pts[j - 1], pts[j]);
            if (d < bestDist) { bestDist = d; best = i; }
        }
    }

    return best;
}

function distanceToSegment(px, py, a, b) {
    const dx = b.x - a.x, dy = b.y - a.y;
    const lenSq = dx * dx + dy * dy;
    if (lenSq < 1e-9) return Math.hypot(px - a.x, py - a.y);
    let t = ((px - a.x) * dx + (py - a.y) * dy) / lenSq;
    t = Math.max(0, Math.min(1, t));
    return Math.hypot(px - (a.x + t * dx), py - (a.y + t * dy));
}

function highlightedFanEntry() {
    if (fanHighlight < 0 || fanHighlight >= transferFan.length) return null;
    return transferFan[fanHighlight];
}

// --- Committing ----------------------------------------------------------------

// Re-integrate a chosen release angle at full resolution. The worker ships a subsampled
// path, which is plenty to draw a fan of twenty curves but not what a craft should
// actually fly; this reproduces the worker's integration exactly, frame for frame.
function simulateTransferFlight(sourceBody, launchFrame, releaseAngle, burn) {
    if (launchFrame >= predictionBuffer.length) return [];

    const orbitRadius = sourceBody.radius + CRAFT_ORBITAL_ALTITUDE;
    const orbitalSpeed = Math.sqrt(G * sourceBody.mass / orbitRadius);
    const escapeVelocity = Math.sqrt(2 * G * sourceBody.mass / orbitRadius);
    const sourceIndex = bodies.indexOf(sourceBody);

    const start = predictionBuffer[launchFrame][sourceIndex];
    let x = start.x + orbitRadius * Math.cos(releaseAngle);
    let y = start.y + orbitRadius * Math.sin(releaseAngle);
    let vx = start.vx - orbitalSpeed * Math.sin(releaseAngle);
    let vy = start.vy + orbitalSpeed * Math.cos(releaseAngle);
    let isAccelerating = true;

    const out = [];
    const lastFrame = Math.min(predictionBuffer.length, launchFrame + MAX_TRANSFER_FRAMES);

    for (let frame = launchFrame; frame < lastFrame; frame++) {
        const offset = frame - launchFrame;
        const bodyStates = predictionBuffer[frame];

        let ax = 0, ay = 0;
        for (let i = 0; i < bodyStates.length; i++) {
            const s = bodyStates[i];
            const dx = s.x - x, dy = s.y - y;
            const dist = Math.sqrt(dx * dx + dy * dy);
            const safeDist = Math.max(dist, MIN_DISTANCE);
            const a = G * bodies[i].mass / (safeDist * safeDist);
            ax += a * (dx / dist);
            ay += a * (dy / dist);
        }

        if (isAccelerating) {
            const src = bodyStates[sourceIndex];
            const dx = x - src.x, dy = y - src.y;
            const dist = Math.sqrt(dx * dx + dy * dy);
            ax += CRAFT_ACCELERATION * (-dy / dist);
            ay += CRAFT_ACCELERATION * (dx / dist);
            const relVx = vx - src.vx, relVy = vy - src.vy;
            if (Math.sqrt(relVx * relVx + relVy * relVy) >= 1.1 * escapeVelocity) {
                isAccelerating = false;
            }
        }

        if (burn && offset >= burn.start && offset < burn.start + burn.duration) {
            ax += CRAFT_ACCELERATION * Math.cos(burn.angle);
            ay += CRAFT_ACCELERATION * Math.sin(burn.angle);
        }

        vx += ax * PREDICTION_DT;
        vy += ay * PREDICTION_DT;
        x += vx * PREDICTION_DT;
        y += vy * PREDICTION_DT;

        out.push({ x, y, vx, vy, isAccelerating });
    }

    return out;
}

// --- Panel ---------------------------------------------------------------------

const transferControlsPanel = document.getElementById('transfer-controls-panel');
const transferReadout = document.getElementById('transfer-readout');
const trajectoryInfoBar = document.getElementById('trajectory-info-bar');
const scheduleLaunchBtn = document.getElementById('schedule-launch-btn');
const cancelTransferBtn = document.getElementById('cancel-transfer-btn');
const transferLaunchControls = document.getElementById('transfer-launch-controls');
const transferQtySlider = document.getElementById('transfer-qty-slider');
const transferStayLabel = document.getElementById('transfer-stay-label');
const transferLaunchLabel = document.getElementById('transfer-launch-label');
const transferAvailLabel = document.getElementById('transfer-avail-label');

transferQtySlider.addEventListener('input', () => {
    transferQtyTouched = true; // stop updateTransferSlider from overriding the choice
    const launchCount = parseInt(transferQtySlider.value);
    const maxCount = parseInt(transferQtySlider.max);
    transferStayLabel.textContent = maxCount - launchCount;
    transferLaunchLabel.textContent = launchCount;
    transferAvailLabel.textContent = maxCount;
    scheduleLaunchBtn.disabled = launchCount === 0 || !highlightedFanEntry();
});

function updateTransferPanel() {
    const active = transferIsPlanning();
    if (!active) {
        transferControlsPanel.style.display = 'none';
        transferReadout.style.display = 'none';
        transferLaunchControls.style.display = 'none';
        return;
    }

    transferControlsPanel.style.display = 'block';
    transferReadout.style.display = 'block';
    document.getElementById('selected-body-info').style.display = 'none';

    const destName = transferDestinationBody ? transferDestinationBody.name : '';
    let html = `<span>Transfer to <strong>${destName}</strong></span>`;
    // When it leaves. The clock is showing the launch moment, and the transfer opens with
    // that moment set ahead of the present (see TRANSFER_LEAD_MINUTES), so this counts
    // down while they choose — it is the only place that lead is visible with the time
    // wheel closed. Outside the scan branch below, so it does not blink out on a re-scan.
    html += `<span><span class="info-label">Launch:</span> +${formatTransferDuration(Math.round(timeViewOffset))}</span>`;

    if (!fanHasScanned || fanScanPending > 0) {
        html += `<span><span class="info-label">Scanning release angles…</span></span>`;
        trajectoryInfoBar.innerHTML = html;
        // Leave the launch controls as they are while re-scanning. Candidates come and go
        // as the wheel moves, and hiding the slider mid-scan pulled it out from under the
        // player's finger.
        if (transferLaunchControls.style.display !== 'none') scheduleLaunchBtn.disabled = true;
        return;
    }

    const entry = highlightedFanEntry();
    html += `<span><span class="info-label">Routes:</span> ${transferFan.length}</span>`;

    if (entry) {
        html += `<span><span class="info-label">Release:</span> ${(entry.releaseAngle * 180 / Math.PI).toFixed(0)}°</span>`;
        html += `<span><span class="info-label">Duration:</span> ${formatTransferDuration(entry.arrivalOffset)}</span>`;
    } else {
        html += `<span>No route from here at this moment — try the clock</span>`;
    }

    trajectoryInfoBar.innerHTML = html;

    if (transferFan.length > 0) {
        transferLaunchControls.style.display = '';
        updateTransferSlider();
    } else {
        // Launch shares a row with Cancel rather than living inside the block being
        // hidden here, so it has to be disabled explicitly — hiding the slider is not
        // enough to stop a stale Launch being pressed against an empty fan.
        transferLaunchControls.style.display = 'none';
        scheduleLaunchBtn.disabled = true;
    }
}

// Configure the transfer quantity slider based on available craft at source body
function updateTransferSlider() {
    if (!transferSourceBody) return;
    // What is at the body at the launch moment and not already promised elsewhere. Counted
    // at fanLaunchFrame rather than now, because that is when this transfer leaves.
    const maxCount = getSendableCraftAtBody(transferSourceBody, Math.max(0, fanLaunchFrame));
    if (maxCount <= 0) {
        transferLaunchControls.style.display = 'none';
        scheduleLaunchBtn.disabled = true;
        return;
    }
    transferQtySlider.max = maxCount;
    // Default to sending everything, but only until the player picks a number —
    // otherwise this runs every frame and drags their choice back up.
    if (!transferQtyTouched) {
        transferQtySlider.value = maxCount;
    }
    if (parseInt(transferQtySlider.value) > maxCount) {
        transferQtySlider.value = maxCount;
    }
    const launchCount = parseInt(transferQtySlider.value);
    transferStayLabel.textContent = maxCount - launchCount;
    transferLaunchLabel.textContent = launchCount;
    transferAvailLabel.textContent = maxCount;
    scheduleLaunchBtn.disabled = launchCount === 0 || !highlightedFanEntry();
}

scheduleLaunchBtn.addEventListener('click', () => {
    const entry = highlightedFanEntry();
    if (!entry || !transferSourceBody || !transferDestinationBody) return;
    if (transferState !== 'ready' && transferState !== 'searching') return;

    // Never commit more than actually exists — the slider max is refreshed per frame,
    // but a stale value must not be trusted at click time.
    const available = getSendableCraftAtBody(transferSourceBody, Math.max(0, fanLaunchFrame));
    const launchCount = Math.min(parseInt(transferQtySlider.value), available);
    if (launchCount <= 0) return;

    const trajectory = simulateTransferFlight(
        transferSourceBody, fanLaunchFrame, entry.releaseAngle, entry.burn
    );
    if (trajectory.length === 0) return;
    const flight = trajectory.slice(0, entry.arrivalOffset + 1);

    // Take the craft: from the body's own total first, then from anything still inbound
    // that can be chained onward. Written down as it goes, because a launch that has not
    // happened yet can still be called off — see withdrawScheduledTransfer.
    const drawnFrom = [];
    let remaining = launchCount;
    const fromBody = Math.min(remaining, transferSourceBody.craftCount);
    transferSourceBody.craftCount -= fromBody;
    if (fromBody > 0) drawnFrom.push({ body: transferSourceBody, count: fromBody });
    remaining -= fromBody;

    if (remaining > 0) {
        for (const sq of squadrons) {
            if (remaining <= 0) break;
            if (sq.destinationBody !== transferSourceBody || sq.count <= 0) continue;
            // Only from squadrons that have landed by the moment this one leaves. The
            // same test getSendableCraftAtBody counted with — drawing from one still in
            // the air would have craft departing before they arrived.
            if (fanLaunchFrame - sq.launchFrame < sq.trajectoryBuffer.length) continue;
            const deduct = Math.min(remaining, sq.count);
            sq.count -= deduct;
            drawnFrom.push({ squadron: sq, count: deduct });
            remaining -= deduct;
        }
    }

    // Defensive: if the pool could not cover the request, ship only what was actually
    // taken. Leaving `remaining` unspent would create craft from nothing.
    const shipped = launchCount - remaining;
    if (shipped <= 0) return;
    if (remaining > 0) {
        console.warn(`[Transfer] Short by ${remaining}; shipping ${shipped} instead of ${launchCount}`);
    }

    const transit = new Squadron(transferSourceBody, shipped);
    transit.createElements();
    squadrons.push(transit);

    transit.launchFrame = fanLaunchFrame;
    transit.sourceBody = transferSourceBody;
    transit.destinationBody = transferDestinationBody;
    transit.trajectoryBuffer = flight;
    transit.releaseAngle = entry.releaseAngle;
    // The burn as it will be depicted, clipped to the frames the flight actually has.
    // The optimizer is free to run a burn past the arrival — nothing after arrival is
    // integrated, so the tail costs it nothing — and the trajectory is cut at
    // arrivalOffset. On a short hop the burn can be longer than the whole flight, which
    // left the craft drawn as still burning on its final frame.
    const burnDuration = entry.burn
        ? Math.min(entry.burn.duration, entry.arrivalOffset - entry.burn.start)
        : 0;
    transit.correctionParams = burnDuration > 0
        ? { angle: entry.burn.angle, duration: burnDuration, startFrame: entry.burn.start }
        : null;
    transit.insertionFrame = entry.arrivalOffset;
    transit.flightFrame = 0;
    transit._displayCount = 0;   // no position of its own until its launch moment
    transit._displayPhase = 'pending';
    // Where every craft aboard came from, so the launch can be undone exactly if the
    // player reopens it before it goes.
    transit.drawnFrom = drawnFrom;

    scheduledTransfers.push({
        squadron: transit,
        sourceBody: transferSourceBody,
        destBody: transferDestinationBody,
    });

    // Deselect so the map is clear to watch the new transfer fly
    selectedSquadron = null;
    selectedBody = null;
    isTrackingSelectedSquadron = false;

    resetTransferState();
});

cancelTransferBtn.addEventListener('click', () => {
    if (transferIsPlanning()) {
        resetTransferState();
    }
});

// --- Lifecycle -----------------------------------------------------------------

// A transfer is being chosen: the fan is up, or a scan for it is out. Both states are the
// same thing to everything outside the search — the player is mid-decision — so they are
// asked about together.
function transferIsPlanning() {
    return transferState === 'searching' || transferState === 'ready';
}

// Unmake a launch that has not gone yet: every craft aboard goes back exactly where it was
// taken from and the squadron stops existing.
//
// Exactly, because a launch can draw from two places — the body's own total and anything
// that had already landed there — and putting it all back on the body would count craft as
// present in the meantime that were still in the air. scheduleLaunchBtn writes down what
// it took (`drawnFrom`) for this.
function withdrawScheduledTransfer(sq) {
    for (const claim of sq.drawnFrom || []) {
        if (claim.body) {
            claim.body.craftCount += claim.count;
        } else if (claim.squadron && squadrons.includes(claim.squadron)) {
            claim.squadron.count += claim.count;
        } else if (sq.sourceBody) {
            // The squadron they were promised out of has since landed here and stopped
            // being one. Its craft are part of this body's total now, so that is where
            // these go back to.
            sq.sourceBody.craftCount += claim.count;
        }
    }
    sq.drawnFrom = null;
    sq.count = 0;

    for (let i = scheduledTransfers.length - 1; i >= 0; i--) {
        if (scheduledTransfers[i].squadron === sq) scheduledTransfers.splice(i, 1);
    }
    const idx = squadrons.indexOf(sq);
    if (idx !== -1) squadrons.splice(idx, 1);
    if (selectedSquadron === sq) {
        selectedSquadron = null;
        isTrackingSelectedSquadron = false;
    }
    sq.removeElements();
}

// Reopen a launch that has not gone yet, so the number going can be changed or the whole
// thing called off.
//
// It is done by unmaking it: the craft go back, the squadron stops existing, and what is
// left is exactly the plan that produced it — same pair, same launch moment, same count on
// the slider. So Launch commits a fresh one and Cancel simply does not, and "adjust it" and
// "drop it" are the two buttons already on the panel instead of a mode with its own rules.
function openScheduledTransfer(sq) {
    if (!sq || sq.launchFrame <= 0) return false;
    const source = sq.sourceBody;
    const dest = sq.destinationBody;
    if (!source || !dest) return false;

    const launchAt = sq.launchFrame;
    const count = sq.count;
    withdrawScheduledTransfer(sq);

    if (transferIsPlanning()) resetTransferState();
    transferSourceBody = source;
    transferDestinationBody = dest;
    selectBody(source);
    startTransferSearch(launchAt);
    // Widen the range before writing the number in. startTransferSearch leaves the slider
    // on a placeholder max of 1 until the first scan comes back, and an input clamps a
    // value to its max the moment it is set — so the count would arrive as 1 and stay
    // there, transferQtyTouched having promised not to touch it again.
    transferQtySlider.max = Math.max(count, 1);
    transferQtySlider.value = count;
    transferQtyTouched = true;   // already their number, not one to be overwritten
    return true;
}

// The launch still waiting at its origin under this point, if any.
//
// Tight, and it has to beat the body it is standing on: the rocket sits on the rim, so the
// body's own tap circle covers it entirely. Nearest-wins keeps the rest of the disc the
// body's — tap the planet to send more, tap the rocket to change what is already going.
function pendingRocketAt(screenX, screenY) {
    let best = null;
    let bestDist = ROCKET_TAP_RADIUS;

    for (const craft of squadrons) {
        if (craft.launchFrame <= 0 || !craft._rocketScreen || craft.count <= 0) continue;
        const d = Math.hypot(screenX - craft._rocketScreen.x, screenY - craft._rocketScreen.y);
        if (d >= bestDist) continue;
        if (craft.sourceBody) {
            const c = bodyScreenPos(craft.sourceBody);
            if (d >= Math.hypot(screenX - c.x, screenY - c.y)) continue;
        }
        best = craft;
        bestDist = d;
    }

    return best;
}

// A transfer opens on a launch that is still ahead of the player rather than on the
// present. Choosing takes a moment — a route out of the fan, a number of craft — and a
// launch moment that has already gone past is one they cannot still be deciding about.
// The same lead is put back if the clock catches up with it mid-decision, so the window
// they are choosing within is always one they can still reach.
const TRANSFER_LEAD_MINUTES = 10;
const TRANSFER_LEAD_FRAMES = Math.round(TRANSFER_LEAD_MINUTES / PREDICTION_DT);

function startTransferSearch(openAtFrame = null) {
    // Open on a launch the player has time to decide about. Only when the clock is at or
    // near the present: further out than the lead is where they put it themselves, hunting
    // for a window, and dragging that back would undo the search they came here with.
    //
    // A launch being reopened brings its own moment with it — the one already chosen is
    // the one being reconsidered — so that overrides both the lead and the exception.
    if (openAtFrame !== null || timeViewOffset < TRANSFER_LEAD_FRAMES) {
        // Only the first time in. Re-aiming at a new destination comes straight back
        // through here, and capturing again would record the moment this feature set as
        // the one to hand back to — the same rule the scale and the camera follow above.
        if (clockBeforeTransfer === null) clockBeforeTransfer = Math.round(timeViewOffset);
        setTimeViewOffset(openAtFrame !== null ? openAtFrame : TRANSFER_LEAD_FRAMES);
        clockSetByTransfer = Math.round(timeViewOffset);
    }

    // Drop to true scale for the duration, and remember what to put back. Only on the way
    // in from 'none': re-aiming at a new destination calls straight back through here
    // without a reset, and capturing again would record the mode this feature just set
    // and leave the player stuck in it.
    if (scaleBeforeTransfer === null) {
        scaleBeforeTransfer = trueScaleOn;
        cameraBeforeTransfer = { x: camera.x, y: camera.y, zoom: camera.zoom };
        setTrueScale(true, performance.now());
    }
    // A new pair to frame, so the fit gets the view back even if the player had grabbed
    // it during the last one.
    transferViewReleased = false;

    // Back on top of the discs. Resetting the game rebuilds every body into this layer,
    // which would leave a preview made before that buried under them.
    if (previewRocket) bodiesLayer.appendChild(previewRocket.group);

    transferState = 'searching';

    transferQtySlider.max = 1;
    transferQtySlider.value = 0;
    transferQtyTouched = false;
    transferLaunchControls.style.display = 'none';

    transferFan = [];
    fanHighlight = -1;
    fanLaunchFrame = -1;
    fanHasScanned = false;
    fanScanPending = 0;
    fanScanQueuedFrame = -1;
    fanScanGeneration++;

    updateTransferPanel();
}

function resetTransferState() {
    // Put the view back the way the player had it. Null means either that no transfer was
    // being planned or that they pressed the scale button themselves partway through, in
    // which case the mode on screen is their decision and not ours to undo.
    if (scaleBeforeTransfer !== null) {
        setTrueScale(scaleBeforeTransfer, performance.now());
        scaleBeforeTransfer = null;
    }
    // And the camera with it, if the fit still had it. Auto-fit would put the whole system
    // back on its own, but auto-fit is off whenever the player has panned at any point in
    // the session — and then nothing would move the view, leaving it parked on the framing
    // of a route that no longer exists. What was borrowed gets returned either way.
    viewRestore = transferViewReleased ? null : cameraBeforeTransfer;
    cameraBeforeTransfer = null;

    // And the clock. Leaving it out on the launch moment is what made a scheduled launch
    // look like it had already gone: the craft do wait, but the map was still showing the
    // moment they leave on. Only if the clock is still where this feature put it — a player
    // who has moved the wheel since has taken it back, the same way pressing the scale
    // button takes the scale back.
    if (clockBeforeTransfer !== null && Math.round(timeViewOffset) === clockSetByTransfer) {
        setTimeViewOffset(clockBeforeTransfer);
    }
    clockBeforeTransfer = null;
    clockSetByTransfer = -1;

    transferState = 'none';
    transferSourceBody = null;
    transferDestinationBody = null;
    transferFan = [];
    fanHighlight = -1;
    fanLaunchFrame = -1;
    fanHasScanned = false;
    fanScanPending = 0;
    fanScanQueuedFrame = -1;
    fanScanGeneration++;      // orphan any shard results still in flight

    transferControlsPanel.style.display = 'none';
    transferReadout.style.display = 'none';
    transferLaunchControls.style.display = 'none';
    clearFanElements();
}

// Keep the fan pinned to the same physical moment as the buffer shifts underneath it.
// The trajectories themselves are still correct — only their index into the buffer moved,
// which is why time simply passing never reads as a scrub and never triggers a re-scan.
function updateFanOnShift() {
    if (fanLaunchFrame > 0) fanLaunchFrame--;
    workerBufferShifts++;
}


// Pure simulation step for prediction (doesn't modify actual bodies)
// Takes an array of body states and returns the next state
function simulateStep(states, masses, dt) {
    const n = states.length;

    // Calculate accelerations for all bodies
    const accelerations = states.map((state, i) => {
        let ax = 0;
        let ay = 0;

        for (let j = 0; j < n; j++) {
            if (i === j) continue;

            const dx = states[j].x - state.x;
            const dy = states[j].y - state.y;
            const distSq = dx * dx + dy * dy;
            const dist = Math.sqrt(distSq);
            const safeDist = Math.max(dist, MIN_DISTANCE);

            const acceleration = G * masses[j] / (safeDist * safeDist);
            ax += acceleration * (dx / dist);
            ay += acceleration * (dy / dist);
        }

        return { ax, ay };
    });

    // Return new states with updated velocities and positions
    return states.map((state, i) => {
        const { ax, ay } = accelerations[i];
        const nvx = state.vx + ax * dt;
        const nvy = state.vy + ay * dt;
        return {
            x: state.x + nvx * dt,
            y: state.y + nvy * dt,
            vx: nvx,
            vy: nvy
        };
    });
}

// Get current body states as an array
function getBodyStates() {
    return bodies.map(body => ({
        x: body.x,
        y: body.y,
        vx: body.vx,
        vy: body.vy
    }));
}

// Get body masses (constant, so we cache this)
function getBodyMasses() {
    return bodies.map(body => body.mass);
}

// Reset prediction buffer
function resetPredictions() {
    predictionBuffer = [];
    predictionTimeAccum = 0;
    sampleOffset = 0;
}

// Fixed sample interval for craft trajectory rendering
const SAMPLE_INTERVAL = 4;

// ===== How far ahead the orbit paths run =====
//
// A body's future path is on the map to answer one question: where will this planet be
// when the craft get to it. So it is drawn exactly that far and no further — out to the
// arrival of the last thing still on its way at the moment being viewed, and, while a
// transfer is being chosen, out to the arrival of the route currently picked. The end of
// every orbit line is therefore a moment the player cares about, and all of them end at
// the same one, which is what makes them comparable at a glance.
//
// Nothing in the air and nothing being planned means there is no question to answer, and
// the paths are not drawn at all. That is the point of tying them to the flights: the
// lines used to run a fixed quarter of the prediction buffer into the future, which said
// nothing in particular and left the map permanently ruled with arcs.
//
// Returns the last buffer frame to draw, or -1 for "draw nothing".
function bodyTrajectoryHorizon(scrubFrame) {
    let horizon = -1;

    for (const craft of squadrons) {
        // Counted whether it has left yet or not: a launch still waiting on its moment
        // already has its whole path on the map, and its arrival is exactly the moment
        // being asked about.
        if (craft.count <= 0 || craft.trajectoryBuffer.length === 0) continue;
        const arrival = Math.max(0, craft.launchFrame) +
            Math.min(craft.trajectoryBuffer.length, MAX_CRAFT_PREDICTION_FRAMES) - 1;
        if (arrival > scrubFrame && arrival > horizon) horizon = arrival;
    }

    // The route being considered, while the slider is up to send craft along it. Not the
    // whole fan: the other routes are alternatives, and running the orbits out to the
    // slowest of twenty would swamp the one being chosen.
    if (transferLaunchControls.style.display !== 'none') {
        const entry = highlightedFanEntry();
        if (entry) horizon = Math.max(horizon, fanLaunchFrame + entry.arrivalOffset);
    }

    return Math.min(horizon, predictionBuffer.length - 1);
}

// Update trajectory path elements with current predictions
function updateTrajectories() {
    if (predictionBuffer.length === 0) return;

    // When scrubbing forward, skip trajectory frames before the scrub position
    // so paths get "consumed" like they do during normal time advancement
    const scrubFrame = Math.round(timeViewOffset);

    // Where every orbit line stops — see "How far ahead the orbit paths run".
    const horizon = bodyTrajectoryHorizon(scrubFrame);
    const fromFrame = Math.max(0, scrubFrame);

    for (let bodyIndex = 0; bodyIndex < bodies.length; bodyIndex++) {
        const body = bodies[bodyIndex];
        if (!body.trajectoryPath) continue;

        if (horizon <= fromFrame) {
            body.trajectoryPath.setAttribute('d', '');
            continue;
        }

        // Enough points to keep the curve smooth over however long the flight is.
        const visibleFrames = horizon - fromFrame + 1;
        const sampleInterval = Math.max(1, Math.ceil(visibleFrames / MAX_TRAJECTORY_POINTS));

        // Samples sit on a fixed grid that shifts with the buffer rather than with the
        // viewed frame, so the vertices stay put as time passes instead of crawling
        // along the curve.
        const gridPhase = sampleOffset % sampleInterval;
        const frames = [];
        for (let i = fromFrame + ((gridPhase - fromFrame) % sampleInterval + sampleInterval) % sampleInterval;
             i <= horizon; i += sampleInterval) {
            frames.push(i);
        }
        // The arrival itself, always: it is the whole reason the line is drawn.
        if (frames.length === 0 || frames[frames.length - 1] !== horizon) frames.push(horizon);

        const points = warpSampledTrajectory(frames, f => predictionBuffer[f][bodyIndex]);

        // Drawn backwards, from the arrival to the body. The line is dashed, and a dash
        // pattern starts at the start of the path — so drawing it this way anchors the
        // dashes to the moment they are about, and the pattern stays put while the near
        // end is eaten away by time passing. Started at the body instead, every dash on
        // every orbit would crawl along its curve for the whole flight.
        //
        // The body's own position ends the line rather than a sampled frame, which can be
        // up to sampleInterval away from where it actually is.
        const bodyScreen = displayTransform(body.x, body.y);
        let d = '';
        for (let i = points.length - 1; i >= 0; i--) {
            const p = points[i].screen;
            d += d === '' ? `M ${p.x} ${p.y}` : ` L ${p.x} ${p.y}`;
        }
        d += ` L ${bodyScreen.x} ${bodyScreen.y}`;
        body.trajectoryPath.setAttribute('d', d);
    }

    // Helper to collect sampled points from a trajectory segment
    function collectPoints(prediction, launchFrame, effectiveSampleOffset) {
        // How far into its own flight this squadron is at the moment being viewed. Frames
        // before it are dropped, so scrubbing forward eats the path the same way time
        // passing does.
        //
        // Not conditional on launchFrame: a squadron already under way has launchFrame 0,
        // and clamping at zero covers a launch still in the future on its own. (This used
        // to be gated on launchFrame > 0, from when a transfer could only be scheduled for
        // a future moment and launchFrame 0 meant "parked, no flight to be part-way
        // through". Launches happen at the viewed moment now, so that gate excluded every
        // squadron actually in the air — the whole path stayed drawn, and the start point
        // below jumped to the craft, leaving a straight line back to the launch point.)
        const craftScrubFrame = Math.max(0, scrubFrame - launchFrame);
        const maxFrames = Math.min(prediction.length, MAX_CRAFT_PREDICTION_FRAMES);

        const frames = [];
        if (effectiveSampleOffset !== 0 && maxFrames > 0 && craftScrubFrame <= 0) {
            frames.push(0);
        }
        for (let i = effectiveSampleOffset; i < maxFrames; i += SAMPLE_INTERVAL) {
            if (i < craftScrubFrame) continue;
            frames.push(i);
        }
        const lastFrame = maxFrames - 1;
        if (lastFrame >= 0 && lastFrame >= craftScrubFrame && (frames.length === 0 || frames[frames.length - 1] !== lastFrame)) {
            frames.push(lastFrame);
        }
        return { points: warpSampledTrajectory(frames, f => prediction[f]), craftScrubFrame };
    }

    // Build path from a list of points with a given start position
    function buildPath(startScreen, points) {
        if (points.length === 0) return '';
        let path = `M ${startScreen.x} ${startScreen.y}`;
        for (const point of points) {
            path += ` L ${point.screen.x} ${point.screen.y}`;
        }
        return path;
    }

    // Render craft trajectories (every squadron is in flight or scheduled to be)
    for (const craft of squadrons) {
        if (!craft.trajectoryPath) continue;

        let fullPath = '';

        {
            const craftPrediction = craft.trajectoryBuffer;
            if (craftPrediction.length === 0) {
                craft.trajectoryPath.setAttribute('d', '');
                if (craft.trajectoryHitArea) craft.trajectoryHitArea.setAttribute('d', '');
                if (craft.correctionOverlay) craft.correctionOverlay.style.display = 'none';
                continue;
            }

            const effectiveLaunchFrame = Math.max(0, craft.launchFrame);
            const effectiveSampleOffset = sampleOffset;

            // Nothing left to draw: by the moment in view these craft have arrived and
            // joined the destination's total.
            if (scrubFrame >= effectiveLaunchFrame + craftPrediction.length) {
                craft.trajectoryPath.setAttribute('d', '');
                if (craft.trajectoryHitArea) craft.trajectoryHitArea.setAttribute('d', '');
                if (craft.correctionOverlay) craft.correctionOverlay.style.display = 'none';
                continue;
            }

            const { points, craftScrubFrame } = collectPoints(craftPrediction, effectiveLaunchFrame, effectiveSampleOffset);
            if (points.length > 0) {
                // The line starts at the dot, not at the first sampled frame — sampling is
                // on a fixed grid, so the first frame kept is up to SAMPLE_INTERVAL ahead of
                // where the craft actually is, and starting there would leave a gap between
                // the two. syncToViewFrame has already placed the dot at the viewed moment.
                //
                // The exception is a launch still in the future, where there is no dot yet:
                // those craft are counted at their origin until they go, so the path starts
                // at the launch point.
                const startScreen = (effectiveLaunchFrame > 0 && craftScrubFrame <= 0)
                    ? displayTransform(craftPrediction[0].x, craftPrediction[0].y)
                    : squadronScreenPos(craft);
                fullPath = buildPath(startScreen, points);
            }

            // Correction overlay
            if (craft.correctionParams && craft.correctionParams.duration > 0 && craft.correctionOverlay) {
                const cp = craft.correctionParams;
                const correctionEndFrame = cp.startFrame + cp.duration;
                const overlayPoints = [];
                for (let i = Math.max(cp.startFrame, craftScrubFrame); i <= correctionEndFrame && i < craftPrediction.length; i++) {
                    const pos = craftPrediction[i];
                    overlayPoints.push(displayTransform(pos.x, pos.y));
                }
                if (overlayPoints.length > 1) {
                    let op = `M ${overlayPoints[0].x} ${overlayPoints[0].y}`;
                    for (let j = 1; j < overlayPoints.length; j++) {
                        op += ` L ${overlayPoints[j].x} ${overlayPoints[j].y}`;
                    }
                    craft.correctionOverlay.setAttribute('d', op);
                    craft.correctionOverlay.style.display = 'block';
                } else {
                    craft.correctionOverlay.style.display = 'none';
                }
            } else if (craft.correctionOverlay) {
                craft.correctionOverlay.style.display = 'none';
            }
        }

        if (fullPath.trim() === '') {
            craft.trajectoryPath.setAttribute('d', '');
            if (craft.trajectoryHitArea) craft.trajectoryHitArea.setAttribute('d', '');
            // Don't hide correctionOverlay here - already handled above
        } else {
            craft.trajectoryPath.setAttribute('d', fullPath);
            if (craft.trajectoryHitArea) {
                craft.trajectoryHitArea.setAttribute('d', fullPath);
            }
        }
    }

    // The candidate transfers, drawn as a fan of release angles rather than one
    // best-so-far trajectory.
    updateTransferFan();
}

// Convert world coordinates to screen coordinates
function worldToScreen(x, y) {
    return {
        x: (x - camera.x) * camera.zoom + svgWidth / 2,
        y: (y - camera.y) * camera.zoom + svgHeight / 2
    };
}

// Convert screen coordinates to world coordinates
function screenToWorld(screenX, screenY) {
    return {
        x: (screenX - svgWidth / 2) / camera.zoom + camera.x,
        y: (screenY - svgHeight / 2) / camera.zoom + camera.y
    };
}

// The rubber band drawn while a transfer drag is in flight. Deliberately a
// straight line, not a trajectory — it says "these two bodies", not "this path".
let transferDragLine = null;

function createTransferDragLine() {
    transferDragLine = document.createElementNS(SVG_NS, 'line');
    transferDragLine.setAttribute('id', 'transfer-drag-line');
    transferDragLine.style.display = 'none';
    uiLayer.appendChild(transferDragLine);
}

function updateTransferDragLine() {
    if (!transferDrag) {
        transferDragLine.style.display = 'none';
        return;
    }
    const from = bodyScreenPos(transferDrag.source);
    // Snap to the destination's centre once one is under the finger, so the band
    // visibly commits rather than trailing the fingertip over the target.
    const to = transferDrag.target ? bodyScreenPos(transferDrag.target)
                                  : { x: transferDrag.x, y: transferDrag.y };
    transferDragLine.setAttribute('x1', from.x);
    transferDragLine.setAttribute('y1', from.y);
    transferDragLine.setAttribute('x2', to.x);
    transferDragLine.setAttribute('y2', to.y);
    transferDragLine.classList.toggle('locked', !!transferDrag.target);
    transferDragLine.style.display = '';
}

// Grid system - dynamic spacing based on zoom
// Generate "nice" spacing values: 1, 2, 5, 10, 20, 50, 100, ...
function getNiceSpacings() {
    const spacings = [];
    const multipliers = [1, 2, 5];
    for (let exp = 0; exp <= 6; exp++) {
        const base = Math.pow(10, exp);
        for (const mult of multipliers) {
            spacings.push(base * mult);
        }
    }
    return spacings;
}

const GRID_SPACINGS = getNiceSpacings();

// Target screen pixels between grid lines
const TARGET_MINOR_SPACING = 50;  // pixels for minor grid
const TARGET_MAJOR_SPACING = 250; // pixels for major grid

// Calculate grid opacity based on how well the spacing matches target
function calculateGridOpacity(worldSpacing, targetScreenSpacing) {
    const screenSpacing = worldSpacing * camera.zoom;

    // Opacity peaks when screenSpacing matches target, fades as it differs
    // Use log scale for smooth transitions
    const ratio = screenSpacing / targetScreenSpacing;

    // Fade in from 0.5x to 1x, fade out from 1x to 2x (in log space)
    const logRatio = Math.log2(ratio);

    // Peak at logRatio = 0, fade to 0 at logRatio = -1 or +1
    const opacity = Math.max(0, 1 - Math.abs(logRatio));

    return opacity;
}

// Render the grid
function renderGrid() {
    // Clear existing grid
    gridLayer.innerHTML = '';

    const width = svgWidth;
    const height = svgHeight;

    // Calculate visible world bounds, overscanned so lines whose true position is just
    // off screen but get bent inward by the warp are still drawn
    const topLeft = screenToWorld(-200, -200);
    const bottomRight = screenToWorld(width + 200, height + 200);

    // Draw grid lines for each spacing level that has non-zero opacity
    for (const spacing of GRID_SPACINGS) {
        // Calculate opacities for minor and major roles
        const minorOpacity = calculateGridOpacity(spacing, TARGET_MINOR_SPACING) * 0.15;
        const majorOpacity = calculateGridOpacity(spacing, TARGET_MAJOR_SPACING) * 0.4;

        // Use whichever role gives higher opacity
        const opacity = Math.max(minorOpacity, majorOpacity);

        if (opacity < 0.01) continue; // Skip invisible grids

        // Calculate which lines are visible
        const startX = Math.floor(topLeft.x / spacing) * spacing;
        const endX = Math.ceil(bottomRight.x / spacing) * spacing;
        const startY = Math.floor(topLeft.y / spacing) * spacing;
        const endY = Math.ceil(bottomRight.y / spacing) * spacing;

        // Create a group for this spacing level
        const group = document.createElementNS(SVG_NS, 'g');
        group.setAttribute('opacity', opacity);

        // Grid lines live at their true physical positions and bend through the space
        // warp, so compressed and stretched regions read directly off the grid.
        // Sampling is adaptive: coarse in flat space, recursively subdivided wherever
        // the warped curve pulls away from its chord — magnified zones get sub-pixel
        // resolution without paying for it in the far field.
        const refine = (x0, y0, w0, x1, y1, w1, depth, pts) => {
            const mx = (x0 + x1) / 2, my = (y0 + y1) / 2;
            const wm = warpScreenPoint(mx, my);
            const dev = Math.hypot(wm.x - (w0.x + w1.x) / 2, wm.y - (w0.y + w1.y) / 2);
            if (depth <= 0 || dev <= GRID_FLATNESS_PX) {
                pts.push(wm, w1);
                return;
            }
            refine(x0, y0, w0, mx, my, wm, depth - 1, pts);
            refine(mx, my, wm, x1, y1, w1, depth - 1, pts);
        };

        const warpedLine = (x1, y1, x2, y2) => {
            const steps = Math.max(1, Math.ceil(Math.hypot(x2 - x1, y2 - y1) / GRID_WARP_SAMPLE_PX));
            const pts = [warpScreenPoint(x1, y1)];
            let prevX = x1, prevY = y1, prevW = pts[0];
            for (let i = 1; i <= steps; i++) {
                const t = i / steps;
                const cx = x1 + (x2 - x1) * t, cy = y1 + (y2 - y1) * t;
                const cw = warpScreenPoint(cx, cy);
                refine(prevX, prevY, prevW, cx, cy, cw, GRID_SUBDIV_DEPTH, pts);
                prevX = cx; prevY = cy; prevW = cw;
            }
            let d = 'M ' + pts[0].x.toFixed(1) + ' ' + pts[0].y.toFixed(1);
            for (let i = 1; i < pts.length; i++) {
                d += ' L ' + pts[i].x.toFixed(1) + ' ' + pts[i].y.toFixed(1);
            }
            const path = document.createElementNS(SVG_NS, 'path');
            path.setAttribute('class', 'grid-line');
            path.setAttribute('fill', 'none');
            path.setAttribute('d', d);
            group.appendChild(path);
        };

        // Overscan past the viewport so lines bent inward by the warp still cover it
        const pad = 200;

        // Vertical lines
        for (let x = startX; x <= endX; x += spacing) {
            const screenX = worldToScreen(x, 0).x;
            warpedLine(screenX, -pad, screenX, height + pad);
        }

        // Horizontal lines
        for (let y = startY; y <= endY; y += spacing) {
            const screenY = worldToScreen(0, y).y;
            warpedLine(-pad, screenY, width + pad, screenY);
        }

        gridLayer.appendChild(group);
    }
}

// Render the scene
function render() {
    // Render dynamic grid
    renderGrid();

    // Update bodies
    for (const body of bodies) {
        body.updateElements();
    }

    // Update crafts
    for (const craft of squadrons) {
        craft.updateElements();
    }

    // Update info panel
    updateInfoPanel();

    // Update the transfer-drag rubber band
    updateTransferDragLine();
}

// Periodic debug logging of squadron state
let _debugLogTimer = 0;
function renderDebugOverlay() {
    _debugLogTimer++;
    if (_debugLogTimer >= 120) {
        _debugLogTimer = 0;
        for (const craft of squadrons) {
            const pos = craft.getPosition();
            const screen = worldToScreen(pos.x, pos.y);
            const hasEl = !!craft.element;
            const inDOM = !!(craft.element && craft.element.parentNode);
            const disp = craft.element ? craft.element.style.display : '?';
            console.log(`[SQ] cnt=${craft.count} el=${hasEl} dom=${inDOM} disp=${disp === '' ? 'vis' : disp} screen=(${screen.x.toFixed(0)},${screen.y.toFixed(0)}) tb=${craft.trajectoryBuffer.length} src=${craft.sourceBody?.name ?? '-'} dest=${craft.destinationBody?.name ?? '-'}`);
        }
        if (scheduledTransfers.length > 0) {
            for (const t of scheduledTransfers) {
                const sq = t.squadron;
                console.log(`[ST] ${t.sourceBody.name}→${t.destBody.name} cnt=${sq.count} frame=${sq.launchFrame} trajLen=${sq.trajectoryBuffer.length}`);
            }
        }
    }
}

// NOTE: applyTimeScrubOffset/restorePositions have been removed.
// Body/craft positioning is now unified in syncToViewFrame() — see above.

// Update info panel
function updateInfoPanel() {
    const energies = calculateEnergies();

    document.getElementById('total-energy').textContent = energies.total.toFixed(1);

    const infoDiv = document.getElementById('selected-body-info');
    const dropdown = document.getElementById('body-details-dropdown');

    // Hide body details dropdown when no body selected
    if (!selectedBody || !bodyInfoExpanded) {
        dropdown.classList.remove('expanded');
    }

    const viewFrame = Math.round(timeViewOffset);

    if (transferIsPlanning()) {
        updateTransferPanel();
        delete infoDiv.dataset.transferState;
        infoDiv.style.display = 'none';
        return;
    }

    // Clear transfer state tracking when in 'none' state
    delete infoDiv.dataset.transferState;
    delete infoDiv.dataset.countdown;
    delete infoDiv.dataset.searchProgress;
    delete infoDiv.dataset.selectedTraj;

    // Handle selected craft display
    if (selectedSquadron) {
        const craft = selectedSquadron;
        const currentCraftId = infoDiv.dataset.craftId;
        const craftId = squadrons.indexOf(craft).toString();

        // Determine craft location description
        let locationInfo = '';
        let transferInfo = '';

        {
            const destBody = craft.destinationBody;
            const fromBody = craft.launchedFromBody || craft.sourceBody;
            if (destBody) {
                const framesLeft = craft.launchFrame + craft.trajectoryBuffer.length;
                const timeToArrival = (framesLeft * PREDICTION_DT).toFixed(1);

                locationInfo = `<div class="info-row">
                    <span class="info-label">From:</span>
                    <span class="info-value">${fromBody ? fromBody.name : 'Unknown'}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">To:</span>
                    <span class="info-value">${destBody.name}</span>
                </div>`;

                if (craft.launchFrame > 0) {
                    const timeToLaunch = (craft.launchFrame * PREDICTION_DT).toFixed(1);
                    transferInfo = `<div class="info-row">
                        <span class="info-label">Launch in:</span>
                        <span class="info-value" id="craft-launch">${timeToLaunch}m</span>
                    </div>`;
                }

                transferInfo += `<div class="info-row">
                    <span class="info-label">Arrival in:</span>
                    <span class="info-value" id="craft-arrival">${timeToArrival}m</span>
                </div>`;

                // Time to correction (if applicable)
                if (craft.correctionParams && craft.correctionParams.duration > 0) {
                    const correctionStart = craft.correctionParams.startFrame;
                    const correctionEnd = correctionStart + craft.correctionParams.duration;

                    if (craft.flightFrame < correctionStart) {
                        const framesToCorrection = correctionStart - craft.flightFrame;
                        const timeToCorrection = (framesToCorrection * PREDICTION_DT).toFixed(1);
                        transferInfo += `<div class="info-row">
                            <span class="info-label">Correction in:</span>
                            <span class="info-value" id="craft-correction">${timeToCorrection}m</span>
                        </div>`;
                    } else if (craft.flightFrame < correctionEnd) {
                        const framesRemaining = correctionEnd - craft.flightFrame;
                        const timeRemaining = (framesRemaining * PREDICTION_DT).toFixed(1);
                        transferInfo += `<div class="info-row">
                            <span class="info-label">Correcting:</span>
                            <span class="info-value" id="craft-correction" style="color: red;">${timeRemaining}m left</span>
                        </div>`;
                    }
                }
            } else {
                // Free flight without destination (regular launch)
                locationInfo = `<div class="info-row">
                    <span class="info-label">Status:</span>
                    <span class="info-value">Free Flight</span>
                </div>`;
                if (craft.launchedFromBody) {
                    locationInfo += `<div class="info-row">
                        <span class="info-label">Launched from:</span>
                        <span class="info-value">${craft.launchedFromBody.name}</span>
                    </div>`;
                }
            }
        }

        // Only rebuild if craft changed, phase changed, or launch status changed
        const currentCraftState = infoDiv.dataset.craftState;
        const craftPhase = craft.destinationBody ? 'transfer' : 'free';
        const pendingKey = craft.launchFrame > 0 ? 'pending' : 'launched';
        if (currentCraftId !== craftId || currentCraftState !== craftPhase || infoDiv.dataset.pendingKey !== pendingKey) {
            const squadLabel = craft.count > 1 ? `Squadron (${craft.count})` : 'Craft';
            infoDiv.innerHTML = `
                <h3>${squadLabel}</h3>
                ${locationInfo}
                ${transferInfo}
                <div class="info-row">
                    <span class="info-label">Position:</span>
                    <span class="info-value" id="craft-position">(${craft.getPosition().x.toFixed(0)}, ${craft.getPosition().y.toFixed(0)})</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Speed:</span>
                    <span class="info-value" id="craft-speed">${craft.getSpeed().toFixed(1)}</span>
                </div>
            `;
            infoDiv.dataset.craftId = craftId;
            infoDiv.dataset.craftState = craftPhase;
            infoDiv.dataset.pendingKey = pendingKey;
            delete infoDiv.dataset.bodyName;
        } else {
            // Just update dynamic values
            const posEl = document.getElementById('craft-position');
            const speedEl = document.getElementById('craft-speed');
            const arrivalEl = document.getElementById('craft-arrival');
            const correctionEl = document.getElementById('craft-correction');

            if (posEl) {
                const pos = craft.getPosition();
                posEl.textContent = `(${pos.x.toFixed(0)}, ${pos.y.toFixed(0)})`;
            }
            if (speedEl) speedEl.textContent = craft.getSpeed().toFixed(1);

            const launchEl = document.getElementById('craft-launch');
            if (launchEl && craft.launchFrame > 0) {
                launchEl.textContent = (craft.launchFrame * PREDICTION_DT).toFixed(1) + 'm';
            }

            if (arrivalEl && craft.destinationBody) {
                const framesLeft = craft.launchFrame + craft.trajectoryBuffer.length;
                const timeToArrival = (framesLeft * PREDICTION_DT).toFixed(1);
                arrivalEl.textContent = timeToArrival + 'm';
            }

            if (correctionEl && craft.correctionParams) {
                const correctionStart = craft.correctionParams.startFrame;
                const correctionEnd = correctionStart + craft.correctionParams.duration;

                if (craft.flightFrame < correctionStart) {
                    const framesToCorrection = correctionStart - craft.flightFrame;
                    const timeToCorrection = (framesToCorrection * PREDICTION_DT).toFixed(1);
                    correctionEl.textContent = timeToCorrection + 'm';
                    correctionEl.style.color = '';
                } else if (craft.flightFrame < correctionEnd) {
                    const framesRemaining = correctionEnd - craft.flightFrame;
                    const timeRemaining = (framesRemaining * PREDICTION_DT).toFixed(1);
                    correctionEl.textContent = timeRemaining + 'm left';
                    correctionEl.style.color = 'red';
                }
            }
        }
        infoDiv.style.display = 'block';
        return;
    }

    // Clear craft tracking when showing body info
    delete infoDiv.dataset.craftId;
    delete infoDiv.dataset.craftState;

    if (selectedBody) {
        // Calculate effective craft count at this body at the viewed frame
        let effectiveCraftCount = getEffectiveCraftAtBody(selectedBody, viewFrame);

        // Check if we need to rebuild the panel structure
        const currentBodyName = infoDiv.dataset.bodyName;
        const currentCraftCount = parseInt(infoDiv.dataset.craftCount || '0', 10);
        const bufferReady = predictionBuffer.length >= PREDICTION_FRAMES;
        const currentBufferReady = infoDiv.dataset.bufferReady === 'true';
        // Whether a drag would actually do anything. The same question the number
        // above answers — see bodyDisplayCraftCount — so the panel never shows a
        // count it will not then let the player act on.
        const canSend = bodyCanSend(selectedBody);
        const currentCanSend = infoDiv.dataset.canSend === 'true';
        const needsRebuild = currentBodyName !== selectedBody.name
            || currentCraftCount !== effectiveCraftCount
            || currentBufferReady !== bufferReady
            || currentCanSend !== canSend;

        if (needsRebuild) {
            let craftHtml = `<div class="info-row">
                <span class="info-label">Craft:</span>
                <span class="info-value" id="craft-count-display">${effectiveCraftCount}</span>
                <button id="build-craft-btn" title="Build craft">+ Build</button>
            </div>`;

            // There is no Transfer button any more — the gesture IS the control,
            // so the panel teaches it instead of duplicating it. The hint appears
            // only when the gesture would work, so it never promises nothing.
            if (canSend && bufferReady) {
                craftHtml += `<div id="transfer-hint">Drag to another body to plan a transfer</div>`;
            } else if (canSend) {
                const progress = Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100);
                craftHtml += `<div id="transfer-hint" class="waiting">Propagating — ${progress}%</div>`;
            }

            const lore = planetLore[selectedBody.name];
            infoDiv.innerHTML = `
                <h3><span class="body-indicator" style="background-color: ${selectedBody.color}"></span>${selectedBody.name}</h3>
                ${craftHtml}
                ${lore ? `<div id="body-lore">${lore.desc}</div>` : ''}
            `;
            dropdown.innerHTML = `
                <div class="info-row">
                    <span class="info-label">Mass:</span>
                    <span class="info-value" id="info-mass">${selectedBody.mass.toFixed(1)}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Radius:</span>
                    <span class="info-value" id="info-radius">${selectedBody.radius.toFixed(1)}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Position:</span>
                    <span class="info-value" id="info-position">(${selectedBody.x.toFixed(0)}, ${selectedBody.y.toFixed(0)})</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Speed:</span>
                    <span class="info-value" id="info-speed">${selectedBody.speed.toFixed(1)}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Kinetic E:</span>
                    <span class="info-value" id="info-kinetic">${selectedBody.kineticEnergy.toFixed(1)}</span>
                </div>
            `;
            dropdown.classList.toggle('expanded', bodyInfoExpanded);
            infoDiv.dataset.bodyName = selectedBody.name;
            infoDiv.dataset.craftCount = effectiveCraftCount;
            infoDiv.dataset.bufferReady = bufferReady;
            infoDiv.dataset.canSend = canSend;
        } else {
            // Just update the dynamic values without rebuilding
            const posEl = document.getElementById('info-position');
            const speedEl = document.getElementById('info-speed');
            const kineticEl = document.getElementById('info-kinetic');
            if (posEl) posEl.textContent = `(${selectedBody.x.toFixed(0)}, ${selectedBody.y.toFixed(0)})`;
            if (speedEl) speedEl.textContent = selectedBody.speed.toFixed(1);
            if (kineticEl) kineticEl.textContent = selectedBody.kineticEnergy.toFixed(1);

            // Update craft count display
            const countEl = document.getElementById('craft-count-display');
            if (countEl) countEl.textContent = effectiveCraftCount;

            // Keep the propagation countdown live while the buffer fills
            if (canSend && !bufferReady) {
                const hint = document.getElementById('transfer-hint');
                if (hint) {
                    const progress = Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100);
                    hint.textContent = `Propagating — ${progress}%`;
                }
            }
        }
        infoDiv.style.display = 'block';
    } else {
        // Nothing selected: the map itself is the menu, so there is no panel
        // to show. Selecting is done by tapping a body, planning a transfer by
        // dragging between two.
        infoDiv.style.display = 'none';
        delete infoDiv.dataset.bodyName;
        delete infoDiv.dataset.craftCount;
    }
}

// Find body at screen position
function findBodyAtPosition(screenX, screenY) {
    // Hit-test in screen space against the drawn radius, since that is what the player
    // sees and aims at. Exaggerated bodies can overlap each other when zoomed out, so
    // pick the one whose centre is nearest the tap rather than the first in the list.
    let best = null;
    let bestDist = Infinity;

    for (const body of bodies) {
        const screen = bodyScreenPos(body);
        const dx = screenX - screen.x;
        const dy = screenY - screen.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist <= bodyTapRadius(body) && dist < bestDist) {
            best = body;
            bestDist = dist;
        }
    }

    return best;
}

// Find craft at screen position (for craft selection)
//
// Against the rocket as drawn, which is bigger than the dot it replaced — and only for
// squadrons actually on the map at the viewed moment. One that has arrived is part of a
// body's total by then and has nothing to hit; one still waiting at its origin is handled
// by pendingRocketAt, which has to argue with the body underneath it first.
function findCraftAtPosition(screenX, screenY) {
    const clickRadius = ROCKET_LENGTH_PX * 0.7;

    for (const craft of squadrons) {
        if (craft._displayPhase !== 'flight') continue;
        if (craft._displayCount !== undefined && craft._displayCount <= 0) continue;

        const pos = squadronScreenPos(craft);
        if (Math.hypot(screenX - pos.x, screenY - pos.y) <= clickRadius) return craft;
    }

    return null;
}

function selectBody(body) {
    selectedBody = body;          // null means deselect
    selectedSquadron = null;
    isTrackingSelectedSquadron = false;
}

// Apply a clean tap/click at a screen point — the single place map selection is
// decided, shared by mouse and touch so both agree on what a tap means.
//
// Only called once the pointer has come back up having barely moved. A press that
// turns into a drag pans instead and selects nothing, so the player can always
// grab empty space *or* a body to move the view around.
function selectAtPoint(x, y, clientX, clientY) {
    // A launch that has not gone yet is the one thing that beats the body under it, and
    // only where the tap is genuinely nearer the rocket than the planet. Tapping it
    // reopens the launch controls, which is the only way back into a decision already
    // made — see openScheduledTransfer.
    const pending = pendingRocketAt(x, y);
    if (pending && openScheduledTransfer(pending)) return;

    // Otherwise bodies win. Craft and trajectories crowd around the body they came from,
    // and if those took precedence you could no longer tap the body to send more.
    const body = findBodyAtPosition(x, y);
    if (body) {
        selectBody(body);
        return;
    }

    // Out in open space, a rocket or the trajectory stroke under the point selects that
    // squadron. The stroke needs DOM hit-testing: it is a thin drawn path rather than
    // something with a position to measure against.
    const hit = document.elementFromPoint(clientX, clientY);
    const onTrajectory = hit && hit._craft ? hit._craft : null;
    const craft = findCraftAtPosition(x, y) || onTrajectory;
    if (craft) {
        // Its path counts as it: the whole line out from the origin belongs to a launch
        // that has not happened, and touching any of it is asking about that launch.
        if (craft.launchFrame > 0 && openScheduledTransfer(craft)) return;
        selectedSquadron = craft;
        selectedBody = null;
        isTrackingSelectedSquadron = true;
        return;
    }

    selectBody(null);   // tapped empty sky
}

// ===== Transfer drag gesture =====
//
// The map is the transfer picker: drag from a body you have craft on to the body
// you want them at, and release. There is no separate list of origins and
// destinations — the thing you point at IS the choice.
//
// Selection is the gate, and holding is how you reach it mid-gesture:
//
//   press-and-hold a body  -> it SELECTS under your finger, before you lift
//   keep dragging from there -> the transfer band follows, if it has craft
//   release on another body  -> that pair goes to the launch-window search
//
// so the whole thing is one uninterrupted press. Dragging off a body that is not
// selected pans instead, which is what keeps the map draggable everywhere: the
// gate is deliberate commitment, not merely landing on a planet.
//
// A selected body with no craft also pans, because there is nothing to send.
//
// Once a transfer is being planned there is a third thing a press can mean: picking a
// route from the fan drawn across the map. That takes precedence over bodies lying under
// the curves, with the selected source as the one exception — see pressOnMap.

// Whether a drag off this body starts a transfer or pans the map.
//
// Asks the same question the number beside the body answers, at the same moment: a body
// showing craft must be draggable. Reading body.craftCount instead meant a fleet that had
// just landed — visibly parked at its destination, but not yet arrived in the *present*,
// because the player had run the clock forward to watch it get there — could not be sent
// on. The map said five craft and the gesture said none.
function bodyCanSend(body) {
    return !!body && getSendableCraftAtBody(body) > 0;
}

function cancelTransferHold() {
    if (transferHoldTimer !== null) {
        clearTimeout(transferHoldTimer);
        transferHoldTimer = null;
    }
}

// Bodies you may drop on: not the source, and not the star, since a transfer into
// the star is not a trip anyone takes.
function transferTargetAt(x, y, source) {
    const body = findBodyAtPosition(x, y);
    if (!body || body === source || body.isStar) return null;
    return body;
}

// Open the transfer picker for a pair: scan the release circle at the moment on the
// clock and fan the results across the map.
function beginTransferBetween(source, dest) {
    if (!bodyCanSend(source)) return;

    transferSourceBody = source;
    transferDestinationBody = dest;
    selectBody(source);
    startTransferSearch();
}

// --- One press, shared by mouse and touch so the two cannot drift apart ---

function pressOnMap(x, y) {
    isDragging = true;
    dragStart = { x, y };
    cameraStart = { x: camera.x, y: camera.y };
    transferDrag = null;
    fanDrag = false;
    fanDragBody = null;
    cancelTransferHold();

    const body = findBodyAtPosition(x, y);

    // Landing on the fan picks a route, and the fan wins over a body merely in the way.
    //
    // Bodies-win is the rule everywhere else, and it is wrong here: the routes loop
    // right around the system, so on a small screen a curve reliably passes under some
    // moon's tap radius, and honouring the body there turned a sweep into a pan for no
    // reason the player could see. The one body that still wins is the selected source,
    // because dragging off it is how you re-aim the transfer — and every curve starts
    // there, so the fan would otherwise swallow that gesture completely. A plain tap on
    // any other body still selects it; releaseOnMap sorts that out on the way up.
    const bodyOwnsPress = body && body === selectedBody && bodyCanSend(body);

    if (!bodyOwnsPress && transferFan.length > 0) {
        const hit = fanEntryAt(x, y);
        if (hit >= 0) {
            fanDrag = true;
            fanDragBody = body;
            fanHighlight = hit;
            fanPointer = { x, y };
            updateTransferPanel();
            return;
        }
    }

    if (!body) return;

    if (body === selectedBody) {
        // Already committed to this one, so a drag off it means the transfer.
        if (bodyCanSend(body)) transferDrag = { source: body, x, y, target: null };
        return;
    }

    // Not selected yet. Hold still and it selects under the finger — visibly,
    // before you lift — which arms the same drag without ever releasing. Any
    // body selects this way; only one with craft also arms the band.
    transferHoldTimer = setTimeout(() => {
        transferHoldTimer = null;
        selectBody(body);
        if (bodyCanSend(body)) transferDrag = { source: body, x, y, target: null };
    }, TRANSFER_HOLD_MS);
}

// True when the move belongs to a transfer drag or a sweep across the fan, neither of
// which may pan the view.
function moveOnMap(x, y) {
    if (fanDrag) {
        fanPointer = { x, y };
        // Sustain radius, not the pick radius. Getting onto a curve should take aim, but
        // once you are sweeping the highlight has to keep up across the gaps between
        // them, or it would drop out every time the finger crossed open space.
        const hit = fanEntryAt(x, y, FAN_PICK_RADIUS_PX * 3);
        if (hit >= 0 && hit !== fanHighlight) {
            fanHighlight = hit;
            updateTransferPanel();
        }
        return true;
    }

    if (!transferDrag) return false;
    transferDrag.x = x;
    transferDrag.y = y;
    transferDrag.target = transferTargetAt(x, y, transferDrag.source);
    return true;
}

// Drop a press without acting on it — the pointer left the map, or the system
// took the gesture. Leaving transferDrag set would strand a rubber band on screen,
// and a live hold timer would select a body long after the finger was gone.
function abandonGesture() {
    cancelTransferHold();
    transferDrag = null;
    fanDrag = false;
    fanDragBody = null;
    fanPointer = null;
    isDragging = false;
}

// Settle a press that has come back up. `moved` is how far it travelled, `slop`
// the distance below which this still counts as a tap rather than a drag.
function releaseOnMap(x, y, clientX, clientY, moved, slop) {
    cancelTransferHold();

    if (fanDrag) {
        const overBody = fanDragBody;
        fanDrag = false;
        fanDragBody = null;
        fanPointer = null;

        // A press that never went anywhere, on a body that happened to lie under a
        // curve, was a tap on that body — not a route pick. This is what lets you still
        // reach a planet to re-aim the transfer even where the fan covers it.
        if (moved < slop && overBody) {
            selectAtPoint(x, y, clientX, clientY);
            return;
        }

        // Otherwise the highlight stays where the finger left it — that is the choice.
        // Only the pointer is dropped, which parks the duration label back at the middle
        // of the chosen curve instead of under a finger that is no longer there.
        updateTransferPanel();
        return;
    }

    if (transferDrag) {
        const { source, target } = transferDrag;
        transferDrag = null;
        if (target) {
            beginTransferBetween(source, target);
        } else if (moved < slop) {
            // Armed but never went anywhere — that is just a tap.
            selectAtPoint(x, y, clientX, clientY);
        }
        // Dragged out and dropped on nothing: cancelled. The view never moved,
        // so there is nothing to pause or restore.
        return;
    }

    if (moved < slop) {
        selectAtPoint(x, y, clientX, clientY);
    } else {
        // User actually panned - pause auto-fit, leave the selection alone
        userMovedTheView();
        isTrackingSelectedSquadron = false;
    }
}

// Event handlers
function handleMouseMove(e) {
    const rect = svg.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    if (isDragging) {
        if (moveOnMap(x, y)) { svg.style.cursor = 'grabbing'; return; }

        // Pan the camera, but only once past the slop — see handleTouchMove
        const dx = x - dragStart.x;
        const dy = y - dragStart.y;
        if (Math.sqrt(dx * dx + dy * dy) < CLICK_SLOP_PX) return;

        cancelTransferHold();   // moved too far to still be a press-and-hold
        camera.x = cameraStart.x - dx / camera.zoom;
        camera.y = cameraStart.y - dy / camera.zoom;
        svg.style.cursor = 'grabbing';
    } else {
        hoveredBody = findBodyAtPosition(x, y);
        svg.style.cursor = hoveredBody ? 'pointer' : 'grab';
    }
}

function handleMouseDown(e) {
    const rect = svg.getBoundingClientRect();
    // Always arm a drag, bodies included — pressing on a body is how you grab the
    // view in a crowded system. handleMouseUp decides whether it was a click.
    pressOnMap(e.clientX - rect.left, e.clientY - rect.top);
    svg.style.cursor = 'grabbing';
}

function handleMouseUp(e) {
    const rect = svg.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    if (isDragging) {
        const dx = x - dragStart.x;
        const dy = y - dragStart.y;
        releaseOnMap(x, y, e.clientX, e.clientY, Math.sqrt(dx * dx + dy * dy), CLICK_SLOP_PX);
    }

    isDragging = false;
    svg.style.cursor = hoveredBody ? 'pointer' : 'grab';
}

function handleWheel(e) {
    e.preventDefault();

    // User manually zooming - pause auto-fit and stop tracking
    userMovedTheView();
    isTrackingSelectedSquadron = false;

    const rect = svg.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;

    // Get world position under mouse before zoom
    const worldBefore = screenToWorld(mouseX, mouseY);

    // Calculate new zoom level - normalize deltaY for trackpad vs mouse wheel
    const normalizedDelta = Math.sign(e.deltaY) * Math.min(Math.abs(e.deltaY), 10);
    const zoomFactor = 1 - normalizedDelta * 0.002;
    camera.zoom = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, camera.zoom * zoomFactor));

    // Get world position under mouse after zoom
    const worldAfter = screenToWorld(mouseX, mouseY);

    // Adjust camera to keep mouse position fixed in world space
    camera.x += worldBefore.x - worldAfter.x;
    camera.y += worldBefore.y - worldAfter.y;
}

// Touch event helpers
function getTouchDistance(touches) {
    const dx = touches[0].clientX - touches[1].clientX;
    const dy = touches[0].clientY - touches[1].clientY;
    return Math.sqrt(dx * dx + dy * dy);
}

function getTouchCenter(touches, rect) {
    return {
        x: (touches[0].clientX + touches[1].clientX) / 2 - rect.left,
        y: (touches[0].clientY + touches[1].clientY) / 2 - rect.top
    };
}

function handleTouchStart(e) {
    e.preventDefault();
    const rect = svg.getBoundingClientRect();
    const touches = e.touches;

    if (touches.length === 1) {
        // Single touch - arm a drag wherever it landed, bodies included. Whether
        // this turns out to be a tap or a pan is settled in handleTouchEnd.
        const x = touches[0].clientX - rect.left;
        const y = touches[0].clientY - rect.top;

        pressOnMap(x, y);

        touchState.active = true;
        touchState.lastTouches = [{ x, y }];
    } else if (touches.length === 2) {
        // Two finger touch - a pinch is never a tap or a transfer drag
        isDragging = false;
        transferDrag = null;
        cancelTransferHold();
        touchState.active = true;
        touchState.lastPinchDist = getTouchDistance(touches);
        touchState.lastPinchCenter = getTouchCenter(touches, rect);
        cameraStart = { x: camera.x, y: camera.y };
    }
}

function handleTouchMove(e) {
    e.preventDefault();
    if (!touchState.active) return;

    const rect = svg.getBoundingClientRect();
    const touches = e.touches;

    if (touches.length === 1 && isDragging) {
        // Single touch pan
        const x = touches[0].clientX - rect.left;
        const y = touches[0].clientY - rect.top;

        if (moveOnMap(x, y)) return;   // dragging a transfer, not the view

        const dx = x - dragStart.x;
        const dy = y - dragStart.y;
        // Inside the slop this is still a candidate tap: don't move the view and
        // don't stop auto-fit, or a finger that rolls a pixel would cancel the fit
        // every time the player taps empty space to deselect.
        if (Math.sqrt(dx * dx + dy * dy) < TAP_SLOP_PX) return;

        cancelTransferHold();   // moved too far to still be a press-and-hold
        camera.x = cameraStart.x - dx / camera.zoom;
        camera.y = cameraStart.y - dy / camera.zoom;

        // User manually panning - pause auto-fit
        userMovedTheView();
    } else if (touches.length === 2) {
        // Pinch zoom
        const newDist = getTouchDistance(touches);
        const newCenter = getTouchCenter(touches, rect);

        if (touchState.lastPinchDist > 0) {
            // Get world position at pinch center before zoom
            const worldBefore = screenToWorld(newCenter.x, newCenter.y);

            // Calculate zoom change
            const scale = newDist / touchState.lastPinchDist;
            camera.zoom = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, camera.zoom * scale));

            // Get world position at pinch center after zoom
            const worldAfter = screenToWorld(newCenter.x, newCenter.y);

            // Adjust camera to keep pinch center fixed in world space
            camera.x += worldBefore.x - worldAfter.x;
            camera.y += worldBefore.y - worldAfter.y;

            // User manually zooming - pause auto-fit
            userMovedTheView();
        }

        touchState.lastPinchDist = newDist;
        touchState.lastPinchCenter = newCenter;
    }
}

function handleTouchEnd(e) {
    e.preventDefault();
    const rect = svg.getBoundingClientRect();

    if (e.touches.length === 0) {
        // All fingers lifted
        if (isDragging && touchState.lastTouches.length === 1) {
            // Check if this was a tap (minimal movement)
            const endTouch = e.changedTouches[0];
            const endX = endTouch.clientX - rect.left;
            const endY = endTouch.clientY - rect.top;
            const startTouch = touchState.lastTouches[0];
            const dx = endX - startTouch.x;
            const dy = endY - startTouch.y;
            const moved = Math.sqrt(dx * dx + dy * dy);

            releaseOnMap(endX, endY, endTouch.clientX, endTouch.clientY, moved, TAP_SLOP_PX);
        }

        cancelTransferHold();
        transferDrag = null;
        isDragging = false;
        touchState.active = false;
        touchState.lastTouches = [];
        touchState.lastPinchDist = 0;
    } else if (e.touches.length === 1) {
        // Went from 2 fingers to 1 - switch to pan mode
        const x = e.touches[0].clientX - rect.left;
        const y = e.touches[0].clientY - rect.top;
        isDragging = true;
        dragStart = { x, y };
        cameraStart = { x: camera.x, y: camera.y };
        touchState.lastTouches = [{ x, y }];
        touchState.lastPinchDist = 0;
    }
}

// Calculate bounding box of all bodies and their predicted trajectories
function calculateBoundingBox() {
    if (bodies.length === 0) return { minX: 0, maxX: 0, minY: 0, maxY: 0 };

    let minX = Infinity, maxX = -Infinity;
    let minY = Infinity, maxY = -Infinity;

    // Include current body positions with radii
    for (const body of bodies) {
        minX = Math.min(minX, body.x - body.radius);
        maxX = Math.max(maxX, body.x + body.radius);
        minY = Math.min(minY, body.y - body.radius);
        maxY = Math.max(maxY, body.y + body.radius);
    }

    // Include downsampled trajectory points with body radii
    if (predictionBuffer.length > 0) {
        for (let bodyIndex = 0; bodyIndex < bodies.length; bodyIndex++) {
            const radius = bodies[bodyIndex].radius;

            // Always include first point if not selected by sampling
            if (sampleOffset !== 0) {
                const state = predictionBuffer[0][bodyIndex];
                minX = Math.min(minX, state.x - radius);
                maxX = Math.max(maxX, state.x + radius);
                minY = Math.min(minY, state.y - radius);
                maxY = Math.max(maxY, state.y + radius);
            }

            // Include downsampled points
            for (let i = sampleOffset; i < predictionBuffer.length; i += SAMPLE_INTERVAL) {
                const state = predictionBuffer[i][bodyIndex];
                minX = Math.min(minX, state.x - radius);
                maxX = Math.max(maxX, state.x + radius);
                minY = Math.min(minY, state.y - radius);
                maxY = Math.max(maxY, state.y + radius);
            }

            // Always include last point if not already included
            const lastFrame = predictionBuffer.length - 1;
            const lastSampledFrame = sampleOffset + Math.floor((lastFrame - sampleOffset) / SAMPLE_INTERVAL) * SAMPLE_INTERVAL;
            if (lastFrame !== lastSampledFrame) {
                const state = predictionBuffer[lastFrame][bodyIndex];
                minX = Math.min(minX, state.x - radius);
                maxX = Math.max(maxX, state.x + radius);
                minY = Math.min(minY, state.y - radius);
                maxY = Math.max(maxY, state.y + radius);
            }
        }
    }

    return { minX, maxX, minY, maxY };
}

// Fit camera to show all bodies with margin
const FIT_SOLVE_EVERY = 4;   // frames between full zoom/knob solves (recentre is per-frame)
let fitSolveCounter = 0;
let fitSolveState = null;    // {zT, gapT} glide targets held between solves
function fitAllBodies() {
    const rect = svg.getBoundingClientRect();
    const bbox = calculateBoundingBox();

    // Calculate center of bounding box
    const centerX = (bbox.minX + bbox.maxX) / 2;
    const centerY = (bbox.minY + bbox.maxY) / 2;

    const edgePad = 26; // screen px kept clear around the drawn discs (labels)
    const availWidth = Math.max(50, rect.width - edgePad * 2);
    const availHeight = Math.max(50, rect.height - edgePad * 2);

    camera.x = centerX;
    camera.y = centerY;

    // Measure, at the current zoom, the screen bbox of everything that should stay in
    // view: the drawn discs (layout positions + exaggerated radii) unioned with the
    // unwarped orbital sweep (so the fit view still holds the full orbit rings steady
    // instead of chasing the planets around them).
    const measure = () => {
        const entries = getDisplayLayout().entries;
        let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
        for (const e of entries) {
            minX = Math.min(minX, e.qx - e.drawnR);
            maxX = Math.max(maxX, e.qx + e.drawnR);
            minY = Math.min(minY, e.qy - e.drawnR);
            maxY = Math.max(maxY, e.qy + e.drawnR);
        }
        const tl = worldToScreen(bbox.minX, bbox.minY);
        const br = worldToScreen(bbox.maxX, bbox.maxY);
        minX = Math.min(minX, tl.x); maxX = Math.max(maxX, br.x);
        minY = Math.min(minY, tl.y); maxY = Math.max(maxY, br.y);
        return { minX, maxX, minY, maxY,
                 over: Math.max((maxX - minX) / availWidth, (maxY - minY) / availHeight) };
    };

    // The span/avail ratio is NOT monotone in zoom: drawn sizes and gaps are fixed
    // pixels, and at very low zoom the star's magnification bump dominates the span,
    // so span grows as zoom shrinks and a naive fixed-point iteration runs away to
    // MIN_ZOOM. Instead scan zoom candidates from high to low and take the largest
    // zoom that fits, log-interpolating at the crossing so the result moves smoothly
    // as the bodies orbit.
    const SCAN_STEPS = 32;
    const scan = (prefZ) => {
        // Sample over(z) top-down and collect every contiguous fitting run with its
        // upper crossing (log-interpolated); several runs can exist because span is
        // not monotone in zoom.
        const runs = [];
        let bestZ = MIN_ZOOM, bestOver = Infinity;
        let prevZ = null, prevOver = null, run = null;
        for (let i = SCAN_STEPS; i >= 0; i--) {
            const z = MIN_ZOOM * Math.pow(MAX_ZOOM / MIN_ZOOM, i / SCAN_STEPS);
            camera.zoom = z;
            const over = measure().over;
            if (over < bestOver) { bestOver = over; bestZ = z; }
            if (over <= 1) {
                if (!run) {
                    const top = (prevOver !== null && prevOver > 1)
                        ? z * Math.pow(prevZ / z, (1 - over) / (prevOver - over))
                        : z;
                    run = { top, bottom: z, over };
                } else run.bottom = z;
            } else if (run) { runs.push(run); run = null; }
            prevZ = z; prevOver = over;
        }
        if (run) runs.push(run);
        if (!runs.length) return { z: bestZ, over: bestOver };
        // Prefer the run the previous solve lives in (else the nearest run): the
        // fitting set has multiple branches, and hopping to a distant one because
        // it is marginally "larger" teleports the whole view between frames.
        let pick = runs[0];
        if (prefZ) {
            const slack = Math.log(MAX_ZOOM / MIN_ZOOM) / SCAN_STEPS;
            const p = Math.log(prefZ);
            let bestD = Infinity;
            for (const r of runs) {
                const lo = Math.log(r.bottom) - slack, hi = Math.log(r.top) + slack;
                const d = p < lo ? lo - p : p > hi ? p - hi : 0;
                if (d < bestD) { bestD = d; pick = r; }
            }
        }
        return { z: pick.top, over: pick.over };
    };

    // Seven discs plus six full gaps can be wider than a phone when the system lines
    // up along one axis, and no zoom fixes that (the schematic span is fixed pixels).
    // Body sizes are non-negotiable; the gap and the schematic spread are not. Squeeze
    // the gap first, then compress the schematic toward its centroid, each only as far
    // as the current alignment demands. Both knobs return to 1 the moment they fit.
    const solveKnob = (set, prefZ) => {
        // Binary-search the largest knob value in [0, 1] whose best zoom fits;
        // assumes 0 fits (caller checked). Returns the scan result at the answer.
        let lo = 0, r = scan(prefZ);
        for (let k = 0, hi = 1; k < 6; k++) {
            const mid = (lo + hi) / 2;
            set(mid);
            const rm = scan(prefZ);
            if (rm.over <= 1) { lo = mid; r = rm; } else hi = mid;
        }
        set(lo);
        return r;
    };

    // The zoom/knob solve is the expensive part and its inputs (body positions)
    // barely move between frames, so re-solve on a cadence — and treat the answer
    // as a TARGET to glide toward, never a value to snap to. Snapping (or holding
    // a stale solve and then jumping at the cadence boundary) is exactly the kind
    // of frame-to-frame teleport this display is trying to eliminate.
    fitSolveCounter++;
    const firstSolve = !fitSolveState;
    if (firstSolve || fitSolveCounter % FIT_SOLVE_EVERY === 0) {
        const prefZ = fitSolveState ? fitSolveState.zT : null;
        const easedZ = camera.zoom, easedGap = displayGapScale;
        displayGapScale = 1;
        let r = scan(prefZ);
        if (r.over > 1) {
            displayGapScale = 0;
            const r0 = scan(prefZ);
            r = r0.over <= 1
                ? solveKnob(v => { displayGapScale = v; }, prefZ)
                : r0; // beyond help (discs alone exceed the screen); least overflow
        }
        fitSolveState = { zT: Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, r.z)), gapT: displayGapScale };
        // The scans trampled the live knobs; restore the eased values (or, on the
        // very first solve, adopt the target outright)
        camera.zoom = firstSolve ? fitSolveState.zT : easedZ;
        displayGapScale = firstSolve ? fitSolveState.gapT : easedGap;
    }
    const FIT_EASE = 0.22; // per-frame fraction of the remaining (log-)distance
    camera.zoom = Math.exp(Math.log(camera.zoom)
        + (Math.log(fitSolveState.zT) - Math.log(camera.zoom)) * FIT_EASE);
    displayGapScale += (fitSolveState.gapT - displayGapScale) * FIT_EASE;

    // Layout is translation-equivariant, so one recentring lands exactly.
    const m = measure();
    camera.x += ((m.minX + m.maxX) / 2 - rect.width / 2) / camera.zoom;
    camera.y += ((m.minY + m.maxY) / 2 - rect.height / 2) / camera.zoom;
}

// The player has moved the view by hand. Every automatic framing lets go — including the
// transfer fit, for the rest of this transfer: a camera that argued with a pinch would read
// as the map refusing to be moved.
function userMovedTheView() {
    isAutoFitPaused = true;
    transferViewReleased = true;
    viewRestore = null;   // wherever they have just put it is now the view worth keeping
}

// Reset auto-fit (called by Escape or Fit All button)
function resetAutoFit() {
    isAutoFitPaused = false;
    // Asking for the whole system is asking for something other than the route being
    // planned, so the transfer fit lets go too — otherwise it would take the view straight
    // back and the key would look dead.
    transferViewReleased = true;
    isTrackingSelectedSquadron = false;
    selectedBody = null;
    selectedSquadron = null;
}

// Update camera to track the selected craft, or fit all
//
// Selecting a *body* deliberately moves nothing. It still stops auto-fit (the
// condition below sees selectedBody), so the view holds wherever the player left
// it and the body they tapped stays where they were already looking at it.
function updateCameraTracking() {
    if (isDragging) return;

    if (transferIsPlanning() && !transferViewReleased) {
        // Planning owns the view outright: the route being weighed up is the only thing
        // on screen that matters, and it outranks both the selection (the source body is
        // selected, which would otherwise freeze the camera) and auto-fit.
        fitTransferSelection();
    } else if (selectedSquadron && isTrackingSelectedSquadron && selectedSquadron.state === 'free') {
        // Track selected craft - fit to trajectory and destination
        fitCraftTrajectory(selectedSquadron);
    } else if (!selectedBody && !selectedSquadron && !isAutoFitPaused) {
        // Auto-fit all bodies when nothing selected. It is already putting the whole system
        // back, which is a better answer than the exact view the transfer borrowed.
        viewRestore = null;
        fitAllBodies();
    } else if (viewRestore) {
        // Nothing else wants the camera, and a transfer left it somewhere the player did
        // not put it. Hand it back.
        if (easeCameraToward(viewRestore)) viewRestore = null;
    }

    // Outside auto-fit, ease the fit's gap squeeze back out to the full gap —
    // an instant reset would jump the layout the moment auto-fit stops
    if ((selectedBody || selectedSquadron || isAutoFitPaused) && displayGapScale < 1) {
        displayGapScale += (1 - displayGapScale) * 0.08;
        if (displayGapScale > 0.999) displayGapScale = 1;
    }

    // Update Fit All badge/item active state - active when auto-fitting (no body selected and not paused)
    const isAutoFitActive = !selectedBody && !selectedSquadron && !isAutoFitPaused;
    const fitAllItem = document.getElementById('fit-all-item');
    const fitAllBadge = document.getElementById('fit-all-badge');
    if (fitAllItem) fitAllItem.classList.toggle('active', isAutoFitActive);
    if (fitAllBadge) fitAllBadge.classList.toggle('hidden', !isAutoFitActive);
}

// --- Choosing a transfer, at true scale ------------------------------------------
//
// Planning a transfer takes the view over for as long as the planning lasts: the map drops
// to true scale, and the camera frames the two bodies and whichever route is currently
// picked. Releasing hands both back.
//
// The two halves are one idea. A route is a shape — how far out it swings, how much of the
// system it crosses, where it doubles back — and the schematic layout is built to lie about
// exactly the quantities that shape is made of. Choosing between routes is the one moment in
// the game when what the curve looks like is the whole of the decision, so it is the one
// moment worth paying the schematic's price to be honest. Framing follows from that: at true
// scale the routes are drawn at their real proportions, which is no use if half of one is
// off the edge of the screen.
//
// It reverts on its own because true scale is not a good map to play on — bodies go
// sub-pixel and the system is mostly empty — and a mode the player did not ask to enter
// should not be a mode they have to notice and leave.
//
// The camera holds still for the whole of a sweep across the fan and re-frames when the
// finger lifts. This is not an oversight and it is not laziness — it is the one place the
// obvious version has a feedback loop in it. Reframing on every highlight change moves the
// curves out from under the finger that is choosing between them, which changes which curve
// is nearest, which changes the highlight: sweeping across five routes flipped the pick
// nine times instead of six, alternating between two neighbours while the finger travelled
// steadily in one direction. Freezing during the gesture is also just what the gesture
// wants — while you are comparing curves the map should stop moving, and once you have
// chosen is exactly when framing the choice is worth something.

// The screen rectangle a framed route has to fit inside: the map minus the panels a transfer
// puts on top of it. Both are measured rather than assumed, because the readout wraps to a
// second line on a narrow screen and fitting a route into space that is covered would be a
// fit in name only.
function transferFitViewport() {
    const rect = svg.getBoundingClientRect();
    let top = TRANSFER_FIT_PAD_PX;
    let bottom = rect.height - TRANSFER_FIT_PAD_PX;

    for (const el of [transferReadout, transferControlsPanel]) {
        if (!el || el.offsetParent === null) continue;
        const r = el.getBoundingClientRect();
        const t = r.top - rect.top, b = r.bottom - rect.top;
        // Which edge a panel pushes in from is read off where it sits, not hardcoded:
        // whichever half of the map holds its middle is the side it is eating.
        if ((t + b) / 2 < rect.height / 2) top = Math.max(top, b + TRANSFER_FIT_PAD_PX);
        else bottom = Math.min(bottom, t - TRANSFER_FIT_PAD_PX);
    }

    return {
        width: Math.max(40, rect.width - TRANSFER_FIT_PAD_PX * 2),
        height: Math.max(40, bottom - top),
        cx: rect.width / 2,
        // Centre of what is actually visible, not of the map — so a route ends up in the
        // band between the panels rather than centred behind them.
        cy: (top + bottom) / 2,
    };
}

// Frame the two bodies and the whole of the highlighted route.
//
// Solved in SCREEN space, not world space. The obvious version — take the world bounding box
// and divide — is exact only once trueScale has finished easing to 1, and the second the
// player picks a route the picture is still morphing out of the schematic. A world-space fit
// during that second targets a frame that does not match anything on screen, so the camera
// swings out and then crawls back. Measuring what is actually drawn, at a candidate zoom,
// costs a handful of transforms and is right at every point of the transition.
//
// The solve is a fixed point rather than a formula because the drawn extent depends on the
// zoom it is measured at (the warp, and the exaggerated body radii, are both functions of
// it). Once trueScale reaches 1 the transform is linear and the first pass lands exactly;
// the extra passes exist only for the morph.
function fitTransferSelection() {
    const source = transferSourceBody, dest = transferDestinationBody;
    if (!source || !dest) return;

    const entry = highlightedFanEntry();
    const path = entry && entry.path && entry.path.length > 1 ? entry.path : null;
    const view = transferFitViewport();

    // Drawn extent of everything that has to fit, at whatever the camera is set to now.
    const measure = () => {
        let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
        const add = (x, y, r) => {
            if (x - r < minX) minX = x - r;
            if (x + r > maxX) maxX = x + r;
            if (y - r < minY) minY = y - r;
            if (y + r > maxY) maxY = y + r;
        };
        for (const b of [source, dest]) {
            const s = bodyScreenPos(b);
            add(s.x, s.y, bodyScreenRadius(b));
        }
        if (path) {
            // Every point would be hundreds of transforms a frame for a bound that a
            // sample settles to within a pixel. The last point is taken explicitly so the
            // arrival is never the one the stride skips.
            const step = Math.max(1, Math.ceil(path.length / TRANSFER_FIT_SAMPLES));
            for (let i = 0; i < path.length; i += step) {
                const s = displayTransform(path[i].x, path[i].y);
                add(s.x, s.y, 0);
            }
            const end = displayTransform(path[path.length - 1].x, path[path.length - 1].y);
            add(end.x, end.y, 0);
        }
        return { minX, maxX, minY, maxY };
    };

    const z0 = camera.zoom, cx0 = camera.x, cy0 = camera.y;
    let z = z0, cx = cx0, cy = cy0;

    // Until there is a route, the camera does the least it can get away with: it moves only
    // to stop the two bodies leaving the screen, and otherwise not at all.
    //
    // Two bodies are not the thing being framed — the route between them is, and it is a far
    // bigger and differently placed object. Framing the pair while the scan is still out
    // therefore aims at the wrong picture in both senses: it zooms onto them and then back
    // out, and it slides to the midpoint between them and then off again to wherever the
    // route actually lies. The whole opening of a transfer spent going somewhere it did not
    // mean to go.
    //
    // Doing nothing at all until the scan lands is not the answer either. The switch to true
    // scale runs through exactly this window and pulls the bodies apart to their real
    // separation, so a frozen camera would let them drift off the edge. Keeping them on
    // screen is the one thing that genuinely needs the camera here; framing them is the part
    // that is guessing.
    //
    // Same for re-scans: moving the time wheel empties the fan, and without this the view
    // lurched at the pair and recovered on every scrub of the clock.
    const framing = !!path;
    const halfW = view.width / 2, halfH = view.height / 2;

    for (let k = 0; k < TRANSFER_FIT_STEPS; k++) {
        camera.zoom = z; camera.x = cx; camera.y = cy;
        const m = measure();

        // Move at the zoom the measurement was taken at — the layout is
        // translation-equivariant, so this lands exactly — then correct the zoom. The
        // shift survives the zoom change because it is stored in world units.
        cx += axisCorrection(m.minX, m.maxX, view.cx - halfW, view.cx + halfW, framing) / z;
        cy += axisCorrection(m.minY, m.maxY, view.cy - halfH, view.cy + halfH, framing) / z;

        const over = Math.max((m.maxX - m.minX) / view.width,
                              (m.maxY - m.minY) / view.height);
        if (over > 1e-6) z = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, z / over));
        if (!framing) z = Math.min(z, z0);   // widen if the morph demands it, never tighten
    }

    // The probes trampled the live camera; put it back before easing, or the ease would
    // start from the last candidate instead of from where the player is looking.
    camera.zoom = z0; camera.x = cx0; camera.y = cy0;
    easeCameraToward({ x: cx, y: cy, zoom: z });
}

// How far to slide one axis, in screen pixels, to put the span [lo, hi] where it belongs
// between the edges [edgeLo, edgeHi]. Positive means the content should move left/up.
//
// `centre` picks between the two jobs this serves: centring the content, which is what
// framing a chosen route means, and merely rescuing it, which is all that is wanted before
// there is anything worth framing — content already inside the edges is left exactly where
// it is. When the span is wider than the space, "inside" is unachievable and both fall back
// to centring, which is the least bad of the positions available.
function axisCorrection(lo, hi, edgeLo, edgeHi, centre) {
    const outLo = edgeLo - lo;   // > 0 when it hangs off the near edge
    const outHi = hi - edgeHi;   // > 0 when it hangs off the far edge
    if (centre || (outLo > 0 && outHi > 0)) return (outHi - outLo) / 2;
    if (outLo > 0) return -outLo;
    if (outHi > 0) return outHi;
    return 0;
}

// Move the camera a fixed fraction of the way to `target`, and say whether it has
// effectively arrived. Glide, never snap: picking a route replaces the target outright, and
// watching the new one settle into frame is most of how the choice reads.
//
// Zoom eases in log space so a factor-of-two change takes the same time in either
// direction; easing it linearly would make zooming out feel slower than zooming in.
function easeCameraToward(target) {
    camera.zoom = Math.exp(Math.log(camera.zoom)
        + (Math.log(target.zoom) - Math.log(camera.zoom)) * TRANSFER_FIT_EASE);
    camera.x += (target.x - camera.x) * TRANSFER_FIT_EASE;
    camera.y += (target.y - camera.y) * TRANSFER_FIT_EASE;

    // "Arrived" measured in screen pixels rather than world units — a world tolerance
    // means something different at every zoom, and what matters is whether the picture is
    // still visibly moving.
    return Math.hypot(target.x - camera.x, target.y - camera.y) * camera.zoom < 0.5
        && Math.abs(Math.log(target.zoom / camera.zoom)) < 1e-3;
}

// Fit camera to show craft trajectory and destination body
function fitCraftTrajectory(craft) {
    if (!craft) return;

    const rect = svg.getBoundingClientRect();

    // Collect all points to fit: craft position, trajectory, and destination
    let minX = Infinity, maxX = -Infinity;
    let minY = Infinity, maxY = -Infinity;

    // Include craft's current position
    const craftPos = craft.getPosition();
    minX = Math.min(minX, craftPos.x);
    maxX = Math.max(maxX, craftPos.x);
    minY = Math.min(minY, craftPos.y);
    maxY = Math.max(maxY, craftPos.y);

    // Include trajectory points
    for (const point of craft.trajectoryBuffer) {
        minX = Math.min(minX, point.x);
        maxX = Math.max(maxX, point.x);
        minY = Math.min(minY, point.y);
        maxY = Math.max(maxY, point.y);
    }

    // Include destination body if set
    if (craft.destinationBody) {
        const dest = craft.destinationBody;
        minX = Math.min(minX, dest.x - dest.radius);
        maxX = Math.max(maxX, dest.x + dest.radius);
        minY = Math.min(minY, dest.y - dest.radius);
        maxY = Math.max(maxY, dest.y + dest.radius);
    }

    if (minX === Infinity) return;

    // Calculate center and zoom
    const centerX = (minX + maxX) / 2;
    const centerY = (minY + maxY) / 2;
    const worldWidth = maxX - minX;
    const worldHeight = maxY - minY;
    const margin = 1.3; // 30% margin

    const zoomX = rect.width / (worldWidth * margin);
    const zoomY = rect.height / (worldHeight * margin);
    const targetZoom = Math.min(zoomX, zoomY, MAX_ZOOM);

    camera.x = centerX;
    camera.y = centerY;
    camera.zoom = Math.max(targetZoom, MIN_ZOOM);
}

// Main game loop
function gameLoop(timestamp) {
    const frameStartTime = performance.now();

    const dt = (timestamp - lastTime) / 1000;
    lastTime = timestamp;

    advanceTrueScale(timestamp);
    advanceTimeline(dt);
    extendCraftBuffers();
    updateTransferSearch();

    // Sync all body/craft state to the currently viewed frame (present or future)
    syncToViewFrame();
    updateCameraTracking();
    render();
    updateTrajectories();
    renderDebugOverlay();

    // Redraw time wheel and label if panel is open
    if (timeScrubPanelOpen) {
        drawTimeWheel();
        updateTimeScrubLabel();
    }

    // Keep the transfer panel in step with the fan while planning
    if (transferIsPlanning()) {
        updateTransferPanel();
    }

    // CPU benchmark: measure work time and report once per second
    if (benchmarkEnabled) {
        const frameEndTime = performance.now();
        const workTime = frameEndTime - frameStartTime;
        benchmarkTotalWorkTime += workTime;
        benchmarkFrameCount++;

        // Report once per second (using timestamp which is in ms)
        if (benchmarkLastReportTime === 0) {
            benchmarkLastReportTime = timestamp;
        } else if (timestamp - benchmarkLastReportTime >= 1000) {
            const elapsedMs = timestamp - benchmarkLastReportTime;
            const cpuPercent = (benchmarkTotalWorkTime / elapsedMs) * 100;
            const avgFrameTime = benchmarkTotalWorkTime / benchmarkFrameCount;
            _origConsoleLog(`[CPU Benchmark] CPU: ${cpuPercent.toFixed(1)}% | Avg frame: ${avgFrameTime.toFixed(2)}ms | Frames: ${benchmarkFrameCount} | Elapsed: ${(elapsedMs/1000).toFixed(1)}`);

            // Reset counters for next interval
            benchmarkLastReportTime = timestamp;
            benchmarkTotalWorkTime = 0;
            benchmarkFrameCount = 0;
        }
    }

    requestAnimationFrame(gameLoop);
}

// Time scrub wheel drawing (SVG-based)
// The outer ring with notches rotates visually as the user drags.
let timeWheelInitialized = false;
let timeWheelRotation = 0; // cumulative rotation in degrees for the outer wheel

function initTimeWheelSVG() {
    const svgEl = document.getElementById('time-wheel');
    if (!svgEl || timeWheelInitialized) return;
    timeWheelInitialized = true;

    const ns = 'http://www.w3.org/2000/svg';
    const cx = 60, cy = 60, r = 45;

    // --- Rotating outer group (ring + notches) ---
    const outerGroup = document.createElementNS(ns, 'g');
    outerGroup.setAttribute('id', 'wheel-outer-group');

    // Outer ring
    const ring = document.createElementNS(ns, 'circle');
    ring.setAttribute('cx', cx);
    ring.setAttribute('cy', cy);
    ring.setAttribute('r', r);
    ring.setAttribute('fill', 'none');
    ring.setAttribute('stroke-width', '3');
    ring.setAttribute('class', 'wheel-ring');
    outerGroup.appendChild(ring);

    // 24 notch marks around the edge for a detailed mechanical look
    for (let i = 0; i < 24; i++) {
        const angle = (i / 24) * 360 - 90;
        const isMajor = i % 6 === 0;
        const isMedium = i % 3 === 0;
        const innerR = isMajor ? r - 10 : (isMedium ? r - 7 : r - 5);
        const outerR = r - 1;
        const rad = angle * Math.PI / 180;
        const line = document.createElementNS(ns, 'line');
        line.setAttribute('x1', cx + innerR * Math.cos(rad));
        line.setAttribute('y1', cy + innerR * Math.sin(rad));
        line.setAttribute('x2', cx + outerR * Math.cos(rad));
        line.setAttribute('y2', cy + outerR * Math.sin(rad));
        line.setAttribute('stroke-width', isMajor ? 2.5 : (isMedium ? 1.5 : 1));
        line.setAttribute('class', 'wheel-notch');
        outerGroup.appendChild(line);
    }

    svgEl.appendChild(outerGroup);

    // --- Static inner elements (progress arc + indicator dot) ---
    const progressArc = document.createElementNS(ns, 'path');
    progressArc.setAttribute('id', 'wheel-progress-arc');
    progressArc.setAttribute('fill', 'none');
    progressArc.setAttribute('stroke-width', '4');
    progressArc.setAttribute('opacity', '0.6');
    progressArc.setAttribute('stroke-linecap', 'round');
    progressArc.setAttribute('class', 'wheel-progress');
    svgEl.appendChild(progressArc);

    const dot = document.createElementNS(ns, 'circle');
    dot.setAttribute('id', 'wheel-indicator-dot');
    dot.setAttribute('r', '5');
    dot.setAttribute('class', 'wheel-dot');
    svgEl.appendChild(dot);

    // --- Step buttons (static, non-rotating, center of wheel) ---
    const btnGroup = document.createElementNS(ns, 'g');
    btnGroup.setAttribute('id', 'wheel-step-buttons');
    btnGroup.setAttribute('pointer-events', 'none'); // drags pass through to wheel

    // Left step button (retreat one frame)
    const leftArrow = document.createElementNS(ns, 'path');
    leftArrow.setAttribute('id', 'wheel-step-left');
    leftArrow.setAttribute('d', 'M 32.7 60 L 55.7 44.7 L 55.7 75.3 Z');
    leftArrow.setAttribute('class', 'wheel-step-arrow');
    btnGroup.appendChild(leftArrow);

    // Right step button (advance one frame)
    const rightArrow = document.createElementNS(ns, 'path');
    rightArrow.setAttribute('id', 'wheel-step-right');
    rightArrow.setAttribute('d', 'M 87.3 60 L 64.3 44.7 L 64.3 75.3 Z');
    rightArrow.setAttribute('class', 'wheel-step-arrow');
    btnGroup.appendChild(rightArrow);

    svgEl.appendChild(btnGroup);
}

function drawTimeWheel() {
    const svgEl = document.getElementById('time-wheel');
    if (!svgEl) return;

    if (!timeWheelInitialized) initTimeWheelSVG();

    const cx = 60, cy = 60, r = 45;

    // Get computed styles for theme-aware colors
    const style = getComputedStyle(document.documentElement);
    const mutedColor = style.getPropertyValue('--text-muted').trim() || '#888888';
    const accentColor = style.getPropertyValue('--accent-color').trim() || '#88aaff';
    const borderColor = style.getPropertyValue('--panel-border').trim() || '#333333';

    // Apply colors
    const ring = svgEl.querySelector('.wheel-ring');
    if (ring) ring.setAttribute('stroke', borderColor);

    svgEl.querySelectorAll('.wheel-notch').forEach(n => n.setAttribute('stroke', mutedColor));

    // Rotate the outer group (ring + notches) to match drag
    const outerGroup = document.getElementById('wheel-outer-group');
    if (outerGroup) {
        outerGroup.setAttribute('transform', `rotate(${timeWheelRotation} ${cx} ${cy})`);
    }

    // Progress arc
    const maxOffset = predictionBuffer.length > 0 ? predictionBuffer.length - 1 : 1;
    const progress = timeViewOffset / maxOffset;
    const progressArc = document.getElementById('wheel-progress-arc');
    if (progressArc) {
        progressArc.setAttribute('stroke', accentColor);
        if (progress > 0.001) {
            const arcR = r - 5;
            if (progress >= 0.999) {
                // Full circle — SVG arcs degenerate when start ≈ end, so use two semicircles
                progressArc.setAttribute('d',
                    `M ${cx} ${cy - arcR} A ${arcR} ${arcR} 0 1 1 ${cx} ${cy + arcR} A ${arcR} ${arcR} 0 1 1 ${cx} ${cy - arcR}`);
            } else {
                const startAngle = -Math.PI / 2;
                const endAngle = startAngle + progress * 2 * Math.PI;
                const x1 = cx + arcR * Math.cos(startAngle);
                const y1 = cy + arcR * Math.sin(startAngle);
                const x2 = cx + arcR * Math.cos(endAngle);
                const y2 = cy + arcR * Math.sin(endAngle);
                const largeArc = progress > 0.5 ? 1 : 0;
                progressArc.setAttribute('d', `M ${x1} ${y1} A ${arcR} ${arcR} 0 ${largeArc} 1 ${x2} ${y2}`);
            }
            progressArc.style.display = '';
        } else {
            progressArc.style.display = 'none';
        }
    }

    // Indicator dot
    const dot = document.getElementById('wheel-indicator-dot');
    if (dot) {
        dot.setAttribute('fill', accentColor);
        const dotR = r - 5;
        const dotAngle = -Math.PI / 2 + progress * 2 * Math.PI;
        dot.setAttribute('cx', cx + dotR * Math.cos(dotAngle));
        dot.setAttribute('cy', cy + dotR * Math.sin(dotAngle));
    }

    // Step buttons — grey out at boundaries
    const leftStep = document.getElementById('wheel-step-left');
    const rightStep = document.getElementById('wheel-step-right');
    if (leftStep) {
        leftStep.setAttribute('fill', mutedColor);
        leftStep.setAttribute('opacity', timeViewOffset <= 0 ? '0.2' : '0.7');
    }
    if (rightStep) {
        rightStep.setAttribute('fill', mutedColor);
        rightStep.setAttribute('opacity', timeViewOffset >= maxOffset ? '0.2' : '0.7');
    }
}

// Update the time scrub label
function updateTimeScrubLabel() {
    const label = document.getElementById('time-scrub-label');
    if (!label) return;
    const offsetMin = (timeViewOffset * PREDICTION_DT).toFixed(PREDICTION_DT_DECIMALS);
    label.textContent = '+' + offsetMin + 'm';
}

// Move the clock from outside the wheel's handlers. Everything the wheel does on a drag
// has to happen here too: a fling still coasting would drag the time straight back off
// the moment just set, and the ring is a separate visual that only turns when told to,
// so setting the offset without spinning it leaves it pointing at the wrong time.
function setTimeViewOffset(frames) {
    const maxOffset = predictionBuffer.length > 0 ? predictionBuffer.length - 1 : 0;
    const next = Math.max(0, Math.min(maxOffset, frames));
    if (next === timeViewOffset) return;
    stopWheelCoast();
    timeWheelRotation += ((next - timeViewOffset) / FRAMES_PER_RADIAN) * (180 / Math.PI);
    timeViewOffset = next;
    updateTimeScrubLabel();
    drawTimeWheel();
}

// Initialize
function init() {
    // Initialize worker pool for parallel transfer search
    initWorkerPool();

    svg.addEventListener('mousemove', handleMouseMove);
    svg.addEventListener('mousedown', handleMouseDown);
    svg.addEventListener('mouseup', handleMouseUp);
    svg.addEventListener('mouseleave', abandonGesture);
    svg.addEventListener('wheel', handleWheel, { passive: false });

    // Touch events for mobile
    svg.addEventListener('touchstart', handleTouchStart, { passive: false });
    svg.addEventListener('touchmove', handleTouchMove, { passive: false });
    svg.addEventListener('touchend', handleTouchEnd, { passive: false });
    // A cancelled touch is the system taking the gesture away, so it must drop
    // everything rather than commit whatever the finger happened to be over.
    svg.addEventListener('touchcancel', () => {
        abandonGesture();
        touchState.active = false;
        touchState.lastTouches = [];
        touchState.lastPinchDist = 0;
    }, { passive: false });

    // Prevent browser zoom on UI elements (multi-touch pinch and double-tap)
    // This ensures only the game canvas handles zoom, not the browser
    document.addEventListener('touchstart', (e) => {
        // Prevent multi-touch (pinch) from triggering browser zoom on UI elements
        if (e.touches.length > 1 && e.target !== svg && !svg.contains(e.target)) {
            e.preventDefault();
        }
    }, { passive: false });

    document.addEventListener('touchmove', (e) => {
        // Prevent pinch-to-zoom on UI elements
        if (e.touches.length > 1 && e.target !== svg && !svg.contains(e.target)) {
            e.preventDefault();
        }
    }, { passive: false });

    // Prevent Safari gesture zoom on UI elements
    document.addEventListener('gesturestart', (e) => {
        if (e.target !== svg && !svg.contains(e.target)) {
            e.preventDefault();
        }
    }, { passive: false });

    document.addEventListener('gesturechange', (e) => {
        if (e.target !== svg && !svg.contains(e.target)) {
            e.preventDefault();
        }
    }, { passive: false });

    // Clicks on craft trajectories are handled by selectAtPoint, which hit-tests
    // the drawn path the same way for mouse and touch. A separate 'click' listener
    // here would also fire after a pan that merely started and ended on the path.

    // Controls popover
    const popoverTrigger = document.getElementById('popover-trigger');
    const popoverPanel = document.getElementById('popover-panel');
    let popoverOpen = false;

    function openControlsPopover() {
        popoverOpen = true;
        popoverPanel.classList.remove('hidden');
        popoverPanel.offsetHeight; // Force reflow for transition
        popoverPanel.classList.remove('opacity-0', 'translate-y-1');
        popoverPanel.classList.add('opacity-100', 'translate-y-0');
    }

    function closeControlsPopover() {
        popoverOpen = false;
        popoverPanel.classList.remove('opacity-100', 'translate-y-0');
        popoverPanel.classList.add('opacity-0', 'translate-y-1');
        const onTransitionEnd = () => {
            if (!popoverOpen) popoverPanel.classList.add('hidden');
            popoverPanel.removeEventListener('transitionend', onTransitionEnd);
        };
        popoverPanel.addEventListener('transitionend', onTransitionEnd);
    }

    popoverTrigger.addEventListener('click', (e) => {
        e.stopPropagation();
        if (popoverOpen) closeControlsPopover();
        else openControlsPopover();
    });

    document.addEventListener('click', (e) => {
        if (popoverOpen && !popoverPanel.contains(e.target) && !popoverTrigger.contains(e.target)) {
            closeControlsPopover();
        }
    });

    // Reset item in popover
    document.getElementById('reset-item').addEventListener('click', () => {
        initBodies();
        resetPredictions();
        resetTransferState();
        abandonGesture();
        selectedBody = null;
        selectedSquadron = null;
        hoveredBody = null;
        isAutoFitPaused = false;
        isTrackingSelectedSquadron = false;
        // Reset time scrub state
        timeViewOffset = 0;
        timeScrubPanelOpen = false;
        const scrubPanel = document.getElementById('time-scrub-panel');
        if (scrubPanel) scrubPanel.classList.remove('visible');
        // Reset squadrons
        for (const sq of squadrons) sq.removeElements();
        squadrons.length = 0;
        scheduledTransfers.length = 0;
        camera = { x: 0, y: 0, zoom: 1 };
        updateTimeScrubLabel();
        closeControlsPopover();
    });

    // Fit All item in popover
    document.getElementById('fit-all-item').addEventListener('click', () => {
        isTrackingSelectedSquadron = false;
        isAutoFitPaused = false;
        transferViewReleased = true;   // see resetAutoFit
        fitAllBodies();
        closeControlsPopover();
    });

    // Escape key to reset auto-fit
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') {
            resetAutoFit();
        }
    });

    // Energy display click handler - toggle body details dropdown
    document.getElementById('energy-display').addEventListener('click', () => {
        if (!selectedBody) return;
        bodyInfoExpanded = !bodyInfoExpanded;
        const dropdown = document.getElementById('body-details-dropdown');
        dropdown.classList.toggle('expanded', bodyInfoExpanded);
    });

    // The selected-body panel now holds one control: build a craft here.
    // Choosing where craft go is the map's job, not a list's.
    document.getElementById('selected-body-info').addEventListener('click', (e) => {
        if (e.target.id === 'build-craft-btn' && selectedBody) {
            addCraftToOrbit(selectedBody, 1);
        }
    });

    // To-scale toggle. Timestamps come from performance.now() so they share a clock
    // with the requestAnimationFrame timestamp advanceTrueScale() eases against.
    document.getElementById('true-scale-btn').addEventListener('click', () => {
        setTrueScale(!trueScaleOn, performance.now());
        // Pressed while a transfer was being planned, which switched to true scale on the
        // player's behalf. Forget what we meant to restore: they have now said what they
        // want the map to look like, and putting it back when the transfer ends would read
        // as the button not having worked.
        scaleBeforeTransfer = null;
    });

    // Time scrub button and wheel
    const timeScrubBtn = document.getElementById('time-scrub-btn');
    const timeScrubPanel = document.getElementById('time-scrub-panel');
    const timeWheelSvg = document.getElementById('time-wheel');
    const timeScrubLabel = document.getElementById('time-scrub-label');

    timeScrubBtn.addEventListener('click', () => {
        timeScrubPanelOpen = !timeScrubPanelOpen;
        timeScrubPanel.classList.toggle('visible', timeScrubPanelOpen);
        timeScrubBtn.classList.toggle('active', timeScrubPanelOpen);
        if (timeScrubPanelOpen) {
            initTimeWheelSVG();
            drawTimeWheel();
        } else {
            // Reset view offset, wheel rotation, and stop momentum when closing
            stopWheelMomentum();
            timeViewOffset = 0;
            timeWheelRotation = 0;
            updateTimeScrubLabel();
        }
    });

    // Time wheel interaction state
    let wheelDragging = false;
    let wheelLastAngle = 0;
    let wheelAccumulatedAngle = 0;

    // Tap detection for step buttons
    let wheelTapStartX = 0;
    let wheelTapStartY = 0;
    let wheelTapStartTime = 0;
    let wheelTotalDragDelta = 0;

    // Momentum state — velocity is measured directly from finger movement so that
    // coast speed matches drag speed. An asymmetric exponential moving average
    // responds quickly to speed-ups / direction changes but resists brief
    // slow-downs right before release so built-up momentum isn't lost.
    let wheelVelocity = 0;          // angular velocity in radians/ms
    let wheelMomentumRAF = null;    // requestAnimationFrame id
    let wheelPendingImpulse = 0;    // accumulated finger delta since last physics tick (radians)
    let wheelLastTickTime = 0;      // timestamp of last physics tick
    const WHEEL_COAST_FRICTION = 0.979;  // velocity decay when free-spinning (long coast)
    const WHEEL_GRIP_FRICTION = 0.895;   // velocity decay when finger is on wheel (quick stop)
    const WHEEL_STOP_THRESHOLD = 0.0005; // min velocity before stopping (rad/ms) — snappy cutoff like a real wheel

    function getWheelAngle(clientX, clientY) {
        const rect = timeWheelSvg.getBoundingClientRect();
        // The centre of the element, not a fixed offset: the wheel is drawn centred in
        // its viewBox, so wherever that box is cropped to, the centre stays the middle
        // of the rendered box.
        const x = clientX - rect.left - rect.width / 2;
        const y = clientY - rect.top - rect.height / 2;
        return Math.atan2(y, x);
    }

    function applyWheelDelta(delta) {
        // Clamp offset to valid range, then only rotate wheel by the effective delta
        const maxOffset = predictionBuffer.length > 0 ? predictionBuffer.length - 1 : 0;
        const prevOffset = timeViewOffset;
        timeViewOffset = Math.max(0, Math.min(maxOffset, timeViewOffset + delta * FRAMES_PER_RADIAN));
        const effectiveDelta = (timeViewOffset - prevOffset) / FRAMES_PER_RADIAN;

        // Rotate the outer wheel visually (convert radians to degrees)
        timeWheelRotation += effectiveDelta * (180 / Math.PI);

        updateTimeScrubLabel();
        drawTimeWheel();
    }

    function stopWheelMomentum() {
        if (wheelMomentumRAF !== null) {
            cancelAnimationFrame(wheelMomentumRAF);
            wheelMomentumRAF = null;
        }
        wheelVelocity = 0;
        wheelPendingImpulse = 0;
    }
    stopWheelCoast = stopWheelMomentum;   // see setTimeViewOffset

    function stepTimeScrub(direction) {
        const maxOffset = predictionBuffer.length > 0 ? predictionBuffer.length - 1 : 0;
        const newOffset = Math.max(0, Math.min(maxOffset, Math.round(timeViewOffset) + direction));
        if (newOffset !== timeViewOffset) {
            const frameDelta = newOffset - timeViewOffset;
            const radianDelta = frameDelta / FRAMES_PER_RADIAN;
            timeViewOffset = newOffset;
            timeWheelRotation += radianDelta * (180 / Math.PI);
            updateTimeScrubLabel();
            drawTimeWheel();
        }
    }

    function tickWheel(timestamp) {
        if (!timeScrubPanelOpen) {
            wheelMomentumRAF = null;
            return;
        }

        const dt = timestamp - wheelLastTickTime;
        wheelLastTickTime = timestamp;

        // Skip if dt is unreasonable (first frame or long pause)
        if (dt <= 0 || dt > 200) {
            wheelMomentumRAF = requestAnimationFrame(tickWheel);
            return;
        }

        // Process accumulated finger impulse
        const impulse = wheelPendingImpulse;
        wheelPendingImpulse = 0;

        if (wheelDragging) {
            if (Math.abs(impulse) > 0.001) {
                // Measure finger velocity directly so coast speed matches drag speed.
                // Asymmetric blend: fast response to speed-ups and direction changes,
                // slow response to brief slow-downs (preserves momentum before release).
                const fingerVelocity = impulse / dt;
                const sameDir = (fingerVelocity > 0) === (wheelVelocity > 0)
                    || Math.abs(wheelVelocity) < WHEEL_STOP_THRESHOLD;
                const slowingDown = sameDir && Math.abs(fingerVelocity) < Math.abs(wheelVelocity);
                const retention = slowingDown ? 0.85 : 0.4;
                const blend = 1 - Math.pow(retention, dt / 16);
                wheelVelocity = wheelVelocity * (1 - blend) + fingerVelocity * blend;
            } else {
                // Finger is down but not moving — apply grip friction (quick stop)
                wheelVelocity *= Math.pow(WHEEL_GRIP_FRICTION, dt / 16);
            }
        } else {
            // Coasting — apply coast friction
            wheelVelocity *= Math.pow(WHEEL_COAST_FRICTION, dt / 16);
        }

        // Apply velocity to wheel position (only when coasting — during drag,
        // handleWheelMove applies deltas directly for 1:1 finger tracking)
        if (!wheelDragging && Math.abs(wheelVelocity) >= WHEEL_STOP_THRESHOLD) {
            applyWheelDelta(wheelVelocity * dt);
        }

        // Clamp velocity at boundaries
        const maxOffset = predictionBuffer.length > 0 ? predictionBuffer.length - 1 : 0;
        if (timeViewOffset <= 0 && wheelVelocity < 0) wheelVelocity = 0;
        if (timeViewOffset >= maxOffset && wheelVelocity > 0) wheelVelocity = 0;

        // Stop tick if coasting and velocity is negligible
        if (!wheelDragging && Math.abs(wheelVelocity) < WHEEL_STOP_THRESHOLD) {
            wheelVelocity = 0;
            wheelMomentumRAF = null;
            return;
        }

        wheelMomentumRAF = requestAnimationFrame(tickWheel);
    }

    function handleWheelStart(clientX, clientY) {
        wheelDragging = true;
        wheelLastAngle = getWheelAngle(clientX, clientY);
        wheelPendingImpulse = 0;
        // Record tap start for step button detection
        wheelTapStartX = clientX;
        wheelTapStartY = clientY;
        wheelTapStartTime = performance.now();
        wheelTotalDragDelta = 0;
        // Start physics tick if not already running (preserves existing velocity
        // so consecutive flicks can build up speed)
        if (wheelMomentumRAF === null) {
            wheelLastTickTime = performance.now();
            wheelMomentumRAF = requestAnimationFrame(tickWheel);
        }
    }

    function handleWheelMove(clientX, clientY) {
        if (!wheelDragging) return;
        const currentAngle = getWheelAngle(clientX, clientY);
        let delta = currentAngle - wheelLastAngle;

        // Handle wrapping around -PI/PI boundary
        if (delta > Math.PI) delta -= 2 * Math.PI;
        if (delta < -Math.PI) delta += 2 * Math.PI;

        // Block impulse past boundaries
        const maxOffset = predictionBuffer.length > 0 ? predictionBuffer.length - 1 : 0;
        if (timeViewOffset <= 0 && delta < 0) delta = 0;
        if (timeViewOffset >= maxOffset && delta > 0) delta = 0;

        wheelAccumulatedAngle += delta;
        wheelLastAngle = currentAngle;
        wheelTotalDragDelta += Math.abs(delta);

        // Apply finger delta directly to the wheel for 1:1 tracking
        applyWheelDelta(delta);

        // Also accumulate as impulse so tickWheel can track velocity for coast on release
        wheelPendingImpulse += delta;
    }

    function handleWheelEnd() {
        wheelDragging = false;

        // Detect quick tap on step buttons (minimal drag, short duration)
        const tapElapsed = performance.now() - wheelTapStartTime;
        if (tapElapsed < 300 && wheelTotalDragDelta < 0.05) {
            // Convert tap position to SVG coordinates
            const rect = timeWheelSvg.getBoundingClientRect();
            // Read the mapping off the viewBox rather than assuming one, so the arrow
            // zones below stay in the drawing's own coordinates however it is cropped.
            const vb = timeWheelSvg.viewBox.baseVal;
            const svgX = vb.x + (wheelTapStartX - rect.left) * (vb.width / rect.width);
            const svgY = vb.y + (wheelTapStartY - rect.top) * (vb.height / rect.height);

            // Left button zone: triangle around (32.7-55.7, 44.7-75.3) with padding
            if (svgX >= 26 && svgX <= 58 && svgY >= 38 && svgY <= 82) {
                stopWheelMomentum();
                stepTimeScrub(-1);
                return;
            }
            // Right button zone: triangle around (64.3-87.3, 44.7-75.3) with padding
            if (svgX >= 62 && svgX <= 94 && svgY >= 38 && svgY <= 82) {
                stopWheelMomentum();
                stepTimeScrub(1);
                return;
            }
        }
        // Physics tick continues running — wheel coasts on its built-up momentum
    }

    // Mouse events
    timeWheelSvg.addEventListener('mousedown', (e) => {
        e.preventDefault();
        handleWheelStart(e.clientX, e.clientY);
    });
    window.addEventListener('mousemove', (e) => {
        if (wheelDragging) handleWheelMove(e.clientX, e.clientY);
    });
    window.addEventListener('mouseup', () => {
        if (wheelDragging) handleWheelEnd();
    });

    // Touch events
    timeWheelSvg.addEventListener('touchstart', (e) => {
        e.preventDefault();
        const touch = e.touches[0];
        handleWheelStart(touch.clientX, touch.clientY);
    });
    window.addEventListener('touchmove', (e) => {
        if (wheelDragging) {
            e.preventDefault();
            const touch = e.touches[0];
            handleWheelMove(touch.clientX, touch.clientY);
        }
    }, { passive: false });
    window.addEventListener('touchend', () => {
        if (wheelDragging) handleWheelEnd();
    });
    window.addEventListener('touchcancel', () => {
        if (wheelDragging) handleWheelEnd();
    });

    // Scroll wheel / trackpad events — turn the scrubber on hover + scroll
    timeWheelSvg.addEventListener('wheel', (e) => {
        e.preventDefault();
        // Convert pixel delta to radians (negative so scroll-down = forward in time)
        const PIXELS_PER_RADIAN = 200;
        const delta = e.deltaY / PIXELS_PER_RADIAN;
        applyWheelDelta(delta);
    }, { passive: false });

    createTransferDragLine();
    initBodies();

    lastTime = performance.now();
    requestAnimationFrame(gameLoop);
}

// Debug helper - call window.debugSquadrons() in browser console
window.debugSquadrons = function() {
    console.log('=== Squadron Debug ===');
    console.log(`Total squadrons: ${squadrons.length}`);
    for (const sq of squadrons) {
        const inDOM = sq.element ? !!sq.element.parentNode : false;
        const display = sq.element ? sq.element.style.display : 'N/A';
        const cx = sq.element ? sq.element.getAttribute('cx') : 'N/A';
        const cy = sq.element ? sq.element.getAttribute('cy') : 'N/A';
        console.log(`  [transit] src=${sq.sourceBody?.name} count=${sq.count} _displayCount=${sq._displayCount} pos=(${sq.x?.toFixed(1)},${sq.y?.toFixed(1)}) cx=${cx} cy=${cy} display=${display} inDOM=${inDOM} element=${!!sq.element} dest=${sq.destinationBody?.name ?? 'none'} trajBuf=${sq.trajectoryBuffer.length}`);
    }
    console.log(`Scheduled transfers: ${scheduledTransfers.length}`);
    for (const t of scheduledTransfers) {
        const sq = t.squadron;
        console.log(`  ${t.sourceBody.name} → ${t.destBody.name} count=${sq.count} launchFrame=${sq.launchFrame} trajLen=${sq.trajectoryBuffer.length}`);
    }
    console.log(`Bodies layer children: ${bodiesLayer.children.length}`);
};

// Start the game
init();

// Commit info display functionality
(function initCommitInfo() {
    const commitInfoEl = document.getElementById('commit-info');
    const commitModal = document.getElementById('commit-modal');
    const commitModalContent = document.getElementById('commit-modal-content');

    if (!commitInfoEl || !commitModal) return;

    // Get commit hash and repo from meta tags (injected during build)
    const commitHashMeta = document.querySelector('meta[name="commit-hash"]');
    const repoMeta = document.querySelector('meta[name="github-repo"]');
    const branchMeta = document.querySelector('meta[name="branch-name"]');
    const commitHash = commitHashMeta?.content;
    const repoName = repoMeta?.content;
    const branchName = branchMeta?.content;

    if (!commitHash || !repoName) {
        commitInfoEl.textContent = 'dev';
        commitInfoEl.classList.remove('loading');
        return;
    }

    let commitData = null;

    // Format relative time with succinct notation (e.g., "3m ago", "4h ago")
    function formatRelativeTime(date) {
        const now = new Date();
        const diffMs = now - date;
        const diffSeconds = Math.floor(diffMs / 1000);
        const diffMinutes = Math.floor(diffSeconds / 60);
        const diffHours = Math.floor(diffMinutes / 60);
        const diffDays = Math.floor(diffHours / 24);
        const diffWeeks = Math.floor(diffDays / 7);
        const diffMonths = Math.floor(diffDays / 30);
        const diffYears = Math.floor(diffDays / 365);

        if (diffYears > 0) return `${diffYears}y ago`;
        if (diffMonths > 0) return `${diffMonths}mo ago`;
        if (diffWeeks > 0) return `${diffWeeks}w ago`;
        if (diffDays > 0) return `${diffDays}d ago`;
        if (diffHours > 0) return `${diffHours}h ago`;
        if (diffMinutes > 0) return `${diffMinutes}m ago`;
        if (diffSeconds > 0) return `${diffSeconds}s ago`;
        return 'now';
    }

    // Format date in RFC3339-like format (2-digit year, no timezone)
    function formatDate(date) {
        const pad = (n) => n.toString().padStart(2, '0');
        const year = date.getFullYear().toString().slice(-2);
        const month = pad(date.getMonth() + 1);
        const day = pad(date.getDate());
        const hours = pad(date.getHours());
        const minutes = pad(date.getMinutes());
        const seconds = pad(date.getSeconds());

        return `${year}-${month}-${day}T${hours}:${minutes}:${seconds}`;
    }

    // Update the relative time display
    function updateRelativeTime() {
        if (!commitData) return;
        const date = new Date(commitData.commit.author.date);
        commitInfoEl.textContent = formatRelativeTime(date);
    }

    // Fetch commit info from GitHub API with timeout
    async function fetchCommitInfo() {
        const controller = new AbortController();
        const timeoutId = setTimeout(() => controller.abort(), 5000);

        try {
            const response = await fetch(
                `https://api.github.com/repos/${repoName}/commits/${commitHash}`,
                { signal: controller.signal }
            );
            clearTimeout(timeoutId);
            if (!response.ok) throw new Error('Failed to fetch');

            commitData = await response.json();
            const date = new Date(commitData.commit.author.date);

            commitInfoEl.textContent = formatRelativeTime(date);
            commitInfoEl.classList.remove('loading');

            // Update relative time every minute
            setInterval(updateRelativeTime, 60000);

        } catch (error) {
            clearTimeout(timeoutId);
            commitInfoEl.textContent = commitHash.substring(0, 7);
            commitInfoEl.classList.remove('loading');
        }
    }

    // Show modal with commit message
    function showModal() {
        const branchEl = commitModalContent.querySelector('.commit-branch');
        const dateLineEl = commitModalContent.querySelector('.commit-date-line');
        const hashEl = commitModalContent.querySelector('.commit-hash');
        const messageEl = commitModalContent.querySelector('.commit-message');

        if (commitData) {
            const date = new Date(commitData.commit.author.date);
            branchEl.textContent = branchName ? `Branch: ${branchName}` : '';
            dateLineEl.textContent = formatDate(date);
            const commitUrl = `https://github.com/${repoName}/commit/${commitHash}`;
            hashEl.innerHTML = `<a href="${commitUrl}" target="_blank" rel="noopener noreferrer">${commitHash}</a>`;
            messageEl.textContent = commitData.commit.message;
        }

        // Populate log viewer
        const logViewer = document.getElementById('log-viewer');
        logViewer.textContent = _logBuffer.length > 0 ? _logBuffer.join('\n') : '(no logs yet)';
        logViewer.scrollTop = logViewer.scrollHeight;

        commitModal.classList.add('visible');
    }

    // Hide modal
    function hideModal() {
        commitModal.classList.remove('visible');
    }

    // Modal tab switching
    commitModalContent.addEventListener('click', (e) => {
        const tab = e.target.closest('.modal-tab');
        if (tab && tab.dataset.modalTab) {
            commitModalContent.querySelectorAll('.modal-tab').forEach(t => t.classList.remove('active'));
            commitModalContent.querySelectorAll('.modal-tab-body').forEach(b => b.classList.remove('active'));
            tab.classList.add('active');
            commitModalContent.querySelector(`.modal-tab-body[data-modal-tab-body="${tab.dataset.modalTab}"]`).classList.add('active');
            // Scroll log viewer to bottom when switching to logs tab
            if (tab.dataset.modalTab === 'logs') {
                const logViewer = document.getElementById('log-viewer');
                logViewer.textContent = _logBuffer.length > 0 ? _logBuffer.join('\n') : '(no logs yet)';
                logViewer.scrollTop = logViewer.scrollHeight;
            }
        }
    });

    // Copy logs to clipboard
    document.getElementById('copy-logs-btn').addEventListener('click', () => {
        const text = _logBuffer.join('\n');
        navigator.clipboard.writeText(text).then(() => {
            const btn = document.getElementById('copy-logs-btn');
            btn.textContent = 'Copied!';
            setTimeout(() => { btn.textContent = 'Copy All Logs'; }, 1500);
        });
    });

    // Event listeners
    commitInfoEl.addEventListener('click', () => {
        showModal();
    });

    commitModal.addEventListener('click', (e) => {
        if (e.target === commitModal) {
            hideModal();
        }
    });

    // Close on escape key
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape' && commitModal.classList.contains('visible')) {
            hideModal();
        }
    });

    // Fetch the commit info
    fetchCommitInfo();
})();
