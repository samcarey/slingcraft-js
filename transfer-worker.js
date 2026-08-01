// Transfer Search Web Worker
//
// Searches over RELEASE ANGLE, not over launch time.
//
// Craft parked at a body are held to have no particular orbital phase — they can cast
// off from wherever around the body suits them. So the free variable is where on the
// circle they let go, and the launch moment is whatever the player is looking at. That
// inverts the old search, which walked forward through launch frames and derived the
// phase from each one, and it is why a scan is now cheap enough to redo every time the
// time wheel moves: one moment, many angles, instead of many moments at one angle.
//
// For each release angle the burn after escape is then tuned for the EARLIEST ARRIVAL
// that still captures cleanly. See `optimizeBurn` for how those two goals are held in
// one number.

// Physics constants (must match game.js)
const G = 50.0;
const MIN_DISTANCE = 10;
const CRAFT_ACCELERATION = 2.5;
const PREDICTION_DT = 0.1; // minutes
const CRAFT_ORBITAL_ALTITUDE = 5;

// The release circle is divided into this many sectors, and exactly one angle — the most
// promising in that sector — is optimized from each.
//
// Sectors rather than a global ranking, and this is the difference between a fan and a
// thicket. Ranking the whole circle and spending the budget on the best sixty angles
// concentrates every one of them in the same narrow lobe, because release angles that
// work are neighbours: it drew thirty-four routes that were all the same route, drawn
// thirty-four times. Forcing one candidate per sector spends the same effort on options
// the player can actually tell apart, and covers arcs a global ranking would never reach.
//
// It also fixes the cost of a scan at a constant, which is what makes re-scanning on
// every move of the time wheel safe.
//
// Measured across six body pairs: 36 sectors gives a fan of 2-6 routes, 72 gives 3-11,
// 120 gives 6-19 at twice the cost and starts producing neighbours too alike to tell
// apart again. 72 is where the fan is worth dragging across.
const ANGLE_SECTORS = 72;   // 5 degrees each

// Below this, the craft was effectively already there and the "transfer" is a degenerate
// one-point path. Guards the fan renderer rather than the physics.
const MIN_TRANSFER_FRAMES = 5;

// Mean altitude error over the frames after closest approach that still counts as
// captured. This is the feasibility line: inside it a trajectory is offered to the
// player, outside it is discarded however early it arrives.
const POST_OPTIMIZATION_THRESHOLD = 5;

// How long a transfer is allowed to take before we stop simulating it. Capping this is
// the single biggest cost saving in the scan: the old search integrated every candidate
// to the end of the prediction buffer, which is up to 9x further than any transfer it
// would ever accept.
const MAX_TRANSFER_MINUTES = 200;
const MAX_TRANSFER_FRAMES = Math.ceil(MAX_TRANSFER_MINUTES / PREDICTION_DT);

// Longest burn the optimizer may ask for, in frames.
const MAX_BURN_FRAMES = Math.ceil(10 / PREDICTION_DT);

// Worker state
let predictionBuffer = null;
let bodiesMasses = null;

// --- Simulation ----------------------------------------------------------------

// Integrate one craft from `launchFrame`, released at `releaseAngle` around its source
// body, optionally applying a burn of `burnDur` frames at angle `burnAng` starting
// `burnStart` frames after release.
//
// Returns the flight plus its closest approach to the destination. Bails out early once
// the craft has plainly captured and left again — with earliest arrival as the goal
// there is nothing to gain from watching it recede, and the saving compounds across the
// hundreds of integrations the optimizer runs per angle.
function simulateFlight(params, releaseAngle, burnStart, burnDur, burnAng) {
    const {
        launchFrame, sourceBodyIndex, destBodyIndex, destBodyRadius,
        orbitRadius, orbitalSpeed, escapeVelocity, orbitalDirection
    } = params;

    if (launchFrame >= predictionBuffer.length) return null;

    const bodyState = predictionBuffer[launchFrame][sourceBodyIndex];

    let x = bodyState.x + orbitRadius * Math.cos(releaseAngle);
    let y = bodyState.y + orbitRadius * Math.sin(releaseAngle);
    let vx = bodyState.vx - orbitalDirection * orbitalSpeed * Math.sin(releaseAngle);
    let vy = bodyState.vy + orbitalDirection * orbitalSpeed * Math.cos(releaseAngle);
    let isAccelerating = true;

    const idealDistance = destBodyRadius + CRAFT_ORBITAL_ALTITUDE;
    const captureDistance = idealDistance + POST_OPTIMIZATION_THRESHOLD;

    const lastFrame = Math.min(predictionBuffer.length, launchFrame + MAX_TRANSFER_FRAMES);
    const states = [];
    const distances = [];

    let minDistance = Infinity;
    let insertionOffset = 0;

    for (let frame = launchFrame; frame < lastFrame; frame++) {
        const offset = frame - launchFrame;
        const bodyStates = predictionBuffer[frame];

        let ax = 0;
        let ay = 0;

        for (let i = 0; i < bodyStates.length; i++) {
            const s = bodyStates[i];
            const dx = s.x - x;
            const dy = s.y - y;
            const dist = Math.sqrt(dx * dx + dy * dy);
            const safeDist = Math.max(dist, MIN_DISTANCE);
            const acceleration = G * bodiesMasses[i] / (safeDist * safeDist);
            ax += acceleration * (dx / dist);
            ay += acceleration * (dy / dist);
        }

        // Prograde burn out of the source orbit, until clear of it
        if (isAccelerating) {
            const src = bodyStates[sourceBodyIndex];
            const dx = x - src.x;
            const dy = y - src.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            ax += CRAFT_ACCELERATION * (-orbitalDirection * dy / dist);
            ay += CRAFT_ACCELERATION * (orbitalDirection * dx / dist);

            const relVx = vx - src.vx;
            const relVy = vy - src.vy;
            if (Math.sqrt(relVx * relVx + relVy * relVy) >= 1.1 * escapeVelocity) {
                isAccelerating = false;
            }
        }

        // The tunable burn
        if (offset >= burnStart && offset < burnStart + burnDur) {
            ax += CRAFT_ACCELERATION * Math.cos(burnAng);
            ay += CRAFT_ACCELERATION * Math.sin(burnAng);
        }

        vx += ax * PREDICTION_DT;
        vy += ay * PREDICTION_DT;
        x += vx * PREDICTION_DT;
        y += vy * PREDICTION_DT;

        states.push({ x, y, vx, vy, isAccelerating });

        const dest = bodyStates[destBodyIndex];
        const ddx = x - dest.x;
        const ddy = y - dest.y;
        const dist = Math.sqrt(ddx * ddx + ddy * ddy);
        distances.push(dist);

        if (dist < minDistance) {
            minDistance = dist;
            insertionOffset = offset;
        }

        // Captured and now well clear again: the arrival we were looking for has already
        // happened, so stop paying for the departure. Never cut in before the witness
        // window has been filled, or the saving would manufacture exactly the phantom
        // arrivals captureError() exists to reject.
        if (minDistance <= captureDistance &&
            dist > minDistance * 4 &&
            offset >= insertionOffset + CAPTURE_WITNESS_FRAMES) {
            break;
        }
    }

    if (states.length === 0) return null;

    return { states, distances, minDistance, insertionOffset, idealDistance };
}

// Frames after closest approach that must be inspected before we will call it a capture.
const CAPTURE_WITNESS_FRAMES = 20;

// Mean altitude error over the frames just after closest approach. Averaging rather than
// taking the single closest point is what distinguishes a craft that settles alongside
// the destination from one that merely clips past it at the right distance.
//
// A flight whose closest approach lands at the very end of the simulated window is
// rejected outright. There, the average has only a frame or two to work with and reports
// a tiny error simply because we stopped watching — every candidate that ran to the
// 200-minute cap looked like a perfect arrival for that reason alone. Not witnessing a
// departure is not the same as witnessing a capture.
function captureError(flight) {
    if (!flight || flight.minDistance === Infinity) return Infinity;

    const available = flight.distances.length - flight.insertionOffset;
    if (available < CAPTURE_WITNESS_FRAMES) return Infinity;

    let total = 0;
    for (let i = flight.insertionOffset; i < flight.insertionOffset + CAPTURE_WITNESS_FRAMES; i++) {
        total += Math.abs(flight.distances[i] - flight.idealDistance);
    }
    return total / CAPTURE_WITNESS_FRAMES;
}

// --- Optimization --------------------------------------------------------------

// Weight on infeasibility, in frames per unit of altitude error. Large enough that any
// improvement in capture beats any improvement in arrival time while we are still
// missing the target, so the descent finds its way into the feasible region first.
const FEASIBILITY_WEIGHT = 500;

// Weight on residual error once already feasible, in frames per unit. Deliberately small:
// a whole unit of altitude error is worth less than a single frame of arrival, so among
// trajectories that all capture cleanly the earliest one wins. It exists only to give the
// descent a gradient to follow when arrival — an integer count of frames — goes flat.
const QUALITY_WEIGHT = 0.05;

function objective(flight) {
    if (!flight) return Infinity;
    const error = captureError(flight);
    if (error === Infinity) return Infinity;

    const excess = Math.max(0, error - POST_OPTIMIZATION_THRESHOLD);
    return flight.insertionOffset
        + FEASIBILITY_WEIGHT * excess
        + QUALITY_WEIGHT * Math.min(error, POST_OPTIMIZATION_THRESHOLD);
}

// Tune the post-escape burn for the earliest arrival that still captures.
//
// All three parameters are free — when the burn starts, which way it points, and how long
// it lasts. The old search fixed the start at two thirds of the way to arrival, which is
// a fine guess and nothing more; here it is only the seed. Freeing it is what lets the
// optimizer trade a slightly earlier, longer burn for an arrival a few minutes sooner.
//
// Coordinate descent, coarse to fine. The schedule matters more than the method: the old
// optimizer stepped the angle by a fixed 0.1 degrees and needed thousands of integrations
// to cross a degree, where halving from 8 degrees reaches the same precision in tens.
function optimizeBurn(params, releaseAngle, seedInsertion) {
    // Retrograde at the seed point is the burn that slows you into an orbit, which is the
    // right guess often enough to save the descent a lot of wandering.
    let start = Math.max(1, Math.floor(seedInsertion * 2 / 3));
    let dur = 1;

    const seed = simulateFlight(params, releaseAngle, start, 0, 0);
    if (!seed) return null;
    const at = seed.states[Math.min(start, seed.states.length - 1)];
    let ang = Math.atan2(at.vy, at.vx) + Math.PI;

    let best = simulateFlight(params, releaseAngle, start, dur, ang);
    let bestScore = objective(best);

    // (angle step in radians, duration step in frames, burn-start step in frames)
    const SCHEDULE = [
        [8 * Math.PI / 180, 16, 64],
        [2 * Math.PI / 180, 4, 16],
        [0.5 * Math.PI / 180, 1, 4],
        [0.1 * Math.PI / 180, 1, 1],
    ];

    const maxStart = Math.max(1, Math.min(seedInsertion * 2, MAX_TRANSFER_FRAMES - 1));

    for (const [angStep, durStep, startStep] of SCHEDULE) {
        let improved = true;
        let guard = 0;
        while (improved && guard++ < 200) {
            improved = false;

            for (const d of [-angStep, angStep]) {
                const trial = simulateFlight(params, releaseAngle, start, dur, ang + d);
                const score = objective(trial);
                if (score < bestScore) {
                    bestScore = score; ang += d; best = trial; improved = true;
                }
            }

            for (const d of [-durStep, durStep]) {
                const testDur = Math.max(0, Math.min(MAX_BURN_FRAMES, dur + d));
                if (testDur === dur) continue;
                const trial = simulateFlight(params, releaseAngle, start, testDur, ang);
                const score = objective(trial);
                if (score < bestScore) {
                    bestScore = score; dur = testDur; best = trial; improved = true;
                }
            }

            for (const d of [-startStep, startStep]) {
                const testStart = Math.max(0, Math.min(maxStart, start + d));
                if (testStart === start) continue;
                const trial = simulateFlight(params, releaseAngle, testStart, dur, ang);
                const score = objective(trial);
                if (score < bestScore) {
                    bestScore = score; start = testStart; best = trial; improved = true;
                }
            }
        }
    }

    if (!best) return null;
    return { flight: best, burnStart: start, burnDuration: dur, burnAngle: ang, error: captureError(best) };
}

// --- Scan ----------------------------------------------------------------------

// How much of a trajectory to ship back for drawing. The main thread re-integrates the
// one the player commits to at full resolution, so the fan only needs enough points to
// read as a curve — sending every frame of every viable angle would move megabytes per
// scrub of the time wheel.
const PATH_SAMPLE_INTERVAL = 4;

function samplePath(states) {
    const path = [];
    for (let i = 0; i < states.length; i += PATH_SAMPLE_INTERVAL) {
        path.push({ x: states[i].x, y: states[i].y });
    }
    const last = states[states.length - 1];
    if (path.length === 0 || path[path.length - 1].x !== last.x || path[path.length - 1].y !== last.y) {
        path.push({ x: last.x, y: last.y });
    }
    return path;
}

// Scan this worker's share of the release circle's sectors.
//
// Each worker takes every Nth sector, and within its own sectors runs the cheap pass —
// one burn-free integration per sampled angle — to find the most promising angle there,
// then optimizes just that one. Sectors are interleaved rather than handed out in blocks
// so a worker that draws an unreachable arc is not left idle while another grinds through
// the good one.
function scanAngles(params, shardIndex, shardCount, angleCount) {
    const angleOf = (i) => (i / angleCount) * 2 * Math.PI;
    const perSector = Math.max(1, Math.round(angleCount / ANGLE_SECTORS));

    const results = [];
    let examined = 0;
    let optimized = 0;

    for (let sector = shardIndex; sector < ANGLE_SECTORS; sector += shardCount) {
        // Cheap pass across this sector: how close does each release angle get on its
        // own, with no burn?
        let bestIndex = -1;
        let bestError = Infinity;
        let bestSeed = 0;

        for (let k = 0; k < perSector; k++) {
            const i = sector * perSector + k;
            if (i >= angleCount) break;
            examined++;
            const free = simulateFlight(params, angleOf(i), 0, 0, 0);
            if (!free || free.minDistance === Infinity) continue;
            const error = Math.abs(free.minDistance - free.idealDistance);
            if (error < bestError) {
                bestError = error;
                bestIndex = i;
                bestSeed = free.insertionOffset;
            }
        }

        if (bestIndex < 0) continue;

        const releaseAngle = angleOf(bestIndex);
        optimized++;
        const tuned = optimizeBurn(params, releaseAngle, bestSeed);
        if (!tuned || tuned.error > POST_OPTIMIZATION_THRESHOLD) continue;

        const flight = tuned.flight;
        if (flight.insertionOffset < MIN_TRANSFER_FRAMES) continue;

        // Trim at insertion: the flight is over once the craft is in orbit, and drawing
        // the coast past it would show a path the craft never takes.
        const states = flight.states.slice(0, flight.insertionOffset + 1);
        if (states.length < 2) continue;

        results.push({
            releaseAngle,
            arrivalOffset: flight.insertionOffset,
            error: tuned.error,
            burn: { start: tuned.burnStart, duration: tuned.burnDuration, angle: tuned.burnAngle },
            path: samplePath(states),
        });
    }

    return { results, examined, optimized };
}

// --- Messages -------------------------------------------------------------------

self.onmessage = function (e) {
    try {
        if (e.data.type === 'init') {
            predictionBuffer = e.data.predictionBuffer;
            bodiesMasses = e.data.bodiesMasses;
            self.postMessage({ type: 'ready' });
        } else if (e.data.type === 'scan') {
            const { params, shardIndex, shardCount, angleCount, generation } = e.data;
            const started = Date.now();
            const scan = scanAngles(params, shardIndex, shardCount, angleCount);
            self.postMessage({
                type: 'result',
                generation,
                shardIndex,
                elapsedMs: Date.now() - started,
                ...scan,
            });
        } else if (e.data.type === 'updateBuffer') {
            predictionBuffer = e.data.predictionBuffer;
            bodiesMasses = e.data.bodiesMasses;
        }
    } catch (err) {
        console.error('Worker error:', err);
        self.postMessage({ type: 'error', error: err.message, stack: err.stack });
    }
};
