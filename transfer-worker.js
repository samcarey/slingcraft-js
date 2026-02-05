// Transfer Search Web Worker
// Handles both trajectory search and correction optimization in parallel

// Physics constants (must match game.js)
const G = 50.0;
const MIN_DISTANCE = 10;
const CRAFT_ACCELERATION = 2.5;
const PREDICTION_DT = 0.033;
const CRAFT_ORBITAL_ALTITUDE = 5;

// Score thresholds for trajectory evaluation
const PRE_OPTIMIZATION_THRESHOLD = 20;  // Base score threshold to trigger correction optimization
const POST_OPTIMIZATION_THRESHOLD = 5;   // Corrected score threshold for acceptable trajectory

// Worker state
let predictionBuffer = null;
let bodiesMasses = null;

// Simulate craft trajectory from a launch frame
function simulateTrajectory(startFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity, orbitalDirection) {
    if (startFrame >= predictionBuffer.length) return [];

    const bodyState = predictionBuffer[startFrame][sourceBodyIndex];

    let state = {
        x: bodyState.x + orbitRadius * Math.cos(futureAngle),
        y: bodyState.y + orbitRadius * Math.sin(futureAngle),
        vx: bodyState.vx - orbitalDirection * orbitalSpeed * Math.sin(futureAngle),
        vy: bodyState.vy + orbitalDirection * orbitalSpeed * Math.cos(futureAngle),
        isAccelerating: true,
        escapeVelocity
    };

    const results = [];

    for (let frame = startFrame; frame < predictionBuffer.length; frame++) {
        const bodyStates = predictionBuffer[frame];

        let ax = 0;
        let ay = 0;

        for (let i = 0; i < bodyStates.length; i++) {
            const bodyStateI = bodyStates[i];
            const dx = bodyStateI.x - state.x;
            const dy = bodyStateI.y - state.y;
            const distSq = dx * dx + dy * dy;
            const dist = Math.sqrt(distSq);
            const safeDist = Math.max(dist, MIN_DISTANCE);

            const mass = bodiesMasses[i];
            const acceleration = G * mass / (safeDist * safeDist);
            ax += acceleration * (dx / dist);
            ay += acceleration * (dy / dist);
        }

        if (state.isAccelerating) {
            const launchBodyState = bodyStates[sourceBodyIndex];
            const dx = state.x - launchBodyState.x;
            const dy = state.y - launchBodyState.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            const accelDirX = -orbitalDirection * dy / dist;
            const accelDirY = orbitalDirection * dx / dist;

            ax += CRAFT_ACCELERATION * accelDirX;
            ay += CRAFT_ACCELERATION * accelDirY;

            const relVx = state.vx - launchBodyState.vx;
            const relVy = state.vy - launchBodyState.vy;
            const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
            if (relSpeed >= 1.1 * state.escapeVelocity) {
                state.isAccelerating = false;
            }
        }

        state.vx += ax * PREDICTION_DT;
        state.vy += ay * PREDICTION_DT;
        state.x += state.vx * PREDICTION_DT;
        state.y += state.vy * PREDICTION_DT;

        results.push({
            x: state.x,
            y: state.y,
            vx: state.vx,
            vy: state.vy,
            isAccelerating: state.isAccelerating
        });
    }

    return results;
}

// Score trajectory by closest approach to ideal orbital altitude
function scoreTrajectory(trajectory, destBodyIndex, destBodyRadius, startFrame) {
    if (destBodyIndex < 0) return { score: Infinity, insertionFrame: 0 };

    const idealDistance = destBodyRadius + CRAFT_ORBITAL_ALTITUDE;
    let minDistance = Infinity;
    let insertionFrame = 0;

    for (let i = 0; i < trajectory.length; i++) {
        const frameIndex = startFrame + i;
        if (frameIndex >= predictionBuffer.length) break;

        const craftPos = trajectory[i];
        const destPos = predictionBuffer[frameIndex][destBodyIndex];
        const dx = craftPos.x - destPos.x;
        const dy = craftPos.y - destPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);

        if (distance < minDistance) {
            minDistance = distance;
            insertionFrame = i;
        }
    }

    if (minDistance === Infinity) return { score: Infinity, insertionFrame: 0 };

    return { score: Math.abs(minDistance - idealDistance), insertionFrame };
}

// Score using average altitude error over 20 timesteps after insertion (for correction optimization)
function scoreCorrectedTrajectory(trajectory, destBodyIndex, destBodyRadius, startFrame) {
    if (destBodyIndex < 0) return { score: Infinity, insertionFrame: 0 };

    const idealDistance = destBodyRadius + CRAFT_ORBITAL_ALTITUDE;

    let minDistance = Infinity;
    let insertionFrame = 0;
    for (let i = 0; i < trajectory.length; i++) {
        const frameIndex = startFrame + i;
        if (frameIndex >= predictionBuffer.length) break;

        const craftPos = trajectory[i];
        const destPos = predictionBuffer[frameIndex][destBodyIndex];
        const dx = craftPos.x - destPos.x;
        const dy = craftPos.y - destPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);

        if (distance < minDistance) {
            minDistance = distance;
            insertionFrame = i;
        }
    }

    if (minDistance === Infinity) return { score: Infinity, insertionFrame: 0 };

    let totalError = 0;
    let count = 0;
    for (let i = insertionFrame; i < insertionFrame + 20 && i < trajectory.length; i++) {
        const frameIndex = startFrame + i;
        if (frameIndex >= predictionBuffer.length) break;

        const craftPos = trajectory[i];
        const destPos = predictionBuffer[frameIndex][destBodyIndex];
        const dx = craftPos.x - destPos.x;
        const dy = craftPos.y - destPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);

        totalError += Math.abs(distance - idealDistance);
        count++;
    }

    const avgError = count > 0 ? totalError / count : Infinity;
    return { score: avgError, insertionFrame };
}

// Simulate trajectory with correction boost
function simulateTrajectoryWithCorrection(
    startFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity,
    correctionStartOffset, correctionDur, correctionAng, orbitalDirection
) {
    if (startFrame >= predictionBuffer.length) return { trajectory: [], velocityAtCorrection: null };

    const bodyState = predictionBuffer[startFrame][sourceBodyIndex];

    let state = {
        x: bodyState.x + orbitRadius * Math.cos(futureAngle),
        y: bodyState.y + orbitRadius * Math.sin(futureAngle),
        vx: bodyState.vx - orbitalDirection * orbitalSpeed * Math.sin(futureAngle),
        vy: bodyState.vy + orbitalDirection * orbitalSpeed * Math.cos(futureAngle),
        isAccelerating: true,
        escapeVelocity
    };

    const results = [];
    let velocityAtCorrection = null;

    for (let frame = startFrame; frame < predictionBuffer.length; frame++) {
        const localFrame = frame - startFrame;
        const bodyStates = predictionBuffer[frame];

        if (localFrame === correctionStartOffset) {
            velocityAtCorrection = { vx: state.vx, vy: state.vy };
        }

        let ax = 0;
        let ay = 0;

        for (let i = 0; i < bodyStates.length; i++) {
            const bodyStateI = bodyStates[i];
            const dx = bodyStateI.x - state.x;
            const dy = bodyStateI.y - state.y;
            const distSq = dx * dx + dy * dy;
            const dist = Math.sqrt(distSq);
            const safeDist = Math.max(dist, MIN_DISTANCE);

            const mass = bodiesMasses[i];
            const acceleration = G * mass / (safeDist * safeDist);
            ax += acceleration * (dx / dist);
            ay += acceleration * (dy / dist);
        }

        if (state.isAccelerating) {
            const launchBodyState = bodyStates[sourceBodyIndex];
            const dx = state.x - launchBodyState.x;
            const dy = state.y - launchBodyState.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            const accelDirX = -orbitalDirection * dy / dist;
            const accelDirY = orbitalDirection * dx / dist;

            ax += CRAFT_ACCELERATION * accelDirX;
            ay += CRAFT_ACCELERATION * accelDirY;

            const relVx = state.vx - launchBodyState.vx;
            const relVy = state.vy - launchBodyState.vy;
            const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
            if (relSpeed >= 1.1 * state.escapeVelocity) {
                state.isAccelerating = false;
            }
        }

        if (localFrame >= correctionStartOffset && localFrame < correctionStartOffset + correctionDur) {
            ax += CRAFT_ACCELERATION * Math.cos(correctionAng);
            ay += CRAFT_ACCELERATION * Math.sin(correctionAng);
        }

        state.vx += ax * PREDICTION_DT;
        state.vy += ay * PREDICTION_DT;
        state.x += state.vx * PREDICTION_DT;
        state.y += state.vy * PREDICTION_DT;

        results.push({
            x: state.x,
            y: state.y,
            vx: state.vx,
            vy: state.vy,
            isAccelerating: state.isAccelerating
        });
    }

    return { trajectory: results, velocityAtCorrection };
}

// Run gradient descent optimization for correction boost
function optimizeCorrectionBoost(params, insertionFrame) {
    const {
        startFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity,
        destBodyIndex, destBodyRadius, orbitalDirection
    } = params;

    // Fixed start: 2/3 of the way to insertion
    const correctionStart = Math.floor(insertionFrame * 2 / 3);

    // First, simulate to get velocity at correction start point (with no correction)
    const initialResult = simulateTrajectoryWithCorrection(
        startFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity,
        correctionStart, 0, 0, orbitalDirection
    );

    if (!initialResult.velocityAtCorrection) {
        return { angle: 0, duration: 0, startFrame: correctionStart, score: Infinity, trajectory: initialResult.trajectory };
    }

    // Initialize angle to retrograde (opposite of velocity)
    const vel = initialResult.velocityAtCorrection;
    const velocityAngle = Math.atan2(vel.vy, vel.vx);
    let angle = velocityAngle + Math.PI;

    let duration = 1;

    const ANGLE_STEP = 0.1 * Math.PI / 180;
    const DURATION_STEP = 1;
    const MAX_DURATION = Math.ceil(10 / PREDICTION_DT);

    let currentResult = simulateTrajectoryWithCorrection(
        startFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity,
        correctionStart, duration, angle, orbitalDirection
    );
    let currentScore = scoreCorrectedTrajectory(currentResult.trajectory, destBodyIndex, destBodyRadius, startFrame);
    let bestScore = currentScore.score;
    let bestTrajectory = currentResult.trajectory;

    let iterationCount = 0;
    const MAX_ITERATIONS = 10000;

    let improved = true;
    while (improved && iterationCount < MAX_ITERATIONS) {
        improved = false;
        iterationCount++;

        for (const angleDelta of [-ANGLE_STEP, ANGLE_STEP]) {
            const testAngle = angle + angleDelta;
            const result = simulateTrajectoryWithCorrection(
                startFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity,
                correctionStart, duration, testAngle, orbitalDirection
            );
            const score = scoreCorrectedTrajectory(result.trajectory, destBodyIndex, destBodyRadius, startFrame);
            if (score.score < bestScore) {
                bestScore = score.score;
                angle = testAngle;
                bestTrajectory = result.trajectory;
                improved = true;
            }
        }

        for (const durationDelta of [-DURATION_STEP, DURATION_STEP]) {
            const testDuration = Math.max(0, Math.min(MAX_DURATION, duration + durationDelta));
            if (testDuration === duration) continue;

            const result = simulateTrajectoryWithCorrection(
                startFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity,
                correctionStart, testDuration, angle, orbitalDirection
            );
            const score = scoreCorrectedTrajectory(result.trajectory, destBodyIndex, destBodyRadius, startFrame);
            if (score.score < bestScore) {
                bestScore = score.score;
                duration = testDuration;
                bestTrajectory = result.trajectory;
                improved = true;
            }
        }
    }

    // Get the final insertion frame for the best trajectory
    const finalScoreResult = scoreCorrectedTrajectory(bestTrajectory, destBodyIndex, destBodyRadius, startFrame);
    const finalInsertionFrame = finalScoreResult.insertionFrame;

    // Truncate trajectory at insertion frame (include insertion point, nothing after)
    const truncatedTrajectory = bestTrajectory.slice(0, finalInsertionFrame + 1);

    return {
        angle,
        duration,
        startFrame: correctionStart,
        score: bestScore,
        trajectory: truncatedTrajectory,
        insertionFrame: finalInsertionFrame
    };
}

// Process a batch of launch frames
// Returns ALL acceptable trajectories found, plus the best non-acceptable for display
function processBatch(params, frameStart, frameEnd) {
    const {
        sourceBodyIndex, destBodyIndex, destBodyRadius,
        orbitRadius, orbitalSpeed, baseOrbitalAngle, angularVelocity, escapeVelocity,
        orbitalDirection
    } = params;

    const acceptableResults = [];   // All acceptable trajectories found
    let bestNonAcceptable = null;   // Best non-acceptable (by score) for display

    for (let launchFrame = frameStart; launchFrame < frameEnd && launchFrame < predictionBuffer.length; launchFrame++) {
        // Calculate orbital angle at this launch frame
        const futureAngle = baseOrbitalAngle + orbitalDirection * angularVelocity * launchFrame * PREDICTION_DT;

        // Simulate base trajectory
        const trajectory = simulateTrajectory(
            launchFrame, sourceBodyIndex, orbitRadius, orbitalSpeed, futureAngle, escapeVelocity, orbitalDirection
        );

        if (trajectory.length === 0) continue;

        // Score base trajectory
        const baseResult = scoreTrajectory(trajectory, destBodyIndex, destBodyRadius, launchFrame);

        // If base score meets pre-optimization threshold, try correction optimization
        if (baseResult.score <= PRE_OPTIMIZATION_THRESHOLD) {
            const correctionResult = optimizeCorrectionBoost({
                startFrame: launchFrame,
                sourceBodyIndex,
                orbitRadius,
                orbitalSpeed,
                futureAngle,
                escapeVelocity,
                destBodyIndex,
                destBodyRadius,
                orbitalDirection
            }, baseResult.insertionFrame);

            // If corrected score meets post-optimization threshold, this is acceptable
            if (correctionResult.score <= POST_OPTIMIZATION_THRESHOLD) {
                // Arrival frame = launch frame + trajectory length (trajectory already truncated at insertion)
                const arrivalFrame = launchFrame + correctionResult.trajectory.length;

                // Add to list of acceptable trajectories
                acceptableResults.push({
                    launchFrame,
                    score: correctionResult.score,
                    trajectory: correctionResult.trajectory,
                    insertionFrame: correctionResult.insertionFrame,
                    arrivalFrame,
                    correction: {
                        angle: correctionResult.angle,
                        duration: correctionResult.duration,
                        startFrame: correctionResult.startFrame
                    },
                    acceptable: true
                });
            } else {
                // Correction didn't help enough - track as non-acceptable
                if (!bestNonAcceptable || correctionResult.score < bestNonAcceptable.score) {
                    bestNonAcceptable = {
                        launchFrame,
                        score: correctionResult.score,
                        trajectory: correctionResult.trajectory,
                        insertionFrame: correctionResult.insertionFrame,
                        arrivalFrame: launchFrame + correctionResult.trajectory.length,
                        correction: {
                            angle: correctionResult.angle,
                            duration: correctionResult.duration,
                            startFrame: correctionResult.startFrame
                        },
                        acceptable: false
                    };
                }
            }
        } else {
            // Track best non-acceptable for display purposes (no correction attempted)
            if (!bestNonAcceptable || baseResult.score < bestNonAcceptable.score) {
                // Truncate trajectory at insertion frame
                const truncatedTrajectory = trajectory.slice(0, baseResult.insertionFrame + 1);
                bestNonAcceptable = {
                    launchFrame,
                    score: baseResult.score,
                    trajectory: truncatedTrajectory,
                    insertionFrame: baseResult.insertionFrame,
                    arrivalFrame: launchFrame + truncatedTrajectory.length,
                    correction: null,
                    acceptable: false
                };
            }
        }
    }

    // Return all acceptable trajectories and the best non-acceptable
    return {
        acceptableResults,
        bestNonAcceptable
    };
}

// Message handler
self.onmessage = function(e) {
    try {
        if (e.data.type === 'init') {
            // Initialize with prediction buffer and body masses
            predictionBuffer = e.data.predictionBuffer;
            bodiesMasses = e.data.bodiesMasses;
            self.postMessage({ type: 'ready' });
        } else if (e.data.type === 'search') {
            // Process a batch of frames
            const result = processBatch(e.data.params, e.data.frameStart, e.data.frameEnd);
            self.postMessage({
                type: 'result',
                batchId: e.data.batchId,
                generation: e.data.generation,
                frameStart: e.data.frameStart,
                frameEnd: e.data.frameEnd,
                result
            });
        } else if (e.data.type === 'updateBuffer') {
            // Update prediction buffer (for when it shifts)
            predictionBuffer = e.data.predictionBuffer;
            bodiesMasses = e.data.bodiesMasses;
        }
    } catch (err) {
        console.error('Worker error:', err);
        self.postMessage({
            type: 'error',
            error: err.message,
            stack: err.stack
        });
    }
};
