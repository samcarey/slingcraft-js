// SlingCraft - JavaScript Version (SVG Rendering)
// A space simulation with N-body gravitational physics

const svg = document.getElementById('game-svg');
const gridLayer = document.getElementById('grid-layer');
const trajectoriesLayer = document.getElementById('trajectories-layer');
const bodiesLayer = document.getElementById('bodies-layer');
const uiLayer = document.getElementById('ui-layer');
const defs = svg.querySelector('defs');

// Constants
const G = 50.0; // Gravitational constant
const MIN_DISTANCE = 10; // Minimum distance to prevent singularities
const DENSITY = 0.001; // Default density for mass calculation

// Prediction constants
const PREDICTION_TIME = 360; // Predict 360 seconds ahead
const SOLID_PREDICTION_TIME = 320; // First 320 seconds are solid
const PREDICTION_DT = 0.033; // Fixed timestep for prediction (~30fps)
const PREDICTION_FRAMES = Math.ceil(PREDICTION_TIME / PREDICTION_DT);
const SOLID_PREDICTION_FRAMES = Math.ceil(SOLID_PREDICTION_TIME / PREDICTION_DT);
const FADE_PREDICTION_FRAMES = PREDICTION_FRAMES - SOLID_PREDICTION_FRAMES;
const MAX_TRAJECTORY_POINTS = 100; // Max points to render for solid portion
const MAX_CATCHUP_FRAMES = 5; // Max frames to simulate per render frame

// Craft constants
const CRAFT_ORBITAL_ALTITUDE = 5;  // Simulation units above body surface
const CRAFT_ACCELERATION = 2.5;    // Tunable acceleration magnitude
const CRAFT_DOT_RADIUS = 3;        // Visual size in screen pixels

// Game state
let bodies = [];
let crafts = [];
let selectedBody = null;
let hoveredBody = null;
let isPaused = false;
let lastTime = 0;
// Transfer planning state
let transferState = 'none'; // 'none', 'selecting_destination', 'searching', 'ready', 'scheduled'
let transferSourceBody = null;
let transferDestinationBody = null;
let transferCraft = null;
let transferSearchFrame = 0;
let transferBestScore = Infinity;
let transferBestFrame = -1;
let transferBestTrajectory = null;
let transferTrajectorySampleOffset = 0; // Sample offset when trajectory was captured
let transferScheduledFrame = -1; // Frame index in buffer when launch should occur
let transferWorseCount = 0; // Counter for consecutive worse scores

// Camera/view state
let camera = {
    x: 0,
    y: 0,
    zoom: 1
};

// Zoom limits
const MIN_ZOOM = 0.1;
const MAX_ZOOM = 5;

// Drag state for panning
let isDragging = false;
let dragStart = { x: 0, y: 0 };
let cameraStart = { x: 0, y: 0 };

// Auto-fit state - paused when user manually pans/zooms
let isAutoFitPaused = false;

// Track whether we're actively following the selected body
let isTrackingSelectedBody = true;

// Prediction state
// predictionBuffer[frameIndex][bodyIndex] = {x, y, vx, vy}
let predictionBuffer = [];
let predictionTimeAccum = 0; // Accumulated time for popping frames
let sampleOffset = 0; // Offset for consistent trajectory sampling

// SVG namespace
const SVG_NS = 'http://www.w3.org/2000/svg';

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
        this.crafts = 0;

        // Mass based on volume and density
        this.mass = DENSITY * (4/3) * Math.PI * Math.pow(radius, 3);

        // SVG elements (created when body is added to scene)
        this.group = null;
        this.glowElement = null;
        this.circleElement = null;
        this.labelElement = null;
        this.trajectoryPath = null;
        this.trajectoryFadeGroup = null; // Group for fade segments with per-segment opacity
        this.trajectoryFadeColor = null;
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
            <stop offset="25%" stop-color="${this.color}" stop-opacity="0.25"/>
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

        // Create label
        this.labelElement = document.createElementNS(SVG_NS, 'text');
        this.labelElement.setAttribute('class', 'body-label');
        this.labelElement.textContent = this.name;
        this.group.appendChild(this.labelElement);

        bodiesLayer.appendChild(this.group);

        // Create trajectory path for solid portion (in trajectories layer)
        this.trajectoryPath = document.createElementNS(SVG_NS, 'path');
        this.trajectoryPath.setAttribute('class', 'trajectory-path');
        // Mix planet color with theme trajectory-mix color for visibility
        const strokeColor = `color-mix(in srgb, ${this.color} 70%, var(--trajectory-mix))`;
        this.trajectoryPath.style.stroke = strokeColor;
        this.trajectoryPath.style.opacity = '0.6';
        trajectoriesLayer.appendChild(this.trajectoryPath);

        // Create container group for fade segments (opacity per-segment based on time)
        this.trajectoryFadeGroup = document.createElementNS(SVG_NS, 'g');
        this.trajectoryFadeGroup.setAttribute('class', 'trajectory-fade-group');
        this.trajectoryFadeColor = strokeColor;
        trajectoriesLayer.appendChild(this.trajectoryFadeGroup);
    }

    updateElements() {
        const screen = worldToScreen(this.x, this.y);
        const screenRadius = this.radius * camera.zoom;

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

        // Update label position
        this.labelElement.setAttribute('x', screen.x);
        this.labelElement.setAttribute('y', screen.y + screenRadius + 16);
    }

    removeElements() {
        if (this.group) {
            this.group.remove();
        }
        if (this.trajectoryPath) {
            this.trajectoryPath.remove();
        }
        if (this.trajectoryFadeGroup) {
            this.trajectoryFadeGroup.remove();
        }
        // Remove glow gradient from defs
        const gradient = defs.querySelector(`#glow-${this.name}`);
        if (gradient) {
            gradient.remove();
        }
    }
}

// Craft class - spacecraft that can orbit bodies or fly freely
class Craft {
    constructor(parentBody, orbitalAltitude = CRAFT_ORBITAL_ALTITUDE) {
        this.state = 'orbiting'; // 'orbiting' or 'free'
        this.parentBody = parentBody;
        this.orbitalAltitude = orbitalAltitude;
        this.orbitalAngle = 0; // radians, 0 = right side

        // Free flight properties (used when state === 'free')
        this.x = 0;
        this.y = 0;
        this.vx = 0;
        this.vy = 0;

        // Acceleration phase
        this.isAccelerating = false;
        this.accelerationMagnitude = CRAFT_ACCELERATION;
        this.accelerationDirection = { x: 0, y: 0 }; // normalized
        this.escapeVelocity = 0; // set at launch
        this.launchedFromBody = null; // body we launched from (for escape velocity check)

        // Visual element
        this.element = null;

        // Trajectory elements (like CelestialBody)
        this.trajectoryPath = null;
        this.trajectoryFadeGroup = null;

        // Trajectory prediction buffer (used after launch, like body predictionBuffer)
        // Array of {x, y, vx, vy, isAccelerating} states
        this.trajectoryBuffer = [];
    }

    // Get current position (calculated from orbit or stored)
    getPosition() {
        if (this.state === 'orbiting') {
            const orbitRadius = this.parentBody.radius + this.orbitalAltitude;
            return {
                x: this.parentBody.x + orbitRadius * Math.cos(this.orbitalAngle),
                y: this.parentBody.y + orbitRadius * Math.sin(this.orbitalAngle)
            };
        } else {
            return { x: this.x, y: this.y };
        }
    }

    // Get current speed (relative to launch body for escape velocity check)
    getSpeed() {
        return Math.sqrt(this.vx * this.vx + this.vy * this.vy);
    }

    // Create SVG element for rendering
    createElements() {
        this.element = document.createElementNS(SVG_NS, 'circle');
        this.element.setAttribute('r', CRAFT_DOT_RADIUS);
        this.element.setAttribute('class', 'craft-dot');
        // Color handled by CSS (white dark theme, black light theme)
        bodiesLayer.appendChild(this.element);

        // Create trajectory path (solid portion)
        this.trajectoryPath = document.createElementNS(SVG_NS, 'path');
        this.trajectoryPath.setAttribute('class', 'trajectory-path craft-trajectory');
        // Color handled by CSS
        trajectoriesLayer.appendChild(this.trajectoryPath);

        // Create container group for fade segments
        this.trajectoryFadeGroup = document.createElementNS(SVG_NS, 'g');
        this.trajectoryFadeGroup.setAttribute('class', 'trajectory-fade-group');
        trajectoriesLayer.appendChild(this.trajectoryFadeGroup);
    }

    // Update SVG element position and state
    updateElements() {
        if (!this.element) return;

        const pos = this.getPosition();
        const screen = worldToScreen(pos.x, pos.y);

        this.element.setAttribute('cx', screen.x);
        this.element.setAttribute('cy', screen.y);

        // Toggle free class for blinking animation (only during acceleration)
        this.element.classList.toggle('free', this.isAccelerating);
    }

    // Remove SVG element
    removeElements() {
        if (this.element) {
            this.element.remove();
            this.element = null;
        }
        if (this.trajectoryPath) {
            this.trajectoryPath.remove();
            this.trajectoryPath = null;
        }
        if (this.trajectoryFadeGroup) {
            this.trajectoryFadeGroup.remove();
            this.trajectoryFadeGroup = null;
        }
    }

    // Launch from orbit into free flight
    launch() {
        if (this.state !== 'orbiting') return;

        const body = this.parentBody;
        const orbitRadius = body.radius + this.orbitalAltitude;

        // Calculate current position from orbit
        this.x = body.x + orbitRadius * Math.cos(this.orbitalAngle);
        this.y = body.y + orbitRadius * Math.sin(this.orbitalAngle);

        // Calculate orbital velocity (tangent to orbit, clockwise)
        // Clockwise in screen coords means angle increases
        // Velocity is derivative of position: d/dt[r*cos(θ)] = -r*sin(θ)*dθ/dt
        const orbitalSpeed = Math.sqrt(G * body.mass / orbitRadius);
        // For clockwise (dθ/dt > 0): vx = -speed*sin(θ), vy = +speed*cos(θ)
        this.vx = body.vx - orbitalSpeed * Math.sin(this.orbitalAngle);
        this.vy = body.vy + orbitalSpeed * Math.cos(this.orbitalAngle);

        // Set escape velocity target (2x escape velocity from this orbit)
        this.escapeVelocity = Math.sqrt(2 * G * body.mass / orbitRadius);
        this.launchedFromBody = body;

        // Set acceleration direction (prograde - same as velocity direction)
        const speed = this.getSpeed();
        if (speed > 0) {
            this.accelerationDirection = { x: this.vx / speed, y: this.vy / speed };
        }

        // Change state
        this.state = 'free';
        this.isAccelerating = true;

        // Populate trajectory buffer for prediction
        this.trajectoryBuffer = simulateCraftTrajectoryBuffer(this);
    }
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

    // Remove old craft elements
    for (const craft of crafts) {
        craft.removeElements();
    }
    crafts = [];

    // Central large body (like a star/planet)
    const central = new CelestialBody(0, 0, 80, '#ffaa44', 'Sol');
    central.mass = 1000;
    central.createElements();
    bodies.push(central);

    // Ember - inner planet orbiting Sol
    const ember = new CelestialBody(300, 0, 15, '#dd6644', 'Ember');
    ember.mass = 20;
    const emberDist = 300;
    ember.vy = Math.sqrt(G * central.mass / emberDist);
    ember.createElements();
    bodies.push(ember);

    // Add a craft to Ember
    const emberCraft = new Craft(ember);
    emberCraft.createElements();
    crafts.push(emberCraft);

    // Terra - orbiting Sol
    const terra = new CelestialBody(600, 0, 25, '#4488ff', 'Terra');
    terra.mass = 50;
    const terraDist = 600;
    terra.vy = Math.sqrt(G * central.mass / terraDist);
    terra.createElements();
    bodies.push(terra);

    // Luna - moon of Terra
    const luna = createMoon(terra, 50, -Math.PI / 2, 10, '#aaaaaa', 'Luna', 5);
    bodies.push(luna);

    // Gaia - orbiting Sol
    const gaia = new CelestialBody(-700, 0, 35, '#88ff88', 'Gaia');
    gaia.mass = 80;
    const gaiaDist = 700;
    gaia.vy = -Math.sqrt(G * central.mass / gaiaDist);
    gaia.createElements();
    bodies.push(gaia);
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

// Calculate center of mass
function calculateCenterOfMass() {
    let totalMass = 0;
    let comX = 0;
    let comY = 0;

    for (const body of bodies) {
        totalMass += body.mass;
        comX += body.x * body.mass;
        comY += body.y * body.mass;
    }

    return {
        x: comX / totalMass,
        y: comY / totalMass
    };
}

// Update physics - now driven by prediction buffer
// Bodies get their positions FROM the buffer, ensuring perfect sync
function updatePhysics(dt) {
    if (isPaused) return;

    const masses = getBodyMasses();

    // Initialize buffer if empty (first frame)
    if (predictionBuffer.length === 0) {
        // Start with current body states and build initial buffer
        let state = getBodyStates();
        for (let i = 0; i < MAX_CATCHUP_FRAMES && predictionBuffer.length < PREDICTION_FRAMES; i++) {
            state = simulateStep(state, masses, PREDICTION_DT);
            predictionBuffer.push(state);
        }
    }

    // Accumulate time and advance bodies when we have enough
    predictionTimeAccum += dt;
    while (predictionTimeAccum >= PREDICTION_DT && predictionBuffer.length > 0) {
        // Pop the front state and apply it to bodies
        const nextState = predictionBuffer.shift();
        for (let i = 0; i < bodies.length; i++) {
            bodies[i].x = nextState[i].x;
            bodies[i].y = nextState[i].y;
            bodies[i].vx = nextState[i].vx;
            bodies[i].vy = nextState[i].vy;
        }

        // Also pop and apply craft trajectory buffers (synced with body buffer)
        for (const craft of crafts) {
            if (craft.state === 'free' && craft.trajectoryBuffer.length > 0) {
                const craftState = craft.trajectoryBuffer.shift();
                craft.x = craftState.x;
                craft.y = craftState.y;
                craft.vx = craftState.vx;
                craft.vy = craftState.vy;
                craft.isAccelerating = craftState.isAccelerating;
            }
        }

        // Handle transfer frame indices when buffer shifts
        if (transferState === 'ready' || transferState === 'scheduled') {
            transferBestFrame--;

            // Handle scheduled launch
            if (transferState === 'scheduled') {
                transferScheduledFrame--;
                if (transferScheduledFrame <= 0 && transferCraft) {
                    // Execute the launch
                    transferCraft.launch();
                    resetTransferState();
                }
            }

            // If best frame passed and we're in ready state, restart search
            if (transferState === 'ready' && transferBestFrame <= 0) {
                startTransferSearch();
            }
            // Note: transferBestTrajectory stays fixed - it represents the complete planned path
        }

        predictionTimeAccum -= PREDICTION_DT;
        // Adjust sample offset to maintain consistent trajectory sampling
        // Decrement so we sample the same physical frames as buffer shifts
        sampleOffset = (sampleOffset - 1 + SAMPLE_INTERVAL) % SAMPLE_INTERVAL;
    }

    // Add new predictions to maintain buffer (max MAX_CATCHUP_FRAMES per call)
    let framesAdded = 0;
    while (predictionBuffer.length < PREDICTION_FRAMES && framesAdded < MAX_CATCHUP_FRAMES) {
        // Always extend from the last state in buffer
        const lastState = predictionBuffer.length > 0
            ? predictionBuffer[predictionBuffer.length - 1]
            : getBodyStates();

        const nextState = simulateStep(lastState, masses, PREDICTION_DT);
        predictionBuffer.push(nextState);
        framesAdded++;
    }
}

// Update craft physics (separate from body physics since craft don't affect prediction)
function updateCrafts(dt) {
    if (isPaused) return;

    for (const craft of crafts) {
        if (craft.state === 'orbiting') {
            // Update orbital angle (clockwise = positive direction in screen coords)
            const orbitRadius = craft.parentBody.radius + craft.orbitalAltitude;
            // Angular velocity = orbital speed / orbit radius
            const orbitalSpeed = Math.sqrt(G * craft.parentBody.mass / orbitRadius);
            const angularVelocity = orbitalSpeed / orbitRadius;
            craft.orbitalAngle += angularVelocity * dt;
            // Keep angle in [0, 2*PI] range
            if (craft.orbitalAngle > 2 * Math.PI) {
                craft.orbitalAngle -= 2 * Math.PI;
            }
        } else {
            // Free flight - position comes from trajectoryBuffer (popped in updatePhysics)
            // Here we just extend the buffer to maintain prediction length

            // Extend buffer to match predictionBuffer length
            while (craft.trajectoryBuffer.length < predictionBuffer.length && predictionBuffer.length > 0) {
                const lastState = craft.trajectoryBuffer.length > 0
                    ? craft.trajectoryBuffer[craft.trajectoryBuffer.length - 1]
                    : { x: craft.x, y: craft.y, vx: craft.vx, vy: craft.vy, isAccelerating: craft.isAccelerating };

                const frameIndex = craft.trajectoryBuffer.length;
                if (frameIndex < predictionBuffer.length) {
                    const bodyStates = predictionBuffer[frameIndex];
                    const nextState = simulateCraftStep(craft, lastState, bodyStates);
                    craft.trajectoryBuffer.push(nextState);
                }
            }
        }
    }
}

// Simulate craft trajectory using prediction buffer for body positions
// Returns array of {x, y} positions for each frame
function simulateCraftTrajectory(craft) {
    if (predictionBuffer.length === 0) return [];

    const results = [];
    const launchBodyIndex = bodies.indexOf(craft.state === 'orbiting' ? craft.parentBody : craft.launchedFromBody);

    // Get initial state
    let state;
    if (craft.state === 'orbiting') {
        // Starting from orbit - calculate launch state
        const body = craft.parentBody;
        const orbitRadius = body.radius + craft.orbitalAltitude;

        const x = body.x + orbitRadius * Math.cos(craft.orbitalAngle);
        const y = body.y + orbitRadius * Math.sin(craft.orbitalAngle);

        const orbitalSpeed = Math.sqrt(G * body.mass / orbitRadius);
        const vx = body.vx - orbitalSpeed * Math.sin(craft.orbitalAngle);
        const vy = body.vy + orbitalSpeed * Math.cos(craft.orbitalAngle);

        const escapeVelocity = Math.sqrt(2 * G * body.mass / orbitRadius);

        state = { x, y, vx, vy, isAccelerating: true, escapeVelocity };
    } else {
        // Starting from free flight
        state = {
            x: craft.x,
            y: craft.y,
            vx: craft.vx,
            vy: craft.vy,
            isAccelerating: craft.isAccelerating,
            escapeVelocity: craft.escapeVelocity
        };
    }

    // Simulate through prediction buffer
    for (let frame = 0; frame < predictionBuffer.length; frame++) {
        const bodyStates = predictionBuffer[frame];

        // Calculate gravity from all bodies
        let ax = 0;
        let ay = 0;

        for (let i = 0; i < bodyStates.length; i++) {
            const bodyState = bodyStates[i];
            const dx = bodyState.x - state.x;
            const dy = bodyState.y - state.y;
            const distSq = dx * dx + dy * dy;
            const dist = Math.sqrt(distSq);
            const safeDist = Math.max(dist, MIN_DISTANCE);

            const mass = bodies[i].mass;
            const acceleration = G * mass / (safeDist * safeDist);
            ax += acceleration * (dx / dist);
            ay += acceleration * (dy / dist);
        }

        // Apply craft acceleration if in acceleration phase
        if (state.isAccelerating && launchBodyIndex >= 0) {
            const launchBodyState = bodyStates[launchBodyIndex];
            const dx = state.x - launchBodyState.x;
            const dy = state.y - launchBodyState.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            // Perpendicular for clockwise (prograde): (-dy, dx) normalized
            const accelDirX = -dy / dist;
            const accelDirY = dx / dist;

            ax += CRAFT_ACCELERATION * accelDirX;
            ay += CRAFT_ACCELERATION * accelDirY;

            // Check if we've reached 2x escape velocity (relative to launch body)
            const relVx = state.vx - launchBodyState.vx;
            const relVy = state.vy - launchBodyState.vy;
            const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
            if (relSpeed >= 1.1 * state.escapeVelocity) {
                state.isAccelerating = false;
            }
        }

        // Update velocity and position
        state.vx += ax * PREDICTION_DT;
        state.vy += ay * PREDICTION_DT;
        state.x += state.vx * PREDICTION_DT;
        state.y += state.vy * PREDICTION_DT;

        results.push({ x: state.x, y: state.y });
    }

    return results;
}

// Simulate craft trajectory and return full state buffer (used after launch)
// Returns array of {x, y, vx, vy, isAccelerating} for each frame
function simulateCraftTrajectoryBuffer(craft) {
    if (predictionBuffer.length === 0) return [];

    const results = [];
    const launchBodyIndex = bodies.indexOf(craft.launchedFromBody);

    // Start from craft's current state
    let state = {
        x: craft.x,
        y: craft.y,
        vx: craft.vx,
        vy: craft.vy,
        isAccelerating: craft.isAccelerating,
        escapeVelocity: craft.escapeVelocity
    };

    // Simulate through prediction buffer
    for (let frame = 0; frame < predictionBuffer.length; frame++) {
        const bodyStates = predictionBuffer[frame];

        // Calculate gravity from all bodies
        let ax = 0;
        let ay = 0;

        for (let i = 0; i < bodyStates.length; i++) {
            const bodyState = bodyStates[i];
            const dx = bodyState.x - state.x;
            const dy = bodyState.y - state.y;
            const distSq = dx * dx + dy * dy;
            const dist = Math.sqrt(distSq);
            const safeDist = Math.max(dist, MIN_DISTANCE);

            const mass = bodies[i].mass;
            const acceleration = G * mass / (safeDist * safeDist);
            ax += acceleration * (dx / dist);
            ay += acceleration * (dy / dist);
        }

        // Apply craft acceleration if in acceleration phase
        if (state.isAccelerating && launchBodyIndex >= 0) {
            const launchBodyState = bodyStates[launchBodyIndex];
            const dx = state.x - launchBodyState.x;
            const dy = state.y - launchBodyState.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            const accelDirX = -dy / dist;
            const accelDirY = dx / dist;

            ax += CRAFT_ACCELERATION * accelDirX;
            ay += CRAFT_ACCELERATION * accelDirY;

            const relVx = state.vx - launchBodyState.vx;
            const relVy = state.vy - launchBodyState.vy;
            const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
            if (relSpeed >= 1.1 * state.escapeVelocity) {
                state.isAccelerating = false;
            }
        }

        // Update velocity and position
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

// Simulate one step forward for craft trajectory buffer extension
function simulateCraftStep(craft, lastState, bodyStates) {
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

    // Apply craft acceleration if in acceleration phase
    let isAccelerating = lastState.isAccelerating;
    if (isAccelerating && launchBodyIndex >= 0) {
        const launchBodyState = bodyStates[launchBodyIndex];
        const dx = lastState.x - launchBodyState.x;
        const dy = lastState.y - launchBodyState.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        const accelDirX = -dy / dist;
        const accelDirY = dx / dist;

        ax += CRAFT_ACCELERATION * accelDirX;
        ay += CRAFT_ACCELERATION * accelDirY;

        const relVx = lastState.vx - launchBodyState.vx;
        const relVy = lastState.vy - launchBodyState.vy;
        const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
        if (relSpeed >= 1.1 * craft.escapeVelocity) {
            isAccelerating = false;
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

// Score a transfer trajectory based on closest approach to destination's ideal orbital altitude
function scoreTrajectory(trajectory, destinationBody, startFrame) {
    const destIndex = bodies.indexOf(destinationBody);
    if (destIndex < 0) return Infinity;

    let minDistance = Infinity;

    // Find closest approach distance
    for (let i = 0; i < trajectory.length; i++) {
        const frameIndex = startFrame + i;
        if (frameIndex >= predictionBuffer.length) break;

        const craftPos = trajectory[i];
        const destPos = predictionBuffer[frameIndex][destIndex];

        const dx = craftPos.x - destPos.x;
        const dy = craftPos.y - destPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);

        minDistance = Math.min(minDistance, distance);
    }

    if (minDistance === Infinity) return Infinity;

    // Score = how far from ideal orbital altitude
    const idealDistance = destinationBody.radius + CRAFT_ORBITAL_ALTITUDE;
    return Math.abs(minDistance - idealDistance);
}

// Simulate craft trajectory starting from a future frame
function simulateCraftTrajectoryFromFrame(craft, startFrame) {
    if (startFrame >= predictionBuffer.length) return [];

    const sourceBody = craft.parentBody;
    const sourceBodyIndex = bodies.indexOf(sourceBody);
    if (sourceBodyIndex < 0) return [];

    // Calculate orbital angle at startFrame
    const orbitRadius = sourceBody.radius + craft.orbitalAltitude;
    const orbitalSpeed = Math.sqrt(G * sourceBody.mass / orbitRadius);
    const angularVelocity = orbitalSpeed / orbitRadius;
    const futureAngle = craft.orbitalAngle + angularVelocity * startFrame * PREDICTION_DT;

    // Get body state at startFrame
    const bodyState = predictionBuffer[startFrame][sourceBodyIndex];

    // Calculate craft position and velocity at launch
    const x = bodyState.x + orbitRadius * Math.cos(futureAngle);
    const y = bodyState.y + orbitRadius * Math.sin(futureAngle);
    const vx = bodyState.vx - orbitalSpeed * Math.sin(futureAngle);
    const vy = bodyState.vy + orbitalSpeed * Math.cos(futureAngle);
    const escapeVelocity = Math.sqrt(2 * G * sourceBody.mass / orbitRadius);

    // Simulate from startFrame onwards
    const results = [];
    let state = { x, y, vx, vy, isAccelerating: true, escapeVelocity };

    for (let frame = startFrame; frame < predictionBuffer.length; frame++) {
        const bodyStates = predictionBuffer[frame];

        // Calculate gravity from all bodies
        let ax = 0;
        let ay = 0;

        for (let i = 0; i < bodyStates.length; i++) {
            const bodyStateI = bodyStates[i];
            const dx = bodyStateI.x - state.x;
            const dy = bodyStateI.y - state.y;
            const distSq = dx * dx + dy * dy;
            const dist = Math.sqrt(distSq);
            const safeDist = Math.max(dist, MIN_DISTANCE);

            const mass = bodies[i].mass;
            const acceleration = G * mass / (safeDist * safeDist);
            ax += acceleration * (dx / dist);
            ay += acceleration * (dy / dist);
        }

        // Apply craft acceleration if in acceleration phase
        if (state.isAccelerating) {
            const launchBodyState = bodyStates[sourceBodyIndex];
            const dx = state.x - launchBodyState.x;
            const dy = state.y - launchBodyState.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            // Perpendicular for clockwise (prograde): (-dy, dx) normalized
            const accelDirX = -dy / dist;
            const accelDirY = dx / dist;

            ax += CRAFT_ACCELERATION * accelDirX;
            ay += CRAFT_ACCELERATION * accelDirY;

            // Check if we've reached escape velocity target
            const relVx = state.vx - launchBodyState.vx;
            const relVy = state.vy - launchBodyState.vy;
            const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
            if (relSpeed >= 1.1 * state.escapeVelocity) {
                state.isAccelerating = false;
            }
        }

        // Update velocity and position
        state.vx += ax * PREDICTION_DT;
        state.vy += ay * PREDICTION_DT;
        state.x += state.vx * PREDICTION_DT;
        state.y += state.vy * PREDICTION_DT;

        results.push({ x: state.x, y: state.y });
    }

    return results;
}

// Process transfer search (called from game loop)
function updateTransferSearch() {
    if (transferState !== 'searching') return;
    if (!transferCraft || !transferDestinationBody) {
        resetTransferState();
        return;
    }

    // Process frames per tick (slower to show progress)
    const FRAMES_PER_TICK = 50;
    // Require multiple consecutive worse scores to confirm optimum
    const WORSE_FRAMES_REQUIRED = 100;
    // Maximum acceptable score - skip trajectories above this
    const MAX_ACCEPTABLE_SCORE = 10;

    for (let i = 0; i < FRAMES_PER_TICK && transferSearchFrame < predictionBuffer.length; i++) {
        const trajectory = simulateCraftTrajectoryFromFrame(transferCraft, transferSearchFrame);
        if (trajectory.length === 0) {
            transferSearchFrame++;
            continue;
        }

        const score = scoreTrajectory(trajectory, transferDestinationBody, transferSearchFrame);

        // Track best trajectory found (even if score > 10, for display purposes)
        if (score < transferBestScore) {
            transferBestScore = score;
            transferBestFrame = transferSearchFrame;
            transferBestTrajectory = trajectory;
            transferTrajectorySampleOffset = sampleOffset; // Capture sample offset for consistent rendering
            transferWorseCount = 0; // Reset worse counter
        } else {
            transferWorseCount++;
            // Only declare optimum if we have a good score AND enough consecutive worse frames
            if (transferBestScore <= MAX_ACCEPTABLE_SCORE && transferWorseCount >= WORSE_FRAMES_REQUIRED) {
                transferState = 'ready';
                return;
            }
        }

        transferSearchFrame++;
    }

    // Reached end of buffer - restart search from beginning
    if (transferSearchFrame >= predictionBuffer.length) {
        // If we found a good trajectory (score <= 10), go to ready state
        if (transferBestFrame >= 0 && transferBestScore <= MAX_ACCEPTABLE_SCORE) {
            transferState = 'ready';
        } else {
            // Keep searching - restart from beginning (with 5 second skip)
            transferSearchFrame = TRANSFER_SEARCH_MIN_FRAMES;
            // Don't reset best score/frame - keep showing best found so far
        }
    }
}

// Minimum time in the future to start searching (5 seconds)
const TRANSFER_SEARCH_MIN_TIME = 5;
const TRANSFER_SEARCH_MIN_FRAMES = Math.ceil(TRANSFER_SEARCH_MIN_TIME / PREDICTION_DT);

// Start transfer search process
function startTransferSearch() {
    transferState = 'searching';
    transferSearchFrame = TRANSFER_SEARCH_MIN_FRAMES; // Start 5 seconds in the future
    transferBestScore = Infinity;
    transferBestFrame = -1;
    transferBestTrajectory = null;
    transferTrajectorySampleOffset = 0;
    transferWorseCount = 0;
}

// Reset transfer state
function resetTransferState() {
    transferState = 'none';
    transferSourceBody = null;
    transferDestinationBody = null;
    transferCraft = null;
    transferSearchFrame = 0;
    transferBestScore = Infinity;
    transferBestFrame = -1;
    transferBestTrajectory = null;
    transferTrajectorySampleOffset = 0;
    transferScheduledFrame = -1;
    transferWorseCount = 0;
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

// Fixed sample interval for trajectory rendering
const SAMPLE_INTERVAL = Math.ceil(SOLID_PREDICTION_FRAMES / MAX_TRAJECTORY_POINTS);

// Update trajectory path elements with current predictions
function updateTrajectories() {
    if (predictionBuffer.length === 0) return;

    // Build path for each body
    for (let bodyIndex = 0; bodyIndex < bodies.length; bodyIndex++) {
        const body = bodies[bodyIndex];
        if (!body.trajectoryPath) continue;

        // Collect all sampled points from the buffer (starting from sampleOffset for consistency)
        const points = [];

        // Always include first point if not already selected by sampling
        if (sampleOffset !== 0 && predictionBuffer.length > 0) {
            const state = predictionBuffer[0][bodyIndex];
            points.push({
                screen: worldToScreen(state.x, state.y),
                frame: 0
            });
        }

        // Collect downsampled points
        for (let i = sampleOffset; i < predictionBuffer.length; i += SAMPLE_INTERVAL) {
            const state = predictionBuffer[i][bodyIndex];
            points.push({
                screen: worldToScreen(state.x, state.y),
                frame: i
            });
        }

        // Always include last point if not already selected by sampling
        const lastFrame = predictionBuffer.length - 1;
        if (lastFrame >= 0 && (points.length === 0 || points[points.length - 1].frame !== lastFrame)) {
            const state = predictionBuffer[lastFrame][bodyIndex];
            points.push({
                screen: worldToScreen(state.x, state.y),
                frame: lastFrame
            });
        }

        // Calculate fade start based on current buffer length (fade is always at the end)
        const fadeStartFrame = Math.max(0, predictionBuffer.length - FADE_PREDICTION_FRAMES);

        // Build solid portion path (everything before fade)
        const startScreen = worldToScreen(body.x, body.y);
        let solidPath = `M ${startScreen.x} ${startScreen.y}`;

        let lastSolidPoint = null;
        for (const point of points) {
            if (point.frame >= fadeStartFrame) break;
            solidPath += ` L ${point.screen.x} ${point.screen.y}`;
            lastSolidPoint = point;
        }
        body.trajectoryPath.setAttribute('d', solidPath);

        // Build fade segments with per-segment opacity based on temporal position
        if (!body.trajectoryFadeGroup) continue;

        // Get fade points
        const fadePoints = points.filter(p => p.frame >= fadeStartFrame);

        // Clear existing segments
        body.trajectoryFadeGroup.innerHTML = '';

        if (fadePoints.length === 0) continue;

        // Build array of all points for fade segments (including connection from solid)
        const allFadePoints = lastSolidPoint ? [lastSolidPoint, ...fadePoints] : fadePoints;

        // Create line segments with opacity based on frame position
        const fadeLength = predictionBuffer.length - fadeStartFrame;
        for (let i = 0; i < allFadePoints.length - 1; i++) {
            const p1 = allFadePoints[i];
            const p2 = allFadePoints[i + 1];

            // Calculate opacity based on midpoint frame position within fade region
            const midFrame = (p1.frame + p2.frame) / 2;
            const fadeProgress = Math.max(0, (midFrame - fadeStartFrame) / fadeLength);
            const opacity = 0.6 * (1 - fadeProgress);

            const line = document.createElementNS(SVG_NS, 'line');
            line.setAttribute('x1', p1.screen.x);
            line.setAttribute('y1', p1.screen.y);
            line.setAttribute('x2', p2.screen.x);
            line.setAttribute('y2', p2.screen.y);
            line.setAttribute('class', 'trajectory-path');
            line.style.stroke = body.trajectoryFadeColor;
            line.style.opacity = opacity;
            line.style.strokeLinecap = 'butt';
            body.trajectoryFadeGroup.appendChild(line);
        }
    }

    // Render craft trajectories
    for (const craft of crafts) {
        if (!craft.trajectoryPath) continue;

        // Check if this is the transfer craft and we're showing transfer trajectory
        const isTransferCraft = craft === transferCraft;
        const showTransferTrajectory = isTransferCraft && (transferState === 'ready' || transferState === 'scheduled') && transferBestTrajectory;

        // Skip if orbiting and not showing transfer trajectory
        if (craft.state === 'orbiting' && !showTransferTrajectory) {
            // Hide trajectory
            craft.trajectoryPath.setAttribute('d', '');
            craft.trajectoryFadeGroup.innerHTML = '';
            continue;
        }

        // Get trajectory prediction:
        // - If showing transfer trajectory: use transferBestTrajectory
        // - If free: use pre-calculated buffer (like bodies)
        let craftPrediction;
        if (showTransferTrajectory) {
            craftPrediction = transferBestTrajectory;
        } else {
            craftPrediction = craft.trajectoryBuffer;
        }
        if (craftPrediction.length === 0) continue;

        // Collect sampled points (similar to body trajectories)
        const points = [];

        // Use captured sample offset for transfer trajectory, regular offset for others
        const effectiveSampleOffset = showTransferTrajectory ? transferTrajectorySampleOffset : sampleOffset;

        // Always include first point if not already selected by sampling
        if (effectiveSampleOffset !== 0 && craftPrediction.length > 0) {
            const pos = craftPrediction[0];
            points.push({
                screen: worldToScreen(pos.x, pos.y),
                frame: 0
            });
        }

        // Collect downsampled points
        for (let i = effectiveSampleOffset; i < craftPrediction.length; i += SAMPLE_INTERVAL) {
            const pos = craftPrediction[i];
            points.push({
                screen: worldToScreen(pos.x, pos.y),
                frame: i
            });
        }

        // Always include last point
        const lastFrame = craftPrediction.length - 1;
        if (lastFrame >= 0 && (points.length === 0 || points[points.length - 1].frame !== lastFrame)) {
            const pos = craftPrediction[lastFrame];
            points.push({
                screen: worldToScreen(pos.x, pos.y),
                frame: lastFrame
            });
        }

        // Calculate fade start
        const fadeStartFrame = Math.max(0, craftPrediction.length - FADE_PREDICTION_FRAMES);

        // Build solid portion path
        // For transfer trajectory, start from first point of trajectory (future position)
        // For regular trajectory, start from craft's current position
        let startScreen;
        if (showTransferTrajectory && craftPrediction.length > 0) {
            startScreen = worldToScreen(craftPrediction[0].x, craftPrediction[0].y);
        } else {
            const craftPos = craft.getPosition();
            startScreen = worldToScreen(craftPos.x, craftPos.y);
        }
        let solidPath = `M ${startScreen.x} ${startScreen.y}`;

        let lastSolidPoint = null;
        for (const point of points) {
            if (point.frame >= fadeStartFrame) break;
            solidPath += ` L ${point.screen.x} ${point.screen.y}`;
            lastSolidPoint = point;
        }
        craft.trajectoryPath.setAttribute('d', solidPath);

        // Build fade segments
        if (!craft.trajectoryFadeGroup) continue;

        const fadePoints = points.filter(p => p.frame >= fadeStartFrame);
        craft.trajectoryFadeGroup.innerHTML = '';

        if (fadePoints.length === 0) continue;

        const allFadePoints = lastSolidPoint ? [lastSolidPoint, ...fadePoints] : fadePoints;
        const fadeLength = craftPrediction.length - fadeStartFrame;

        for (let i = 0; i < allFadePoints.length - 1; i++) {
            const p1 = allFadePoints[i];
            const p2 = allFadePoints[i + 1];

            const midFrame = (p1.frame + p2.frame) / 2;
            const fadeProgress = Math.max(0, (midFrame - fadeStartFrame) / fadeLength);
            const opacity = 0.6 * (1 - fadeProgress);

            const line = document.createElementNS(SVG_NS, 'line');
            line.setAttribute('x1', p1.screen.x);
            line.setAttribute('y1', p1.screen.y);
            line.setAttribute('x2', p2.screen.x);
            line.setAttribute('y2', p2.screen.y);
            line.setAttribute('class', 'trajectory-path craft-trajectory');
            line.style.opacity = opacity;
            line.style.strokeLinecap = 'butt';
            craft.trajectoryFadeGroup.appendChild(line);
        }
    }
}

// Convert world coordinates to screen coordinates
function worldToScreen(x, y) {
    const rect = svg.getBoundingClientRect();
    return {
        x: (x - camera.x) * camera.zoom + rect.width / 2,
        y: (y - camera.y) * camera.zoom + rect.height / 2
    };
}

// Convert screen coordinates to world coordinates
function screenToWorld(screenX, screenY) {
    const rect = svg.getBoundingClientRect();
    return {
        x: (screenX - rect.width / 2) / camera.zoom + camera.x,
        y: (screenY - rect.height / 2) / camera.zoom + camera.y
    };
}

// Center of mass marker
let comMarker = null;

function createComMarker() {
    comMarker = document.createElementNS(SVG_NS, 'circle');
    comMarker.setAttribute('class', 'center-of-mass');
    comMarker.setAttribute('r', 3);
    uiLayer.appendChild(comMarker);
}

function updateComMarker() {
    const com = calculateCenterOfMass();
    const screen = worldToScreen(com.x, com.y);
    comMarker.setAttribute('cx', screen.x);
    comMarker.setAttribute('cy', screen.y);
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

    const rect = svg.getBoundingClientRect();
    const width = rect.width;
    const height = rect.height;

    // Calculate visible world bounds
    const topLeft = screenToWorld(0, 0);
    const bottomRight = screenToWorld(width, height);

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

        // Draw vertical lines
        for (let x = startX; x <= endX; x += spacing) {
            const screenX = worldToScreen(x, 0).x;
            const line = document.createElementNS(SVG_NS, 'line');
            line.setAttribute('class', 'grid-line');
            line.setAttribute('x1', screenX);
            line.setAttribute('y1', 0);
            line.setAttribute('x2', screenX);
            line.setAttribute('y2', height);
            group.appendChild(line);
        }

        // Draw horizontal lines
        for (let y = startY; y <= endY; y += spacing) {
            const screenY = worldToScreen(0, y).y;
            const line = document.createElementNS(SVG_NS, 'line');
            line.setAttribute('class', 'grid-line');
            line.setAttribute('x1', 0);
            line.setAttribute('y1', screenY);
            line.setAttribute('x2', width);
            line.setAttribute('y2', screenY);
            group.appendChild(line);
        }

        gridLayer.appendChild(group);
    }
}

// Render the scene
function render() {
    // Render dynamic grid
    renderGrid();

    // Update center of mass marker
    updateComMarker();

    // Update bodies
    for (const body of bodies) {
        body.updateElements();
    }

    // Update crafts
    for (const craft of crafts) {
        craft.updateElements();
    }

    // Update info panel
    updateInfoPanel();
}

// Update info panel
function updateInfoPanel() {
    const energies = calculateEnergies();

    document.getElementById('kinetic-energy').textContent = energies.kinetic.toFixed(1);
    document.getElementById('potential-energy').textContent = energies.potential.toFixed(1);
    document.getElementById('total-energy').textContent = energies.total.toFixed(1);

    const infoDiv = document.getElementById('selected-body-info');

    // Handle transfer states
    if (transferState === 'selecting_destination') {
        // Show destination selection UI
        const currentState = infoDiv.dataset.transferState;
        if (currentState !== 'selecting_destination') {
            let bodyListHtml = '<h3>Select Destination</h3><div class="body-list">';
            for (const body of bodies) {
                if (body === transferSourceBody) continue; // Exclude source body
                bodyListHtml += `
                    <div class="body-list-item" data-body-name="${body.name}">
                        <span class="body-indicator" style="background-color: ${body.color}"></span>
                        <span class="body-name">${body.name}</span>
                    </div>
                `;
            }
            bodyListHtml += '</div>';
            bodyListHtml += '<button id="cancel-transfer-btn">Cancel</button>';
            infoDiv.innerHTML = bodyListHtml;
            infoDiv.dataset.transferState = 'selecting_destination';
            delete infoDiv.dataset.bodyName;
        }
        infoDiv.style.display = 'block';
        return;
    }

    if (transferState === 'searching') {
        // Show search progress and best score found so far
        const progress = Math.round((transferSearchFrame / predictionBuffer.length) * 100);
        const bestScoreText = transferBestScore === Infinity ? '--' : transferBestScore.toFixed(1);
        const currentState = infoDiv.dataset.transferState;

        // Build panel structure once, then update values
        if (currentState !== 'searching') {
            infoDiv.innerHTML = `
                <h3>Transfer to ${transferDestinationBody.name}</h3>
                <div class="info-row">
                    <span class="info-label">Searching:</span>
                    <span class="info-value" id="search-progress">${progress}%</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Best score:</span>
                    <span class="info-value" id="search-best-score">${bestScoreText}</span>
                </div>
                <button id="schedule-launch-btn" disabled>Schedule Launch</button>
                <button id="cancel-transfer-btn">Cancel</button>
            `;
            infoDiv.dataset.transferState = 'searching';
        } else {
            // Just update the values
            const progressEl = document.getElementById('search-progress');
            const scoreEl = document.getElementById('search-best-score');
            if (progressEl) progressEl.textContent = progress + '%';
            if (scoreEl) scoreEl.textContent = bestScoreText;
        }
        infoDiv.style.display = 'block';
        return;
    }

    if (transferState === 'ready') {
        // Show ready to launch UI with countdown
        const countdown = (transferBestFrame * PREDICTION_DT).toFixed(1);
        const currentState = infoDiv.dataset.transferState;

        // Only rebuild panel when state changes, not when countdown changes
        if (currentState !== 'ready') {
            infoDiv.innerHTML = `
                <h3>Transfer to ${transferDestinationBody.name}</h3>
                <div class="info-row">
                    <span class="info-label">Launch in:</span>
                    <span class="info-value" id="transfer-countdown">${countdown}s</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Best score:</span>
                    <span class="info-value">${transferBestScore.toFixed(1)}</span>
                </div>
                <button id="schedule-launch-btn">Schedule Launch</button>
                <button id="cancel-transfer-btn">Cancel</button>
            `;
            infoDiv.dataset.transferState = 'ready';
        } else {
            // Just update the countdown value
            const countdownEl = document.getElementById('transfer-countdown');
            if (countdownEl) countdownEl.textContent = countdown + 's';
        }
        infoDiv.style.display = 'block';
        return;
    }

    if (transferState === 'scheduled') {
        // Show scheduled launch UI with countdown
        const countdown = (transferScheduledFrame * PREDICTION_DT).toFixed(1);
        const currentState = infoDiv.dataset.transferState;

        // Only rebuild panel when state changes, not when countdown changes
        if (currentState !== 'scheduled') {
            infoDiv.innerHTML = `
                <h3>Launch Scheduled</h3>
                <div class="info-row">
                    <span class="info-label">To:</span>
                    <span class="info-value">${transferDestinationBody.name}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Launching in:</span>
                    <span class="info-value" id="scheduled-countdown">${countdown}s</span>
                </div>
                <button id="cancel-transfer-btn">Cancel Launch</button>
            `;
            infoDiv.dataset.transferState = 'scheduled';
        } else {
            // Just update the countdown value
            const countdownEl = document.getElementById('scheduled-countdown');
            if (countdownEl) countdownEl.textContent = countdown + 's';
        }
        infoDiv.style.display = 'block';
        return;
    }

    // Clear transfer state tracking when in 'none' state
    delete infoDiv.dataset.transferState;
    delete infoDiv.dataset.countdown;
    delete infoDiv.dataset.searchProgress;

    if (selectedBody) {
        // Count orbiting craft for this body
        const orbitingCraft = crafts.filter(c => c.parentBody === selectedBody && c.state === 'orbiting');
        const orbitingCraftCount = orbitingCraft.length;

        // Check if we need to rebuild the panel structure (different body selected or craft count changed)
        const currentBodyName = infoDiv.dataset.bodyName;
        const currentCraftCount = parseInt(infoDiv.dataset.craftCount || '0', 10);
        const needsRebuild = currentBodyName !== selectedBody.name || currentCraftCount !== orbitingCraftCount;

        if (needsRebuild) {
            let transferBtnHtml = '';
            if (orbitingCraftCount > 0) {
                transferBtnHtml = `<button id="transfer-btn">${orbitingCraftCount} craft - Transfer</button>`;
            }

            infoDiv.innerHTML = `
                ${transferBtnHtml}
                <h3><span class="body-indicator" style="background-color: ${selectedBody.color}"></span>${selectedBody.name}</h3>
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
            infoDiv.dataset.bodyName = selectedBody.name;
            infoDiv.dataset.craftCount = orbitingCraftCount;
        } else {
            // Just update the dynamic values without rebuilding
            const posEl = document.getElementById('info-position');
            const speedEl = document.getElementById('info-speed');
            const kineticEl = document.getElementById('info-kinetic');
            if (posEl) posEl.textContent = `(${selectedBody.x.toFixed(0)}, ${selectedBody.y.toFixed(0)})`;
            if (speedEl) speedEl.textContent = selectedBody.speed.toFixed(1);
            if (kineticEl) kineticEl.textContent = selectedBody.kineticEnergy.toFixed(1);
        }
        infoDiv.style.display = 'block';
    } else {
        // Show list of all bodies when none selected
        // Only rebuild if not already showing body list
        if (!infoDiv.querySelector('.body-list')) {
            let bodyListHtml = '<h3>Bodies</h3><div class="body-list">';
            for (const body of bodies) {
                bodyListHtml += `
                    <div class="body-list-item" data-body-name="${body.name}">
                        <span class="body-indicator" style="background-color: ${body.color}"></span>
                        <span class="body-name">${body.name}</span>
                    </div>
                `;
            }
            bodyListHtml += '</div>';
            infoDiv.innerHTML = bodyListHtml;
            // Clear dataset so we rebuild when selecting a body
            delete infoDiv.dataset.bodyName;
            delete infoDiv.dataset.craftCount;
        }
        infoDiv.style.display = 'block';
    }
}

// Launch one orbiting craft from a body
function launchCraft(body) {
    const craft = crafts.find(c => c.parentBody === body && c.state === 'orbiting');
    if (craft) {
        craft.launch();
    }
}

// Find body at screen position
function findBodyAtPosition(screenX, screenY) {
    const world = screenToWorld(screenX, screenY);

    for (const body of bodies) {
        const dx = world.x - body.x;
        const dy = world.y - body.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist <= body.radius + 10) {
            return body;
        }
    }

    return null;
}

// Event handlers
function handleMouseMove(e) {
    const rect = svg.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    if (isDragging) {
        // Pan the camera
        const dx = (x - dragStart.x) / camera.zoom;
        const dy = (y - dragStart.y) / camera.zoom;
        camera.x = cameraStart.x - dx;
        camera.y = cameraStart.y - dy;
        svg.style.cursor = 'grabbing';
    } else {
        hoveredBody = findBodyAtPosition(x, y);
        svg.style.cursor = hoveredBody ? 'pointer' : 'grab';
    }
}

function handleMouseDown(e) {
    const rect = svg.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    // Check if clicking on a body
    const clickedBody = findBodyAtPosition(x, y);

    if (!clickedBody) {
        // Start dragging to pan
        isDragging = true;
        dragStart = { x, y };
        cameraStart = { x: camera.x, y: camera.y };
        svg.style.cursor = 'grabbing';
    }
}

function handleMouseUp(e) {
    const rect = svg.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    if (isDragging) {
        // Check if this was a click (minimal movement) or a drag
        const dx = x - dragStart.x;
        const dy = y - dragStart.y;
        const moved = Math.sqrt(dx * dx + dy * dy);

        if (moved < 5) {
            // This was a click, deselect
            selectedBody = null;
        } else {
            // User actually panned - pause auto-fit and stop tracking selected body
            isAutoFitPaused = true;
            isTrackingSelectedBody = false;
        }
    } else {
        // Click on a body
        const clicked = findBodyAtPosition(x, y);

        // If selecting destination for transfer
        if (transferState === 'selecting_destination' && clicked && clicked !== transferSourceBody) {
            transferDestinationBody = clicked;
            startTransferSearch();
        } else {
            // Normal body selection
            selectedBody = clicked;
            if (clicked) {
                isTrackingSelectedBody = true;
            }
        }
    }

    isDragging = false;
    svg.style.cursor = hoveredBody ? 'pointer' : 'grab';
}

function handleWheel(e) {
    e.preventDefault();

    // User manually zooming - pause auto-fit
    isAutoFitPaused = true;

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
function fitAllBodies() {
    const rect = svg.getBoundingClientRect();
    const bbox = calculateBoundingBox();

    // Calculate center of bounding box
    const centerX = (bbox.minX + bbox.maxX) / 2;
    const centerY = (bbox.minY + bbox.maxY) / 2;

    // Calculate required zoom to fit all bodies with 20% margin
    const worldWidth = bbox.maxX - bbox.minX;
    const worldHeight = bbox.maxY - bbox.minY;
    const margin = 1.2; // 20% margin on each side = 1.4x total, but we use 1.2 for padding

    const zoomX = rect.width / (worldWidth * margin);
    const zoomY = rect.height / (worldHeight * margin);
    const targetZoom = Math.min(zoomX, zoomY, MAX_ZOOM);

    camera.x = centerX;
    camera.y = centerY;
    camera.zoom = Math.max(targetZoom, MIN_ZOOM);
}

// Reset auto-fit (called by Escape or Fit All button)
function resetAutoFit() {
    isAutoFitPaused = false;
    isTrackingSelectedBody = true;
    selectedBody = null;
}

// Update camera to track selected body or fit all
function updateCameraTracking() {
    if (isDragging) return;

    if (selectedBody && isTrackingSelectedBody) {
        // Track selected body
        camera.x = selectedBody.x;
        camera.y = selectedBody.y;
    } else if (!selectedBody && !isAutoFitPaused) {
        // Auto-fit all bodies when nothing selected
        fitAllBodies();
    }

    // Update Fit All button active state - active when auto-fitting (no body selected and not paused)
    const fitAllBtn = document.getElementById('fit-all-btn');
    const isAutoFitActive = !selectedBody && !isAutoFitPaused;
    fitAllBtn.classList.toggle('active', isAutoFitActive);
}

// Main game loop
function gameLoop(timestamp) {
    const dt = (timestamp - lastTime) / 1000;
    lastTime = timestamp;

    updatePhysics(dt);
    updateCrafts(dt);
    updateTransferSearch();
    updateCameraTracking();
    render();
    updateTrajectories();

    requestAnimationFrame(gameLoop);
}

// Initialize
function init() {
    svg.addEventListener('mousemove', handleMouseMove);
    svg.addEventListener('mousedown', handleMouseDown);
    svg.addEventListener('mouseup', handleMouseUp);
    svg.addEventListener('mouseleave', () => { isDragging = false; });
    svg.addEventListener('wheel', handleWheel, { passive: false });

    // Pause button
    document.getElementById('pause-btn').addEventListener('click', () => {
        isPaused = !isPaused;
        document.getElementById('pause-btn').textContent = isPaused ? '▶' : '⏸';
        document.getElementById('pause-btn').classList.toggle('active', isPaused);
    });

    // Reset button
    document.getElementById('reset-btn').addEventListener('click', () => {
        initBodies();
        resetPredictions();
        resetTransferState();
        selectedBody = null;
        hoveredBody = null;
        isAutoFitPaused = false;
        isTrackingSelectedBody = true;
        camera = { x: 0, y: 0, zoom: 1 };
    });

    // Fit All button - fit all bodies but keep selection
    document.getElementById('fit-all-btn').addEventListener('click', () => {
        isTrackingSelectedBody = false;
        isAutoFitPaused = false;
        fitAllBodies();
    });

    // Escape key to reset auto-fit
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') {
            resetAutoFit();
        }
    });

    // Body list and transfer button click handler (event delegation)
    document.getElementById('selected-body-info').addEventListener('click', (e) => {
        // Handle transfer button click
        if (e.target.id === 'transfer-btn' && selectedBody) {
            const craft = crafts.find(c => c.parentBody === selectedBody && c.state === 'orbiting');
            if (craft) {
                transferState = 'selecting_destination';
                transferSourceBody = selectedBody;
                transferCraft = craft;
            }
            return;
        }

        // Handle cancel button click
        if (e.target.id === 'cancel-transfer-btn') {
            resetTransferState();
            return;
        }

        // Handle schedule launch button click
        if (e.target.id === 'schedule-launch-btn' && transferState === 'ready') {
            transferState = 'scheduled';
            transferScheduledFrame = transferBestFrame;
            return;
        }

        // Handle body list item click
        const item = e.target.closest('.body-list-item');
        if (item) {
            const bodyName = item.dataset.bodyName;
            const body = bodies.find(b => b.name === bodyName);
            if (body) {
                // If selecting destination for transfer
                if (transferState === 'selecting_destination') {
                    transferDestinationBody = body;
                    startTransferSearch();
                } else {
                    // Normal body selection
                    selectedBody = body;
                    isTrackingSelectedBody = true;
                }
            }
        }
    });

    createComMarker();
    initBodies();

    lastTime = performance.now();
    requestAnimationFrame(gameLoop);
}

// Start the game
init();
