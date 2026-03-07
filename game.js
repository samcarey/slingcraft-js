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
const DENSITY = 0.00075; // Default density for mass calculation

// Prediction constants
const PREDICTION_TIME = 1800; // Predict 1800 minutes ahead
const SOLID_PREDICTION_TIME = 1600; // First 1600 minutes are solid
const PREDICTION_DT = 0.1; // Fixed timestep for prediction (minutes)
const PREDICTION_FRAMES = Math.ceil(PREDICTION_TIME / PREDICTION_DT);
const SOLID_PREDICTION_FRAMES = Math.ceil(SOLID_PREDICTION_TIME / PREDICTION_DT);
const FADE_PREDICTION_FRAMES = PREDICTION_FRAMES - SOLID_PREDICTION_FRAMES;
const PREDICTION_DT_DECIMALS = Math.max(0, -Math.floor(Math.log10(PREDICTION_DT))); // Display precision derived from timestep
const MAX_TRAJECTORY_POINTS = 200; // Max points to render for solid portion
const MAX_CATCHUP_FRAMES = 100; // Max frames to simulate per render frame

// Craft constants
const CRAFT_ORBITAL_ALTITUDE = 5;  // Simulation units above body surface
const CRAFT_ACCELERATION = 2.5;    // Tunable acceleration magnitude
const CRAFT_DOT_RADIUS = 3;        // Visual size in screen pixels

// Game state
let bodies = [];
let crafts = [];
let selectedBody = null;
let selectedCraft = null;
let infoTabActive = 'bodies'; // 'bodies' or 'trajectories'
let hoveredBody = null;
let bodyInfoExpanded = false;
let isPaused = false;
let speedMultiplier = 0.1 / 6; // 0.1 sim-minutes per 6 real seconds
let lastTime = 0;
// Time scrub state - offset in frames into the prediction buffer for viewing future positions
let timeViewOffset = 0; // 0 = current time, positive = looking into future
let timeScrubPanelOpen = false;
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
let transferInsertionFrame = 0; // Frame index within trajectory of optimal insertion
let transferBestArrivalFrame = Infinity; // Best arrival frame (launch + trajectory length)

// Correction boost state (stored in best result)
let correctionAngle = 0;           // Angle in radians
let correctionDuration = 0;        // Duration in timesteps
let correctionStartFrame = 0;      // Start frame (relative to trajectory start)

// Worker pool for parallel transfer search
let workerPool = [];               // Array of web workers
let workerBusy = [];               // Track which workers are busy
let workerPoolReady = false;       // Whether all workers are initialized
let searchBatchSize = 50;          // Frames per batch
let nextBatchStart = 0;            // Next frame to assign
let pendingBatches = 0;            // Number of batches still processing
let searchGeneration = 0;          // Incremented each search cycle to ignore stale results
let searchedUpToFrame = 0;         // Highest frame we've fully searched (for incremental search)
let initialSearchComplete = false; // Whether we've done one full pass of the search window
let bufferShiftsSinceInit = 0;     // Track buffer shifts since workers were initialized

// List of all acceptable trajectories found, sorted by arrival frame (earliest first)
// Each entry: { launchFrame, arrivalFrame, score, trajectory, insertionFrame, sampleOffset, correction }
let acceptableTrajectories = [];
let selectedTrajectoryIndex = 0; // Which trajectory in the list is currently selected

// Cache for transfer search results - keyed by "sourceBodyIndex-destBodyIndex"
// Stores valid results that can be reused when restarting searches
let transferCache = new Map();

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

// Track whether we're actively following the selected body
let isTrackingSelectedBody = true;

// Track whether we're actively following the selected craft's trajectory
let isTrackingSelectedCraft = false;

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
        this.trajectoryPath.style.opacity = '0.24';
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
        this.orbitalDirection = 1; // 1 = angle-increasing, -1 = angle-decreasing

        // Position and velocity (always kept in sync by syncToViewFrame)
        const orbitRadius = parentBody.radius + orbitalAltitude;
        this.x = parentBody.x + orbitRadius;
        this.y = parentBody.y;
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

        // Visual element
        this.element = null;

        // Trajectory elements (like CelestialBody)
        this.trajectoryPath = null;
        this.trajectoryFadeGroup = null;

        // Trajectory prediction buffer (used after launch, like body predictionBuffer)
        // Array of {x, y, vx, vy, isAccelerating} states
        this.trajectoryBuffer = [];
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
        this.element = document.createElementNS(SVG_NS, 'circle');
        this.element.setAttribute('r', CRAFT_DOT_RADIUS);
        this.element.setAttribute('class', 'craft-dot');
        // Color handled by CSS (white dark theme, black light theme)
        bodiesLayer.appendChild(this.element);

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
        // Color handled by CSS
        trajectoriesLayer.appendChild(this.trajectoryPath);

        // Create container group for fade segments
        this.trajectoryFadeGroup = document.createElementNS(SVG_NS, 'g');
        this.trajectoryFadeGroup.setAttribute('class', 'trajectory-fade-group');
        trajectoriesLayer.appendChild(this.trajectoryFadeGroup);

        // Create correction arrow (hidden by default)
        this.correctionArrow = document.createElementNS(SVG_NS, 'line');
        this.correctionArrow.setAttribute('stroke', 'red');
        this.correctionArrow.setAttribute('stroke-width', '3');
        this.correctionArrow.setAttribute('marker-end', 'url(#correction-arrowhead)');
        this.correctionArrow.style.display = 'none';
        bodiesLayer.appendChild(this.correctionArrow);

        // Create correction trajectory overlay (red dotted line)
        this.correctionOverlay = document.createElementNS(SVG_NS, 'path');
        this.correctionOverlay.setAttribute('stroke', 'red');
        this.correctionOverlay.setAttribute('stroke-width', '4');
        this.correctionOverlay.setAttribute('stroke-dasharray', '8,4');
        this.correctionOverlay.setAttribute('fill', 'none');
        this.correctionOverlay.style.display = 'none';
        trajectoriesLayer.appendChild(this.correctionOverlay);
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

        // Toggle in-transit class for selectability (only free-flying crafts)
        const inTransit = this.state === 'free';
        this.element.classList.toggle('in-transit', inTransit);

        // Toggle selected class
        const isSelected = selectedCraft === this;
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

    // Remove SVG element
    removeElements() {
        if (this.element) {
            this.element.remove();
            this.element = null;
        }
        if (this.trajectoryHitArea) {
            this.trajectoryHitArea.remove();
            this.trajectoryHitArea = null;
        }
        if (this.trajectoryPath) {
            this.trajectoryPath.remove();
            this.trajectoryPath = null;
        }
        if (this.trajectoryFadeGroup) {
            this.trajectoryFadeGroup.remove();
            this.trajectoryFadeGroup = null;
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

    // Launch from orbit into free flight
    launch() {
        if (this.state !== 'orbiting') return;

        const body = this.parentBody;
        const orbitRadius = body.radius + this.orbitalAltitude;

        // Calculate current position from orbit
        this.x = body.x + orbitRadius * Math.cos(this.orbitalAngle);
        this.y = body.y + orbitRadius * Math.sin(this.orbitalAngle);

        // Calculate orbital velocity (tangent to orbit)
        // Velocity is derivative of position: d/dt[r*cos(θ)] = -r*sin(θ)*dθ/dt
        const orbitalSpeed = Math.sqrt(G * body.mass / orbitRadius);
        // orbitalDirection determines sign of dθ/dt
        this.vx = body.vx - this.orbitalDirection * orbitalSpeed * Math.sin(this.orbitalAngle);
        this.vy = body.vy + this.orbitalDirection * orbitalSpeed * Math.cos(this.orbitalAngle);

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
        this.flightFrame = 0;
        this.isCorrecting = false;

        // Auto-select craft if its origin body was selected
        if (selectedBody === body) {
            selectedBody = null;
            selectedCraft = this;
            isTrackingSelectedBody = false;
            isTrackingSelectedCraft = true;
        }

        // Populate trajectory buffer for prediction
        this.trajectoryBuffer = simulateCraftTrajectoryBuffer(this);
    }

    // Launch with a pre-computed trajectory (from worker)
    // transferParams: {correctionParams, destinationBody, insertionFrame}
    launchWithTrajectory(trajectory, transferParams) {
        if (this.state !== 'orbiting') return;
        if (!trajectory || trajectory.length === 0) {
            // Fall back to regular launch
            this.launch();
            return;
        }

        const body = this.parentBody;
        const orbitRadius = body.radius + this.orbitalAltitude;

        // Use position and velocity from first frame of pre-computed trajectory
        const firstFrame = trajectory[0];
        this.x = firstFrame.x;
        this.y = firstFrame.y;
        this.vx = firstFrame.vx;
        this.vy = firstFrame.vy;

        // Set escape velocity target
        this.escapeVelocity = Math.sqrt(2 * G * body.mass / orbitRadius);
        this.launchedFromBody = body;

        // Set acceleration direction (prograde - same as velocity direction)
        const speed = this.getSpeed();
        if (speed > 0) {
            this.accelerationDirection = { x: this.vx / speed, y: this.vy / speed };
        }

        // Change state
        this.state = 'free';
        this.isAccelerating = firstFrame.isAccelerating !== undefined ? firstFrame.isAccelerating : true;
        this.flightFrame = 0;
        this.isCorrecting = false;

        // Auto-select craft if its origin body was selected
        if (selectedBody === body) {
            selectedBody = null;
            selectedCraft = this;
            isTrackingSelectedBody = false;
            isTrackingSelectedCraft = true;
        }

        // Store transfer parameters if provided
        if (transferParams) {
            this.correctionParams = transferParams.correctionParams || null;
            this.destinationBody = transferParams.destinationBody || null;
            this.insertionFrame = transferParams.insertionFrame || 0;
        } else {
            this.correctionParams = null;
            this.destinationBody = null;
            this.insertionFrame = 0;
        }

        // Use the pre-computed trajectory directly
        this.trajectoryBuffer = trajectory;
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
    central.mass = 18000;
    central.createElements();
    bodies.push(central);

    // Ember - inner planet orbiting Sol
    const ember = new CelestialBody(332.5, 0, 15, '#dd6644', 'Ember');
    ember.mass = 20;
    const emberDist = 332.5;
    ember.vy = Math.sqrt(G * central.mass / emberDist);
    ember.createElements();
    bodies.push(ember);

    // Add a craft to Ember
    const emberCraft = new Craft(ember);
    emberCraft.createElements();
    crafts.push(emberCraft);

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

// Advance timeline - manages the prediction buffer and advances the "present" marker.
// Does NOT set body/craft positions; that's done by syncToViewFrame().
function advanceTimeline(dt) {
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

    // Accumulate time and pop frames from front as present advances
    predictionTimeAccum += dt * speedMultiplier;
    while (predictionTimeAccum >= PREDICTION_DT && predictionBuffer.length > 0) {
        // Pop the front frame (present advances by one tick)
        predictionBuffer.shift();

        // Advance craft state for this tick
        for (const craft of crafts) {
            if (craft.state === 'orbiting') {
                // Advance base orbital angle by one tick
                const orbitRadius = craft.parentBody.radius + craft.orbitalAltitude;
                const orbitalSpeed = Math.sqrt(G * craft.parentBody.mass / orbitRadius);
                const angularVelocity = orbitalSpeed / orbitRadius;
                craft.orbitalAngle += craft.orbitalDirection * angularVelocity * PREDICTION_DT;
                // Normalize angle
                if (craft.orbitalAngle > 2 * Math.PI) craft.orbitalAngle -= 2 * Math.PI;
                else if (craft.orbitalAngle < 0) craft.orbitalAngle += 2 * Math.PI;
            } else if (craft.state === 'free' && craft.trajectoryBuffer.length > 0) {
                // Pop craft trajectory buffer (synced with body buffer)
                craft.trajectoryBuffer.shift();
                craft.flightFrame++;

                // Check for orbit insertion at end of transfer trajectory
                if (craft.trajectoryBuffer.length === 0 && craft.destinationBody) {
                    // Need body positions at present to compute insertion angle
                    // Use first frame in buffer (which is now the present after shift)
                    const presentState = predictionBuffer.length > 0 ? predictionBuffer[0] : null;
                    const destBody = craft.destinationBody;
                    const destIdx = bodies.indexOf(destBody);

                    // Get craft's last known position from the popped frame's end state
                    const lastTrajState = craft; // craft x/y still has old values; use them
                    // Actually we need the position at insertion. The trajectory buffer just ran out,
                    // so the craft's position is whatever it was last set to by syncToViewFrame.
                    // We need to get body position at present for the angle calculation.
                    let destX = destBody.x, destY = destBody.y;
                    let destVx = destBody.vx, destVy = destBody.vy;
                    if (presentState && destIdx >= 0) {
                        destX = presentState[destIdx].x;
                        destY = presentState[destIdx].y;
                        destVx = presentState[destIdx].vx;
                        destVy = presentState[destIdx].vy;
                    }

                    // Calculate orbital angle from craft position relative to destination
                    const dx = craft.x - destX;
                    const dy = craft.y - destY;
                    const orbitalAngle = Math.atan2(dy, dx);

                    // Determine orbit direction from incoming velocity
                    const relVx = craft.vx - destVx;
                    const relVy = craft.vy - destVy;
                    const cross = dx * relVy - dy * relVx;
                    const orbitalDirection = cross >= 0 ? 1 : -1;

                    // Transition to orbiting state
                    craft.state = 'orbiting';
                    craft.parentBody = destBody;
                    craft.orbitalAltitude = CRAFT_ORBITAL_ALTITUDE;
                    craft.orbitalAngle = orbitalAngle;
                    craft.orbitalDirection = orbitalDirection;

                    // Calculate proper orbital velocity
                    const orbitRadius = destBody.radius + CRAFT_ORBITAL_ALTITUDE;
                    const orbitalSpeed = Math.sqrt(G * destBody.mass / orbitRadius);
                    craft.vx = destVx - orbitalDirection * orbitalSpeed * Math.sin(orbitalAngle);
                    craft.vy = destVy + orbitalDirection * orbitalSpeed * Math.cos(orbitalAngle);

                    // Snap position to exact orbital altitude
                    craft.x = destX + orbitRadius * Math.cos(orbitalAngle);
                    craft.y = destY + orbitRadius * Math.sin(orbitalAngle);

                    // Clear transfer-related state
                    craft.destinationBody = null;
                    craft.insertionFrame = 0;
                    craft.correctionParams = null;
                    craft.isCorrecting = false;
                    craft.isAccelerating = false;
                    craft.launchedFromBody = null;
                    craft.escapeVelocity = 0;
                    craft.flightFrame = 0;

                    console.log(`Craft captured into orbit around ${destBody.name} at angle ${(orbitalAngle * 180 / Math.PI).toFixed(1)}° (${orbitalDirection === 1 ? 'prograde' : 'retrograde'})`);

                    // Select destination body if craft was selected
                    if (selectedCraft === craft) {
                        selectedCraft = null;
                        isTrackingSelectedCraft = false;
                        selectedBody = destBody;
                        isTrackingSelectedBody = true;
                    }
                }
            }
        }

        // Update transfer cache on buffer shift
        updateTransferCacheOnShift();

        // Track buffer shifts since workers were initialized (for adjusting incoming results)
        bufferShiftsSinceInit++;

        // Decrement time view offset so we keep looking at the same physical moment
        if (timeViewOffset > 0) {
            timeViewOffset = Math.max(0, timeViewOffset - 1);
        }

        // Handle transfer frame indices when buffer shifts
        if (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') {
            // Update the acceptable trajectories list (removes expired entries)
            updateAcceptableTrajectoriesOnShift();

            // Handle scheduled launch
            if (transferState === 'scheduled') {
                transferScheduledFrame--;
                if (transferScheduledFrame <= 0 && transferCraft) {
                    // Build transfer parameters
                    const transferParams = {
                        correctionParams: correctionDuration > 0 ? {
                            angle: correctionAngle,
                            duration: correctionDuration,
                            startFrame: correctionStartFrame
                        } : null,
                        destinationBody: transferDestinationBody,
                        insertionFrame: transferInsertionFrame
                    };
                    console.log('Launch! Transfer params:', transferParams);
                    // Execute the launch with pre-computed trajectory
                    transferCraft.launchWithTrajectory(transferBestTrajectory, transferParams);
                    resetTransferState();
                }
            } else {
                // Update best from the list (handles when best launch time passes)
                const hadAcceptable = updateBestFromList();

                // Update transfer state based on whether we have acceptable trajectories
                if (hadAcceptable && transferState === 'searching') {
                    transferState = 'ready';
                } else if (!hadAcceptable && transferState === 'ready') {
                    transferState = 'searching';
                }
            }
        }

        predictionTimeAccum = Math.max(0, predictionTimeAccum - PREDICTION_DT);
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

    // Set craft positions for the viewed frame
    for (const craft of crafts) {
        // Case 1: Orbiting craft with a scheduled transfer that has launched by the viewed frame
        if (craft.state === 'orbiting' && transferState === 'scheduled' && craft === transferCraft &&
            transferScheduledFrame > 0 && frameIndex >= transferScheduledFrame && transferBestTrajectory && transferBestTrajectory.length > 0) {
            const trajFrame = frameIndex - transferScheduledFrame;
            if (trajFrame < transferBestTrajectory.length) {
                // Craft is in transit — show trajectory position
                const futurePos = transferBestTrajectory[trajFrame];
                craft.x = futurePos.x;
                craft.y = futurePos.y;
                craft.vx = futurePos.vx;
                craft.vy = futurePos.vy;
            } else {
                // Trajectory ended — show craft orbiting destination body
                const destBody = transferDestinationBody;
                if (destBody) {
                    const insertIdx = Math.min(transferInsertionFrame, transferBestTrajectory.length - 1);
                    const insertBufferFrame = Math.min(transferScheduledFrame + insertIdx, predictionBuffer.length - 1);
                    const craftAtInsert = transferBestTrajectory[insertIdx];
                    const bodyAtInsert = predictionBuffer[insertBufferFrame][bodies.indexOf(destBody)];

                    const dx = craftAtInsert.x - bodyAtInsert.x;
                    const dy = craftAtInsert.y - bodyAtInsert.y;
                    const insertionAngle = Math.atan2(dy, dx);

                    const relVx = craftAtInsert.vx - bodyAtInsert.vx;
                    const relVy = craftAtInsert.vy - bodyAtInsert.vy;
                    const cross = dx * relVy - dy * relVx;
                    const orbitalDirection = cross >= 0 ? 1 : -1;

                    const orbitRadius = destBody.radius + CRAFT_ORBITAL_ALTITUDE;
                    const orbitalSpeed = Math.sqrt(G * destBody.mass / orbitRadius);
                    const angularVelocity = orbitalSpeed / orbitRadius;

                    const elapsedTime = (frameIndex - insertBufferFrame) * PREDICTION_DT;
                    const viewAngle = insertionAngle + orbitalDirection * angularVelocity * elapsedTime;

                    craft.x = destBody.x + orbitRadius * Math.cos(viewAngle);
                    craft.y = destBody.y + orbitRadius * Math.sin(viewAngle);
                }
            }
        }
        // Case 2: Orbiting craft (no transfer, or transfer hasn't launched yet)
        else if (craft.state === 'orbiting') {
            const orbitRadius = craft.parentBody.radius + craft.orbitalAltitude;
            const orbitalSpeed = Math.sqrt(G * craft.parentBody.mass / orbitRadius);
            const angularVelocity = orbitalSpeed / orbitRadius;
            // Compute viewed angle: base angle + offset for viewed frame (exact tick increments only)
            const viewAngle = craft.orbitalAngle + craft.orbitalDirection * angularVelocity * frameIndex * PREDICTION_DT;
            craft.x = craft.parentBody.x + orbitRadius * Math.cos(viewAngle);
            craft.y = craft.parentBody.y + orbitRadius * Math.sin(viewAngle);
        }
        // Case 3: Free-flying craft
        else if (craft.state === 'free' && craft.trajectoryBuffer.length > 0) {
            const craftFrame = Math.min(frameIndex, craft.trajectoryBuffer.length - 1);
            const futurePos = craft.trajectoryBuffer[craftFrame];
            craft.x = futurePos.x;
            craft.y = futurePos.y;
            craft.vx = futurePos.vx;
            craft.vy = futurePos.vy;

            // Set correction/acceleration flags for visual feedback at viewed frame
            craft.isAccelerating = futurePos.isAccelerating;
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

// Extend craft trajectory buffers to maintain prediction length.
// Orbital angle updates are handled by advanceTimeline (per-tick) and syncToViewFrame (for display).
function extendCraftBuffers() {
    if (isPaused) return;

    for (const craft of crafts) {
        if (craft.state === 'free' && !craft.destinationBody) {
            // Extend buffer to match predictionBuffer length (regular launch only)
            while (craft.trajectoryBuffer.length < predictionBuffer.length && predictionBuffer.length > 0) {
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
        const vx = body.vx - craft.orbitalDirection * orbitalSpeed * Math.sin(craft.orbitalAngle);
        const vy = body.vy + craft.orbitalDirection * orbitalSpeed * Math.cos(craft.orbitalAngle);

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

            // Perpendicular prograde direction based on orbitalDirection
            const accelDirX = -craft.orbitalDirection * dy / dist;
            const accelDirY = craft.orbitalDirection * dx / dist;

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

        // Apply craft acceleration if in escape acceleration phase
        if (state.isAccelerating && launchBodyIndex >= 0) {
            const launchBodyState = bodyStates[launchBodyIndex];
            const dx = state.x - launchBodyState.x;
            const dy = state.y - launchBodyState.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            const accelDirX = -craft.orbitalDirection * dy / dist;
            const accelDirY = craft.orbitalDirection * dx / dist;

            ax += CRAFT_ACCELERATION * accelDirX;
            ay += CRAFT_ACCELERATION * accelDirY;

            const relVx = state.vx - launchBodyState.vx;
            const relVy = state.vy - launchBodyState.vy;
            const relSpeed = Math.sqrt(relVx * relVx + relVy * relVy);
            if (relSpeed >= 1.1 * state.escapeVelocity) {
                state.isAccelerating = false;
            }
        }

        // Apply correction boost if in correction phase
        // frame equals flight frame since this is called at launch (flightFrame = 0)
        if (craft.correctionParams) {
            const params = craft.correctionParams;
            if (frame >= params.startFrame && frame < params.startFrame + params.duration) {
                ax += CRAFT_ACCELERATION * Math.cos(params.angle);
                ay += CRAFT_ACCELERATION * Math.sin(params.angle);
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

// Score a transfer trajectory based on closest approach to destination's ideal orbital altitude
// Returns { score, insertionFrame } where insertionFrame is the trajectory index of closest approach
function scoreTrajectory(trajectory, destinationBody, startFrame) {
    const destIndex = bodies.indexOf(destinationBody);
    if (destIndex < 0) return { score: Infinity, insertionFrame: 0 };

    let minDistance = Infinity;
    let insertionFrame = 0;

    // Find closest approach distance and frame
    for (let i = 0; i < trajectory.length; i++) {
        const frameIndex = startFrame + i;
        if (frameIndex >= predictionBuffer.length) break;

        const craftPos = trajectory[i];
        const destPos = predictionBuffer[frameIndex][destIndex];

        const dx = craftPos.x - destPos.x;
        const dy = craftPos.y - destPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);

        if (distance < minDistance) {
            minDistance = distance;
            insertionFrame = i;
        }
    }

    if (minDistance === Infinity) return { score: Infinity, insertionFrame: 0 };

    // Score = how far from ideal orbital altitude
    const idealDistance = destinationBody.radius + CRAFT_ORBITAL_ALTITUDE;
    return { score: Math.abs(minDistance - idealDistance), insertionFrame };
}

// Score a corrected trajectory using average altitude error over 20 timesteps after insertion
// This is used for correction boost optimization
function scoreCorrectedTrajectory(trajectory, destinationBody, startFrame) {
    const destIndex = bodies.indexOf(destinationBody);
    if (destIndex < 0) return { score: Infinity, insertionFrame: 0 };

    const idealDistance = destinationBody.radius + CRAFT_ORBITAL_ALTITUDE;

    // Find optimal insertion frame (closest approach)
    let minDistance = Infinity;
    let insertionFrame = 0;
    for (let i = 0; i < trajectory.length; i++) {
        const frameIndex = startFrame + i;
        if (frameIndex >= predictionBuffer.length) break;

        const craftPos = trajectory[i];
        const destPos = predictionBuffer[frameIndex][destIndex];
        const dx = craftPos.x - destPos.x;
        const dy = craftPos.y - destPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);

        if (distance < minDistance) {
            minDistance = distance;
            insertionFrame = i;
        }
    }

    if (minDistance === Infinity) return { score: Infinity, insertionFrame: 0 };

    // Average altitude error over 20 timesteps after insertion
    let totalError = 0;
    let count = 0;
    for (let i = insertionFrame; i < insertionFrame + 20 && i < trajectory.length; i++) {
        const frameIndex = startFrame + i;
        if (frameIndex >= predictionBuffer.length) break;

        const craftPos = trajectory[i];
        const destPos = predictionBuffer[frameIndex][destIndex];
        const dx = craftPos.x - destPos.x;
        const dy = craftPos.y - destPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);

        totalError += Math.abs(distance - idealDistance);
        count++;
    }

    const avgError = count > 0 ? totalError / count : Infinity;
    return { score: avgError, insertionFrame };
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
    const futureAngle = craft.orbitalAngle + craft.orbitalDirection * angularVelocity * startFrame * PREDICTION_DT;

    // Get body state at startFrame
    const bodyState = predictionBuffer[startFrame][sourceBodyIndex];

    // Calculate craft position and velocity at launch
    const x = bodyState.x + orbitRadius * Math.cos(futureAngle);
    const y = bodyState.y + orbitRadius * Math.sin(futureAngle);
    const vx = bodyState.vx - craft.orbitalDirection * orbitalSpeed * Math.sin(futureAngle);
    const vy = bodyState.vy + craft.orbitalDirection * orbitalSpeed * Math.cos(futureAngle);
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

            // Perpendicular prograde direction based on orbitalDirection
            const accelDirX = -craft.orbitalDirection * dy / dist;
            const accelDirY = craft.orbitalDirection * dx / dist;

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

// Simulate craft trajectory with correction boost applied
// correctionStartOffset: frame offset from startFrame to begin correction
// correctionDur: number of frames to apply correction
// correctionAng: angle (radians) of acceleration direction
// Returns array of {x, y} positions, plus velocity at correction start point
function simulateCraftTrajectoryWithCorrection(craft, startFrame, correctionStartOffset, correctionDur, correctionAng) {
    if (startFrame >= predictionBuffer.length) return { trajectory: [], velocityAtCorrection: null };

    const sourceBody = craft.parentBody;
    const sourceBodyIndex = bodies.indexOf(sourceBody);
    if (sourceBodyIndex < 0) return { trajectory: [], velocityAtCorrection: null };

    // Calculate orbital angle at startFrame
    const orbitRadius = sourceBody.radius + craft.orbitalAltitude;
    const orbitalSpeed = Math.sqrt(G * sourceBody.mass / orbitRadius);
    const angularVelocity = orbitalSpeed / orbitRadius;
    const futureAngle = craft.orbitalAngle + craft.orbitalDirection * angularVelocity * startFrame * PREDICTION_DT;

    // Get body state at startFrame
    const bodyState = predictionBuffer[startFrame][sourceBodyIndex];

    // Calculate craft position and velocity at launch
    const x = bodyState.x + orbitRadius * Math.cos(futureAngle);
    const y = bodyState.y + orbitRadius * Math.sin(futureAngle);
    const vx = bodyState.vx - craft.orbitalDirection * orbitalSpeed * Math.sin(futureAngle);
    const vy = bodyState.vy + craft.orbitalDirection * orbitalSpeed * Math.cos(futureAngle);
    const escapeVelocity = Math.sqrt(2 * G * sourceBody.mass / orbitRadius);

    // Simulate from startFrame onwards
    const results = [];
    let state = { x, y, vx, vy, isAccelerating: true, escapeVelocity };
    let velocityAtCorrection = null;

    for (let frame = startFrame; frame < predictionBuffer.length; frame++) {
        const localFrame = frame - startFrame;
        const bodyStates = predictionBuffer[frame];

        // Store velocity at correction start for computing retrograde angle
        if (localFrame === correctionStartOffset) {
            velocityAtCorrection = { vx: state.vx, vy: state.vy };
        }

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

        // Apply craft acceleration if in escape acceleration phase
        if (state.isAccelerating) {
            const launchBodyState = bodyStates[sourceBodyIndex];
            const dx = state.x - launchBodyState.x;
            const dy = state.y - launchBodyState.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            // Perpendicular prograde direction based on orbitalDirection
            const accelDirX = -craft.orbitalDirection * dy / dist;
            const accelDirY = craft.orbitalDirection * dx / dist;

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

        // Apply correction boost if in correction phase
        if (localFrame >= correctionStartOffset && localFrame < correctionStartOffset + correctionDur) {
            ax += CRAFT_ACCELERATION * Math.cos(correctionAng);
            ay += CRAFT_ACCELERATION * Math.sin(correctionAng);
        }

        // Update velocity and position
        state.vx += ax * PREDICTION_DT;
        state.vy += ay * PREDICTION_DT;
        state.x += state.vx * PREDICTION_DT;
        state.y += state.vy * PREDICTION_DT;

        results.push({ x: state.x, y: state.y });
    }

    return { trajectory: results, velocityAtCorrection };
}

// Initialize worker pool for parallel transfer search
function initWorkerPool() {
    const numWorkers = navigator.hardwareConcurrency || 4;
    workerPool = [];
    workerBusy = [];

    for (let i = 0; i < numWorkers; i++) {
        const worker = new Worker('transfer-worker.js');
        worker.onmessage = (e) => handleWorkerMessage(i, e);
        worker.onerror = (e) => {
            console.error('Worker', i, 'uncaught error:', e.message, e.filename, e.lineno);
            workerBusy[i] = false;
        };
        workerPool.push(worker);
        workerBusy.push(false);
    }

    workerPoolReady = false;
}

// Handle messages from transfer workers
function handleWorkerMessage(workerIndex, e) {
    if (e.data.type === 'error') {
        console.error('Worker', workerIndex, 'error:', e.data.error, e.data.stack);
        workerBusy[workerIndex] = false;
        return;
    }
    if (e.data.type === 'ready') {
        // Worker initialized, check if all ready
        workerBusy[workerIndex] = false;
        const allReady = workerBusy.every(b => !b);
        if (allReady) {
            workerPoolReady = true;
            // All workers ready, dispatch work to all of them
            // Continue searching in all active states (searching, ready, scheduled)
            if (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') {
                const maxLaunchFrame = predictionBuffer.length - MIN_TRAJECTORY_RUNWAY_FRAMES;
                // Ensure nextBatchStart is at least searchedUpToFrame (for incremental search)
                if (nextBatchStart < searchedUpToFrame) {
                    nextBatchStart = searchedUpToFrame;
                }
                for (let i = 0; i < workerPool.length; i++) {
                    if (!workerBusy[i] && nextBatchStart < maxLaunchFrame) {
                        dispatchNextBatch(i);
                    }
                }
            }
        }
    } else if (e.data.type === 'result') {
        workerBusy[workerIndex] = false;

        // Ignore stale results from previous searches
        if (e.data.generation !== searchGeneration) {
            return;
        }

        pendingBatches--;

        const batchResult = e.data.result;
        const batchEnd = e.data.frameEnd;
        const maxLaunchFrame = predictionBuffer.length - MIN_TRAJECTORY_RUNWAY_FRAMES;

        // Adjust batchEnd to current buffer coordinates
        const adjustedBatchEnd = batchEnd - bufferShiftsSinceInit;

        // Track how far we've searched (in current buffer coordinates)
        if (adjustedBatchEnd > searchedUpToFrame) {
            searchedUpToFrame = adjustedBatchEnd;
        }

        if (batchResult) {
            // Add ALL acceptable trajectories from this batch to the list
            // (addAcceptableTrajectory handles the shift adjustment internally)
            if (batchResult.acceptableResults && batchResult.acceptableResults.length > 0) {
                for (const result of batchResult.acceptableResults) {
                    addAcceptableTrajectory(result);
                }

                // Update best from list
                updateBestFromList();

                // Mark as ready once we have an acceptable trajectory
                if (transferState === 'searching') {
                    transferState = 'ready';
                }

                // Update trajectory plot with new data
                onAcceptableTrajectoriesChanged();

                // Save to cache for potential reuse
                saveToTransferCache();
            } else if (acceptableTrajectories.length === 0 && batchResult.bestNonAcceptable) {
                // No acceptable found yet - show best non-acceptable by score for display
                const result = batchResult.bestNonAcceptable;
                // Adjust buffer-relative frame numbers for buffer shift
                // insertionFrame is trajectory-relative, no adjustment needed
                const adjustedLaunchFrame = result.launchFrame - bufferShiftsSinceInit;

                if (adjustedLaunchFrame > 0 && (transferBestFrame < 0 || result.score < transferBestScore)) {
                    transferBestScore = result.score;
                    transferBestFrame = adjustedLaunchFrame;
                    transferBestTrajectory = result.trajectory;
                    transferInsertionFrame = result.insertionFrame;  // Trajectory-relative
                    transferBestArrivalFrame = Infinity;  // Keep as Infinity for non-acceptable
                    transferTrajectorySampleOffset = sampleOffset;

                    if (result.correction) {
                        correctionAngle = result.correction.angle;
                        correctionDuration = result.correction.duration;
                        correctionStartFrame = result.correction.startFrame;
                    } else {
                        correctionAngle = 0;
                        correctionDuration = 0;
                        correctionStartFrame = 0;
                    }
                }
            }
        }

        // Continue dispatching work - search continues in searching, ready, and scheduled states
        if ((transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') &&
            nextBatchStart < maxLaunchFrame) {
            dispatchNextBatch(workerIndex);
        }

        // Check if this search pass is complete
        if (pendingBatches === 0 && nextBatchStart >= maxLaunchFrame) {
            if (!initialSearchComplete) {
                initialSearchComplete = true;
            }
            // updateTransferSearch will trigger the next search cycle
        }
    }
}

// Dispatch a batch of frames to a worker
function dispatchNextBatch(workerIndex) {
    // Max launch frame: buffer length - 200s runway (to ensure full trajectory simulation)
    const maxLaunchFrame = predictionBuffer.length - MIN_TRAJECTORY_RUNWAY_FRAMES;
    if (nextBatchStart >= maxLaunchFrame) return;
    if (!transferCraft || !transferDestinationBody) return;

    const sourceBody = transferCraft.parentBody;
    const sourceBodyIndex = bodies.indexOf(sourceBody);
    const destBodyIndex = bodies.indexOf(transferDestinationBody);

    if (sourceBodyIndex < 0 || destBodyIndex < 0) return;

    const orbitRadius = sourceBody.radius + transferCraft.orbitalAltitude;
    const orbitalSpeed = Math.sqrt(G * sourceBody.mass / orbitRadius);
    const angularVelocity = orbitalSpeed / orbitRadius;
    const escapeVelocity = Math.sqrt(2 * G * sourceBody.mass / orbitRadius);

    const frameStart = nextBatchStart;
    const frameEnd = Math.min(nextBatchStart + searchBatchSize, maxLaunchFrame);
    nextBatchStart = frameEnd;

    workerBusy[workerIndex] = true;
    pendingBatches++;

    workerPool[workerIndex].postMessage({
        type: 'search',
        batchId: frameStart,
        generation: searchGeneration,
        frameStart,
        frameEnd,
        params: {
            sourceBodyIndex,
            destBodyIndex,
            destBodyRadius: transferDestinationBody.radius,
            orbitRadius,
            orbitalSpeed,
            baseOrbitalAngle: transferCraft.orbitalAngle,
            angularVelocity,
            escapeVelocity,
            orbitalDirection: transferCraft.orbitalDirection
        }
    });
}

// Start parallel search across all workers
function startParallelSearch() {
    if (!transferCraft || !transferDestinationBody) return;
    if (workerPool.length === 0) return;

    // Initialize all workers with current prediction buffer
    const bodiesMasses = bodies.map(b => b.mass);
    workerPoolReady = false;
    bufferShiftsSinceInit = 0;  // Reset shift counter when workers get new buffer

    for (let i = 0; i < workerPool.length; i++) {
        workerBusy[i] = true;
        workerPool[i].postMessage({
            type: 'init',
            predictionBuffer: predictionBuffer,
            bodiesMasses
        });
    }
}

// Process transfer search (called from game loop)
function updateTransferSearch() {
    if (transferState !== 'searching' && transferState !== 'ready' && transferState !== 'scheduled') return;
    if (!transferCraft || !transferDestinationBody) {
        resetTransferState();
        return;
    }

    // Only search if buffer is sufficiently populated
    const maxLaunchFrame = predictionBuffer.length - MIN_TRAJECTORY_RUNWAY_FRAMES;
    if (maxLaunchFrame <= TRANSFER_SEARCH_MIN_FRAMES) {
        // Buffer not ready yet, wait for it to grow
        return;
    }

    // Start parallel search if workers are ready and not already searching
    if (workerPoolReady && pendingBatches === 0) {
        // Check if there are new frames to search (incremental search)
        if (searchedUpToFrame < maxLaunchFrame) {
            // If buffer has shifted since workers were initialized, re-initialize with fresh buffer
            // This ensures workers have accurate prediction data for the new frames
            if (bufferShiftsSinceInit > 0) {
                // Set nextBatchStart to continue from where we left off
                nextBatchStart = searchedUpToFrame;
                startParallelSearch();  // This resets bufferShiftsSinceInit and sends fresh buffer
                return;  // Will dispatch batches once workers are ready
            }

            // Search from where we left off to maxLaunchFrame
            if (nextBatchStart < searchedUpToFrame) {
                nextBatchStart = searchedUpToFrame;
            }

            // Dispatch work to all idle workers
            for (let i = 0; i < workerPool.length; i++) {
                if (!workerBusy[i] && nextBatchStart < maxLaunchFrame) {
                    dispatchNextBatch(i);
                }
            }
        }
    }
}

// Transfer search timing constants
const TRANSFER_SEARCH_MIN_TIME = 5;  // Minimum time in the future to start searching (minutes)
const TRANSFER_SEARCH_MIN_FRAMES = Math.ceil(TRANSFER_SEARCH_MIN_TIME / PREDICTION_DT);
const MIN_TRAJECTORY_RUNWAY = 200;   // Minimum simulation time after launch to evaluate trajectory (minutes)
const MIN_TRAJECTORY_RUNWAY_FRAMES = Math.ceil(MIN_TRAJECTORY_RUNWAY / PREDICTION_DT);

// Get cache key for a source/destination pair
function getTransferCacheKey(sourceBody, destBody) {
    const sourceIndex = bodies.indexOf(sourceBody);
    const destIndex = bodies.indexOf(destBody);
    return `${sourceIndex}-${destIndex}`;
}

// Save current best result to cache
function saveToTransferCache() {
    if (!transferCraft || !transferDestinationBody || transferBestFrame < 0) return;

    // Only cache acceptable results (arrivalFrame !== Infinity means acceptable)
    const isAcceptable = transferBestArrivalFrame !== Infinity;
    if (!isAcceptable) return;

    const key = getTransferCacheKey(transferCraft.parentBody, transferDestinationBody);
    transferCache.set(key, {
        score: transferBestScore,
        launchFrame: transferBestFrame,
        arrivalFrame: transferBestArrivalFrame,
        trajectory: transferBestTrajectory,
        insertionFrame: transferInsertionFrame,
        sampleOffset: transferTrajectorySampleOffset,
        correction: {
            angle: correctionAngle,
            duration: correctionDuration,
            startFrame: correctionStartFrame
        }
    });
}

// Try to restore from cache, returns true if successful
function restoreFromTransferCache() {
    if (!transferCraft || !transferDestinationBody) return false;

    const key = getTransferCacheKey(transferCraft.parentBody, transferDestinationBody);
    const cached = transferCache.get(key);

    // Check if cache entry exists and launch time hasn't passed
    if (cached && cached.launchFrame > TRANSFER_SEARCH_MIN_FRAMES) {
        transferBestScore = cached.score;
        transferBestFrame = cached.launchFrame;
        transferBestArrivalFrame = cached.arrivalFrame;
        transferBestTrajectory = cached.trajectory;
        transferInsertionFrame = cached.insertionFrame;
        transferTrajectorySampleOffset = cached.sampleOffset;
        correctionAngle = cached.correction.angle;
        correctionDuration = cached.correction.duration;
        correctionStartFrame = cached.correction.startFrame;
        return true;
    }

    return false;
}

// Update cache on buffer shift - decrement frame indices and remove expired entries
function updateTransferCacheOnShift() {
    for (const [key, entry] of transferCache) {
        entry.launchFrame--;
        entry.arrivalFrame--;

        // Remove if launch time has passed
        if (entry.launchFrame <= 0) {
            transferCache.delete(key);
        }
    }
}

// Add an acceptable trajectory to the sorted list
function addAcceptableTrajectory(result) {
    // Adjust buffer-relative frame numbers by shifts since workers were initialized
    // Workers work on a snapshot, but the main buffer has shifted since then
    const adjustedLaunchFrame = result.launchFrame - bufferShiftsSinceInit;
    const adjustedArrivalFrame = result.arrivalFrame - bufferShiftsSinceInit;
    // insertionFrame is trajectory-relative (index within trajectory), not buffer-relative

    // Skip if this trajectory's launch time has already passed
    if (adjustedLaunchFrame <= 0) {
        return;
    }

    const entry = {
        launchFrame: adjustedLaunchFrame,
        arrivalFrame: adjustedArrivalFrame,
        score: result.score,
        trajectory: result.trajectory,
        insertionFrame: result.insertionFrame,  // Trajectory-relative, no adjustment needed
        sampleOffset: sampleOffset,
        correction: result.correction ? {
            angle: result.correction.angle,
            duration: result.correction.duration,
            startFrame: result.correction.startFrame  // Relative to launch, not buffer
        } : null
    };

    // Insert in sorted order by arrival frame (earliest first)
    let insertIndex = acceptableTrajectories.findIndex(t => t.arrivalFrame > entry.arrivalFrame);
    if (insertIndex === -1) {
        acceptableTrajectories.push(entry);
    } else {
        acceptableTrajectories.splice(insertIndex, 0, entry);
        // Adjust selected index if insertion was before it
        if (insertIndex <= selectedTrajectoryIndex) {
            selectedTrajectoryIndex++;
        }
    }
}

// Update transferBest* variables from the selected entry in the list
function updateBestFromList() {
    if (acceptableTrajectories.length === 0) {
        // No acceptable trajectories - clear best
        transferBestScore = Infinity;
        transferBestFrame = -1;
        transferBestTrajectory = null;
        transferBestArrivalFrame = Infinity;
        transferInsertionFrame = 0;
        correctionAngle = 0;
        correctionDuration = 0;
        correctionStartFrame = 0;
        selectedTrajectoryIndex = 0;
        return false;
    }

    // Clamp selected index to valid range
    if (selectedTrajectoryIndex >= acceptableTrajectories.length) {
        selectedTrajectoryIndex = 0;
    }

    const best = acceptableTrajectories[selectedTrajectoryIndex];
    transferBestScore = best.score;
    transferBestFrame = best.launchFrame;
    transferBestTrajectory = best.trajectory;
    transferBestArrivalFrame = best.arrivalFrame;
    transferInsertionFrame = best.insertionFrame;
    transferTrajectorySampleOffset = best.sampleOffset;

    if (best.correction) {
        correctionAngle = best.correction.angle;
        correctionDuration = best.correction.duration;
        correctionStartFrame = best.correction.startFrame;
    } else {
        correctionAngle = 0;
        correctionDuration = 0;
        correctionStartFrame = 0;
    }

    return true;
}

// Filter trajectories so that no two displayed points have launch times within
// 1 minute of each other. Among nearby points, keep the one with earliest arrival.
// Returns array of {entry, originalIndex} sorted by launch time.
function getFilteredTrajectories() {
    const trajs = acceptableTrajectories;
    if (trajs.length === 0) return [];

    // Skip trajectories outside the visible window (past or beyond 360min from current view)
    const viewFrame = Math.round(timeViewOffset);
    const maxFrame = viewFrame + 360 / PREDICTION_DT; // 360 minutes

    // Create indexed entries and sort by launch time
    const indexed = trajs.map((t, i) => ({ entry: t, originalIndex: i }));
    indexed.sort((a, b) => a.entry.launchFrame - b.entry.launchFrame);

    const THRESHOLD_MIN = 1.0;
    const filtered = [];

    for (let i = 0; i < indexed.length; i++) {
        const current = indexed[i];
        // Skip launch times outside the visible window
        if (current.entry.launchFrame < viewFrame) continue;
        if (current.entry.launchFrame > maxFrame) break; // sorted by launch time, so done

        if (filtered.length === 0) {
            filtered.push(current);
            continue;
        }

        const last = filtered[filtered.length - 1];
        const launchDiffMin = (current.entry.launchFrame - last.entry.launchFrame) * PREDICTION_DT;

        if (launchDiffMin <= THRESHOLD_MIN) {
            // Within 1 minute - keep the one with earlier arrival
            if (current.entry.arrivalFrame < last.entry.arrivalFrame) {
                filtered[filtered.length - 1] = current;
            }
        } else {
            filtered.push(current);
        }
    }

    return filtered;
}

// ========== Trajectory Plot ==========
const trajectoryPlotContainer = document.getElementById('trajectory-plot-container');
const trajectoryPlotCanvas = document.getElementById('trajectory-plot');
const trajectoryPlotCtx = trajectoryPlotCanvas.getContext('2d');
let trajectoryPlotDragging = false;
let trajectoryPlotLastUpdate = 0;

// Padding for the plot area (in CSS pixels)
const PLOT_PADDING_LEFT = 55;
const PLOT_PADDING_RIGHT = 20;
const PLOT_PADDING_TOP = 15;
const PLOT_PADDING_BOTTOM = 25;

function getComputedColor(varName) {
    return getComputedStyle(document.documentElement).getPropertyValue(varName).trim();
}

function updateTrajectoryPlot() {
    const isActive = transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled';
    if (!isActive) {
        trajectoryPlotContainer.style.display = 'none';
        return;
    }
    trajectoryPlotContainer.style.display = 'block';

    // Size the canvas to fill its CSS dimensions at device pixel ratio
    const dpr = window.devicePixelRatio || 1;
    const rect = trajectoryPlotCanvas.getBoundingClientRect();
    const w = rect.width;
    const h = rect.height;
    trajectoryPlotCanvas.width = w * dpr;
    trajectoryPlotCanvas.height = h * dpr;
    const ctx = trajectoryPlotCtx;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

    // Colors from theme
    const textColor = getComputedColor('--text-muted');
    const accentColor = getComputedColor('--accent-color');
    const lineColor = accentColor;
    const pointColor = accentColor;

    // Clear
    ctx.clearRect(0, 0, w, h);

    // Get filtered trajectories (collapse points within 1s on launch axis)
    const filtered = getFilteredTrajectories();

    // Compute data ranges
    const viewFrame = Math.round(timeViewOffset);
    const xMin = viewFrame * PREDICTION_DT;
    const xMax = xMin + 360;
    // The last MIN_TRAJECTORY_RUNWAY_FRAMES of the buffer lack enough runway to simulate transfers.
    // Use PREDICTION_FRAMES (target size) so the zone stays stable while buffer is still filling.
    const noSimStart = (PREDICTION_FRAMES - MIN_TRAJECTORY_RUNWAY_FRAMES) * PREDICTION_DT;

    let yMin, yMax;
    if (filtered.length > 0) {
        let minArrival = Infinity, maxArrival = -Infinity;
        for (const f of filtered) {
            const as = f.entry.arrivalFrame * PREDICTION_DT;
            if (as < minArrival) minArrival = as;
            if (as > maxArrival) maxArrival = as;
        }
        const arrivalRange = maxArrival - minArrival || 1;
        yMin = minArrival - arrivalRange * 0.05;
        yMax = maxArrival + arrivalRange * 0.05;
    } else {
        // Default Y range matches X range when no data points
        yMin = xMin;
        yMax = xMax;
    }

    // Plot area bounds (CSS pixels)
    const plotLeft = PLOT_PADDING_LEFT;
    const plotRight = w - PLOT_PADDING_RIGHT;
    const plotTop = PLOT_PADDING_TOP;
    const plotBottom = h - PLOT_PADDING_BOTTOM;
    const plotW = plotRight - plotLeft;
    const plotH = plotBottom - plotTop;

    // Map data to pixel coordinates
    function dataToPixel(launchMin, arrivalMin) {
        const px = plotLeft + ((launchMin - xMin) / (xMax - xMin)) * plotW;
        const py = plotBottom - ((arrivalMin - yMin) / (yMax - yMin)) * plotH;
        return [px, py];
    }

    // Draw axes
    ctx.strokeStyle = textColor;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(plotLeft, plotTop);
    ctx.lineTo(plotLeft, plotBottom);
    ctx.lineTo(plotRight, plotBottom);
    ctx.stroke();

    // Axis labels
    ctx.fillStyle = textColor;
    ctx.font = '10px monospace';
    ctx.textAlign = 'center';
    ctx.fillText('Launch (min)', (plotLeft + plotRight) / 2, h - 2);

    ctx.save();
    ctx.translate(12, (plotTop + plotBottom) / 2);
    ctx.rotate(-Math.PI / 2);
    ctx.fillText('Arrival (min)', 0, 0);
    ctx.restore();

    // Tick marks - X axis
    const xTickCount = Math.min(6, Math.max(2, Math.floor(plotW / 80)));
    for (let i = 0; i <= xTickCount; i++) {
        const val = xMin + (i / xTickCount) * (xMax - xMin);
        const px = plotLeft + (i / xTickCount) * plotW;
        ctx.fillStyle = textColor;
        ctx.textAlign = 'center';
        ctx.fillText(val.toFixed(0), px, plotBottom + 14);
        // Tick line
        ctx.strokeStyle = textColor;
        ctx.globalAlpha = 0.3;
        ctx.beginPath();
        ctx.moveTo(px, plotTop);
        ctx.lineTo(px, plotBottom);
        ctx.stroke();
        ctx.globalAlpha = 1;
    }

    // Tick marks - Y axis
    const yTickCount = Math.min(4, Math.max(2, Math.floor(plotH / 40)));
    for (let i = 0; i <= yTickCount; i++) {
        const val = yMin + (i / yTickCount) * (yMax - yMin);
        const py = plotBottom - (i / yTickCount) * plotH;
        ctx.fillStyle = textColor;
        ctx.textAlign = 'right';
        ctx.fillText(val.toFixed(0), plotLeft - 6, py + 3);
        // Grid line
        ctx.strokeStyle = textColor;
        ctx.globalAlpha = 0.3;
        ctx.beginPath();
        ctx.moveTo(plotLeft, py);
        ctx.lineTo(plotRight, py);
        ctx.stroke();
        ctx.globalAlpha = 1;
    }

    // Draw red "unsimulated" region where the prediction buffer lacks runway.
    // noSimStart is in data-space minutes; map it into the plot's pixel range.
    if (noSimStart < xMax) {
        const noSimPixelX = plotLeft + ((Math.max(noSimStart, xMin) - xMin) / (xMax - xMin)) * plotW;
        const unsimWidth = plotRight - noSimPixelX;
        if (unsimWidth > 0) {
            ctx.fillStyle = 'rgba(255, 60, 60, 0.12)';
            ctx.fillRect(noSimPixelX, plotTop, unsimWidth, plotH);
            if (unsimWidth > 40) {
                ctx.fillStyle = 'rgba(255, 80, 80, 0.5)';
                ctx.font = '9px monospace';
                ctx.textAlign = 'center';
                ctx.fillText('no sim', noSimPixelX + unsimWidth / 2, plotTop + 12);
            }
        }
    }

    // Skip data rendering if no trajectories
    if (filtered.length === 0) return;

    // Draw connecting line through filtered points (already sorted by launch time)
    ctx.strokeStyle = lineColor;
    ctx.lineWidth = 1.5;
    ctx.globalAlpha = 0.6;
    ctx.beginPath();
    for (let i = 0; i < filtered.length; i++) {
        const t = filtered[i].entry;
        const [px, py] = dataToPixel(t.launchFrame * PREDICTION_DT, t.arrivalFrame * PREDICTION_DT);
        if (i === 0) ctx.moveTo(px, py);
        else ctx.lineTo(px, py);
    }
    ctx.stroke();
    ctx.globalAlpha = 1;

    // Draw points (filtered only)
    for (let i = 0; i < filtered.length; i++) {
        const t = filtered[i].entry;
        const [px, py] = dataToPixel(t.launchFrame * PREDICTION_DT, t.arrivalFrame * PREDICTION_DT);
        ctx.beginPath();
        ctx.arc(px, py, 2.5, 0, Math.PI * 2);
        ctx.fillStyle = pointColor;
        ctx.fill();
    }

    // Draw selected point highlight and vertical slider line
    // Find the filtered entry that matches the selected trajectory (or nearest future one)
    let clampedSelIdx = Math.min(selectedTrajectoryIndex, acceptableTrajectories.length - 1);
    let selFiltered = filtered[0];
    // If the currently selected trajectory is before the view frame and we're NOT in scheduled
    // state, auto-advance the selection. Never auto-advance when scheduled — the committed
    // launch must stay fixed regardless of where the user scrubs.
    if (transferState !== 'scheduled' &&
        clampedSelIdx >= 0 && clampedSelIdx < acceptableTrajectories.length &&
        acceptableTrajectories[clampedSelIdx].launchFrame < viewFrame &&
        filtered.length > 0) {
        selectedTrajectoryIndex = filtered[0].originalIndex;
        clampedSelIdx = selectedTrajectoryIndex;
        updateBestFromList();
    }
    for (const f of filtered) {
        if (f.originalIndex === clampedSelIdx) {
            selFiltered = f;
            break;
        }
        // Pick the filtered entry closest by launch time to the selected trajectory
        if (clampedSelIdx >= 0 && clampedSelIdx < acceptableTrajectories.length) {
            const selLaunch = acceptableTrajectories[clampedSelIdx].launchFrame;
            if (Math.abs(f.entry.launchFrame - selLaunch) <
                Math.abs(selFiltered.entry.launchFrame - selLaunch)) {
                selFiltered = f;
            }
        }
    }
    {
        // When scheduled and scrubbed past the launch time, show a "launched" marker
        // at the left edge instead of highlighting a wrong trajectory
        const scheduledInPast = transferState === 'scheduled' &&
            clampedSelIdx >= 0 && clampedSelIdx < acceptableTrajectories.length &&
            acceptableTrajectories[clampedSelIdx].launchFrame < viewFrame;

        if (scheduledInPast) {
            // Draw a marker at the left edge indicating the launch already happened
            ctx.strokeStyle = 'rgba(100, 255, 100, 0.6)';
            ctx.lineWidth = 2;
            ctx.setLineDash([4, 3]);
            ctx.beginPath();
            ctx.moveTo(plotLeft, plotTop);
            ctx.lineTo(plotLeft, plotBottom);
            ctx.stroke();
            ctx.setLineDash([]);

            ctx.fillStyle = 'rgba(100, 255, 100, 0.7)';
            ctx.font = '9px monospace';
            ctx.textAlign = 'left';
            ctx.fillText('launched', plotLeft + 3, plotTop + 12);
        } else {
            const sel = selFiltered.entry;
            const [sx, sy] = dataToPixel(sel.launchFrame * PREDICTION_DT, sel.arrivalFrame * PREDICTION_DT);

            // Vertical slider line
            ctx.strokeStyle = accentColor;
            ctx.lineWidth = 1;
            ctx.globalAlpha = 0.5;
            ctx.beginPath();
            ctx.moveTo(sx, plotTop);
            ctx.lineTo(sx, plotBottom);
            ctx.stroke();
            ctx.globalAlpha = 1;

            // Selected point - larger and brighter
            ctx.beginPath();
            ctx.arc(sx, sy, 5, 0, Math.PI * 2);
            ctx.fillStyle = '#ffffff';
            ctx.fill();
            ctx.strokeStyle = accentColor;
            ctx.lineWidth = 2;
            ctx.stroke();
        }
    }
}

// Find the closest filtered trajectory's original index for a given x pixel coordinate
function trajectoryIndexFromPlotX(clientX) {
    const rect = trajectoryPlotCanvas.getBoundingClientRect();
    const x = clientX - rect.left;
    const w = rect.width;
    const plotLeft = PLOT_PADDING_LEFT;
    const plotRight = w - PLOT_PADDING_RIGHT;
    const plotW = plotRight - plotLeft;

    const filtered = getFilteredTrajectories();
    if (filtered.length === 0) return 0;

    // X-axis starts at the current view frame, matching updateTrajectoryPlot
    const viewFrame = Math.round(timeViewOffset);
    const xMin = viewFrame * PREDICTION_DT;
    const xMax = xMin + 360;

    // Convert pixel to data space
    const dataX = xMin + ((x - plotLeft) / plotW) * (xMax - xMin);

    // Find nearest filtered trajectory by launch time, return its original index
    // (filtered already excludes trajectories before viewFrame)
    let bestOrigIdx = filtered[0].originalIndex;
    let bestDist = Infinity;
    for (const f of filtered) {
        const dist = Math.abs(f.entry.launchFrame * PREDICTION_DT - dataX);
        if (dist < bestDist) {
            bestDist = dist;
            bestOrigIdx = f.originalIndex;
        }
    }
    return bestOrigIdx;
}

function handlePlotSelect(clientX) {
    const newIndex = trajectoryIndexFromPlotX(clientX);
    if (newIndex !== selectedTrajectoryIndex && newIndex >= 0 && newIndex < acceptableTrajectories.length) {
        selectedTrajectoryIndex = newIndex;
        updateBestFromList();
        if (transferState === 'scheduled') {
            transferScheduledFrame = transferBestFrame;
        }
        updateTrajectoryPlot();
    }
}

// Mouse interaction for plot
trajectoryPlotCanvas.addEventListener('mousedown', (e) => {
    if (acceptableTrajectories.length === 0) return;
    trajectoryPlotDragging = true;
    handlePlotSelect(e.clientX);
    e.preventDefault();
});

window.addEventListener('mousemove', (e) => {
    if (!trajectoryPlotDragging) return;
    handlePlotSelect(e.clientX);
    e.preventDefault();
});

window.addEventListener('mouseup', () => {
    trajectoryPlotDragging = false;
});

// Touch interaction for plot
trajectoryPlotCanvas.addEventListener('touchstart', (e) => {
    if (acceptableTrajectories.length === 0) return;
    trajectoryPlotDragging = true;
    handlePlotSelect(e.touches[0].clientX);
    e.preventDefault();
}, { passive: false });

window.addEventListener('touchmove', (e) => {
    if (!trajectoryPlotDragging) return;
    handlePlotSelect(e.touches[0].clientX);
    e.preventDefault();
}, { passive: false });

window.addEventListener('touchend', () => {
    trajectoryPlotDragging = false;
});

// Prev/next trajectory navigation by launch time (among filtered trajectories only)
function selectAdjacentTrajectory(direction) {
    const filtered = getFilteredTrajectories();
    if (filtered.length < 2) return;
    if (acceptableTrajectories.length === 0) return;

    // Find current position in filtered list
    let currentFilteredIdx = 0;
    const clampedIdx = Math.min(selectedTrajectoryIndex, acceptableTrajectories.length - 1);
    const currentLaunch = acceptableTrajectories[clampedIdx].launchFrame;
    let closestDist = Infinity;
    for (let i = 0; i < filtered.length; i++) {
        if (filtered[i].originalIndex === clampedIdx) {
            currentFilteredIdx = i;
            closestDist = 0;
            break;
        }
        const dist = Math.abs(filtered[i].entry.launchFrame - currentLaunch);
        if (dist < closestDist) {
            closestDist = dist;
            currentFilteredIdx = i;
        }
    }

    const nextFilteredIdx = currentFilteredIdx + direction;
    if (nextFilteredIdx >= 0 && nextFilteredIdx < filtered.length) {
        selectedTrajectoryIndex = filtered[nextFilteredIdx].originalIndex;
        updateBestFromList();
        if (transferState === 'scheduled') {
            transferScheduledFrame = transferBestFrame;
        }
        updateTrajectoryPlot();
    }
}

document.getElementById('traj-prev-btn').addEventListener('click', () => selectAdjacentTrajectory(-1));
document.getElementById('traj-next-btn').addEventListener('click', () => selectAdjacentTrajectory(1));

const trajectoryInfoBar = document.getElementById('trajectory-info-bar');
const scheduleLaunchBtn = document.getElementById('schedule-launch-btn');
const cancelTransferBtn = document.getElementById('cancel-transfer-btn');

scheduleLaunchBtn.addEventListener('click', () => {
    if ((transferState === 'ready' || transferState === 'searching') && acceptableTrajectories.length > 0) {
        transferState = 'scheduled';
        transferScheduledFrame = transferBestFrame;
        updateTrajectoryInfoBar();
    }
});

cancelTransferBtn.addEventListener('click', () => {
    if (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') {
        resetTransferState();
    }
});

// Also update immediately when new trajectories arrive (called from worker callback)
function onAcceptableTrajectoriesChanged() {
    updateTrajectoryPlot();
    updateTrajectoryInfoBar();
}

// Update the info bar and button states in the trajectory plot panel
function updateTrajectoryInfoBar() {
    if (transferState === 'searching') {
        const progress = predictionBuffer.length > 0
            ? Math.round((nextBatchStart / predictionBuffer.length) * 100)
            : 0;
        const activeWorkers = workerBusy.filter(b => b).length;
        const bestScoreText = transferBestScore === Infinity ? '--' : transferBestScore.toFixed(1);

        let html = `<span>Transfer to <strong>${transferDestinationBody.name}</strong></span>`;
        html += `<span><span class="info-label">Search:</span> ${progress}%</span>`;
        html += `<span><span class="info-label">Score:</span> ${bestScoreText}</span>`;
        if (acceptableTrajectories.length > 0) {
            const launchMin = (transferBestFrame * PREDICTION_DT).toFixed(1);
            const arrivalMin = transferBestArrivalFrame === Infinity ? '--' : (transferBestArrivalFrame * PREDICTION_DT).toFixed(1);
            html += `<span><span class="info-label">Launch:</span> ${launchMin}m</span>`;
            html += `<span><span class="info-label">Arrival:</span> ${arrivalMin}m</span>`;
        }
        trajectoryInfoBar.innerHTML = html;

        scheduleLaunchBtn.disabled = acceptableTrajectories.length === 0;
        scheduleLaunchBtn.textContent = 'Schedule';
        scheduleLaunchBtn.style.display = '';
        cancelTransferBtn.textContent = 'Cancel';

    } else if (transferState === 'ready') {
        const launchMin = (transferBestFrame * PREDICTION_DT).toFixed(1);
        const arrivalMin = transferBestArrivalFrame === Infinity ? '--' : (transferBestArrivalFrame * PREDICTION_DT).toFixed(1);

        let html = `<span>Transfer to <strong>${transferDestinationBody.name}</strong></span>`;
        html += `<span><span class="info-label">Launch:</span> ${launchMin}m</span>`;
        html += `<span><span class="info-label">Arrival:</span> ${arrivalMin}m</span>`;
        html += `<span><span class="info-label">Score:</span> ${transferBestScore.toFixed(1)}</span>`;
        if (correctionDuration > 0) {
            const corrMin = (correctionDuration * PREDICTION_DT).toFixed(2);
            const corrDeg = (correctionAngle * 180 / Math.PI).toFixed(1);
            html += `<span><span class="info-label">Corr:</span> ${corrMin}m@${corrDeg}°</span>`;
        }
        trajectoryInfoBar.innerHTML = html;

        scheduleLaunchBtn.disabled = false;
        scheduleLaunchBtn.textContent = 'Schedule';
        scheduleLaunchBtn.style.display = '';
        cancelTransferBtn.textContent = 'Cancel';

    } else if (transferState === 'scheduled') {
        const launchMin = (transferScheduledFrame * PREDICTION_DT).toFixed(1);
        const arrivalMin = transferBestArrivalFrame === Infinity ? '--' : (transferBestArrivalFrame * PREDICTION_DT).toFixed(1);

        let html = `<span><strong>Launch Scheduled</strong> → ${transferDestinationBody.name}</span>`;
        html += `<span><span class="info-label">T-</span>${launchMin}m</span>`;
        html += `<span><span class="info-label">Arrival:</span> ${arrivalMin}m</span>`;
        trajectoryInfoBar.innerHTML = html;

        scheduleLaunchBtn.style.display = 'none';
        cancelTransferBtn.textContent = 'Cancel';
    }
}

// Update acceptable trajectories list on buffer shift
function updateAcceptableTrajectoriesOnShift() {
    // Decrement buffer-relative frame indices and remove expired entries
    // insertionFrame is trajectory-relative, not buffer-relative, so don't decrement it
    for (let i = acceptableTrajectories.length - 1; i >= 0; i--) {
        acceptableTrajectories[i].launchFrame--;
        acceptableTrajectories[i].arrivalFrame--;

        // Remove if launch time has passed
        if (acceptableTrajectories[i].launchFrame <= 0) {
            acceptableTrajectories.splice(i, 1);
            // Adjust selected index if removal was at or before it
            if (i < selectedTrajectoryIndex) {
                selectedTrajectoryIndex--;
            } else if (i === selectedTrajectoryIndex) {
                selectedTrajectoryIndex = 0;
            }
        }
    }
    // Clamp in case list shrunk
    if (selectedTrajectoryIndex >= acceptableTrajectories.length) {
        selectedTrajectoryIndex = Math.max(0, acceptableTrajectories.length - 1);
    }

    // Decrement searchedUpToFrame only when no search is in progress
    // This prevents losing track of frames during active searches
    if (searchedUpToFrame > 0 && pendingBatches === 0) {
        searchedUpToFrame--;
    }
}

// Start transfer search process
function startTransferSearch() {
    transferState = 'searching';
    transferSearchFrame = TRANSFER_SEARCH_MIN_FRAMES;

    // Clear the acceptable trajectories list for new search
    acceptableTrajectories = [];
    searchedUpToFrame = 0;
    initialSearchComplete = false;

    // Reset best values
    transferBestScore = Infinity;
    transferBestFrame = -1;
    transferBestTrajectory = null;
    transferTrajectorySampleOffset = 0;
    transferInsertionFrame = 0;
    transferBestArrivalFrame = Infinity;
    correctionAngle = 0;
    correctionDuration = 0;
    correctionStartFrame = 0;

    // Reset parallel search state
    searchGeneration++;  // Increment to ignore any stale results from previous searches
    nextBatchStart = TRANSFER_SEARCH_MIN_FRAMES;
    pendingBatches = 0;
    // Initialize workers with current buffer and start search
    startParallelSearch();

    // Show trajectory plot container immediately (for info bar + cancel button)
    updateTrajectoryPlot();
    updateTrajectoryInfoBar();
}

// Reset transfer state
function resetTransferState() {
    // Save current result to cache before clearing (if valid)
    saveToTransferCache();

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
    transferInsertionFrame = 0;
    transferBestArrivalFrame = Infinity;
    // Reset correction state
    correctionAngle = 0;
    correctionDuration = 0;
    correctionStartFrame = 0;
    // Reset parallel search state
    nextBatchStart = 0;
    pendingBatches = 0;
    bufferShiftsSinceInit = 0;
    // Clear acceptable trajectories list
    acceptableTrajectories = [];
    selectedTrajectoryIndex = 0;
    searchedUpToFrame = 0;
    initialSearchComplete = false;
    // Hide trajectory plot
    trajectoryPlotContainer.style.display = 'none';
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
const SAMPLE_INTERVAL = Math.ceil(SOLID_PREDICTION_FRAMES / MAX_TRAJECTORY_POINTS);
// Fade ratio: what fraction of visible trajectory should fade at the tip
const BODY_TRAJECTORY_FADE_RATIO = FADE_PREDICTION_FRAMES / PREDICTION_FRAMES;

// Update trajectory path elements with current predictions
function updateTrajectories() {
    if (predictionBuffer.length === 0) return;

    // When scrubbing forward, skip trajectory frames before the scrub position
    // so paths get "consumed" like they do during normal time advancement
    const scrubFrame = Math.round(timeViewOffset);

    // Build path for each body
    for (let bodyIndex = 0; bodyIndex < bodies.length; bodyIndex++) {
        const body = bodies[bodyIndex];
        if (!body.trajectoryPath) continue;

        // Only plot the first quarter of the buffer from the current view position
        const remainingFrames = predictionBuffer.length - Math.max(0, scrubFrame);
        const visibleFrames = Math.ceil(remainingFrames / 4);
        const maxFrame = Math.min(predictionBuffer.length, Math.max(0, scrubFrame) + visibleFrames);

        // Compute sample interval so MAX_TRAJECTORY_POINTS covers the visible range
        const sampleInterval = Math.max(1, Math.ceil(visibleFrames / MAX_TRAJECTORY_POINTS));

        // Collect all sampled points from the buffer (starting from sampleOffset for consistency)
        const points = [];

        // Always include first point if not already selected by sampling
        // Skip when scrubbing forward since those frames are "consumed"
        const adjustedOffset = sampleOffset % sampleInterval;
        if (adjustedOffset !== 0 && predictionBuffer.length > 0 && scrubFrame <= 0) {
            const state = predictionBuffer[0][bodyIndex];
            points.push({
                screen: worldToScreen(state.x, state.y),
                frame: 0
            });
        }

        // Collect downsampled points, skipping frames before scrub position
        for (let i = adjustedOffset; i < maxFrame; i += sampleInterval) {
            if (i < scrubFrame) continue;
            const state = predictionBuffer[i][bodyIndex];
            points.push({
                screen: worldToScreen(state.x, state.y),
                frame: i
            });
        }

        // Always include last visible point if not already selected by sampling
        const lastFrame = maxFrame - 1;
        if (lastFrame >= 0 && (points.length === 0 || points[points.length - 1].frame !== lastFrame)) {
            const state = predictionBuffer[lastFrame][bodyIndex];
            points.push({
                screen: worldToScreen(state.x, state.y),
                frame: lastFrame
            });
        }

        // Fade the tail end of the visible portion
        const fadeLength = Math.ceil(visibleFrames * BODY_TRAJECTORY_FADE_RATIO);
        const fadeStartFrame = Math.max(0, maxFrame - fadeLength);

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
        const fadeLengthActual = maxFrame - fadeStartFrame;
        for (let i = 0; i < allFadePoints.length - 1; i++) {
            const p1 = allFadePoints[i];
            const p2 = allFadePoints[i + 1];

            // Calculate opacity based on midpoint frame position within fade region
            const midFrame = (p1.frame + p2.frame) / 2;
            const fadeProgress = Math.max(0, (midFrame - fadeStartFrame) / fadeLengthActual);
            const opacity = 0.24 * (1 - fadeProgress);

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
        const showTransferTrajectory = isTransferCraft && (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') && transferBestTrajectory;

        // Skip if orbiting and not showing transfer trajectory
        if (craft.state === 'orbiting' && !showTransferTrajectory) {
            // Hide trajectory and correction overlay
            craft.trajectoryPath.setAttribute('d', '');
            if (craft.trajectoryHitArea) craft.trajectoryHitArea.setAttribute('d', '');
            craft.trajectoryFadeGroup.innerHTML = '';
            if (craft.correctionOverlay) craft.correctionOverlay.style.display = 'none';
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

        // Compute effective scrub frame for this craft's trajectory buffer
        let craftScrubFrame = 0;
        if (showTransferTrajectory) {
            // Transfer trajectory buffer starts at the scheduled launch frame
            if (transferScheduledFrame > 0 && scrubFrame >= transferScheduledFrame) {
                craftScrubFrame = scrubFrame - transferScheduledFrame;
            }
        } else {
            craftScrubFrame = scrubFrame;
        }

        // Always include first point if not already selected by sampling
        // Skip when scrubbing forward since those frames are "consumed"
        if (effectiveSampleOffset !== 0 && craftPrediction.length > 0 && craftScrubFrame <= 0) {
            const pos = craftPrediction[0];
            points.push({
                screen: worldToScreen(pos.x, pos.y),
                frame: 0
            });
        }

        // Collect downsampled points, skipping frames before scrub position
        for (let i = effectiveSampleOffset; i < craftPrediction.length; i += SAMPLE_INTERVAL) {
            if (i < craftScrubFrame) continue;
            const pos = craftPrediction[i];
            points.push({
                screen: worldToScreen(pos.x, pos.y),
                frame: i
            });
        }

        // Include last point (unless scrubbed past the end of the trajectory)
        const lastFrame = craftPrediction.length - 1;
        if (lastFrame >= 0 && lastFrame >= craftScrubFrame && (points.length === 0 || points[points.length - 1].frame !== lastFrame)) {
            const pos = craftPrediction[lastFrame];
            points.push({
                screen: worldToScreen(pos.x, pos.y),
                frame: lastFrame
            });
        }

        // If scrubbed past entire trajectory, hide it (craft has already arrived)
        if (points.length === 0) {
            craft.trajectoryPath.setAttribute('d', '');
            if (craft.trajectoryHitArea) craft.trajectoryHitArea.setAttribute('d', '');
            if (craft.correctionOverlay) craft.correctionOverlay.style.display = 'none';
            continue;
        }

        // Build solid path for entire trajectory (no fading for craft trajectories)
        // For transfer trajectory not yet scrubbed past launch, start from first point of trajectory
        // Otherwise, start from craft's current (possibly scrubbed) position
        let startScreen;
        if (showTransferTrajectory && craftPrediction.length > 0 && craftScrubFrame <= 0) {
            startScreen = worldToScreen(craftPrediction[0].x, craftPrediction[0].y);
        } else {
            const craftPos = craft.getPosition();
            startScreen = worldToScreen(craftPos.x, craftPos.y);
        }
        let solidPath = `M ${startScreen.x} ${startScreen.y}`;

        // Draw all points as solid (no fade for craft trajectories)
        for (const point of points) {
            solidPath += ` L ${point.screen.x} ${point.screen.y}`;
        }
        craft.trajectoryPath.setAttribute('d', solidPath);

        // Update hit area with same path (for click detection)
        if (craft.trajectoryHitArea) {
            craft.trajectoryHitArea.setAttribute('d', solidPath);
        }

        // Draw correction overlay if applicable
        if (showTransferTrajectory && correctionDuration > 0 && craft.correctionOverlay) {
            const overlayPoints = [];
            const correctionEndFrame = correctionStartFrame + correctionDuration;
            for (let i = Math.max(correctionStartFrame, craftScrubFrame); i <= correctionEndFrame && i < craftPrediction.length; i++) {
                const pos = craftPrediction[i];
                overlayPoints.push(worldToScreen(pos.x, pos.y));
            }
            if (overlayPoints.length > 1) {
                let overlayPath = `M ${overlayPoints[0].x} ${overlayPoints[0].y}`;
                for (let j = 1; j < overlayPoints.length; j++) {
                    overlayPath += ` L ${overlayPoints[j].x} ${overlayPoints[j].y}`;
                }
                craft.correctionOverlay.setAttribute('d', overlayPath);
                craft.correctionOverlay.style.display = 'block';
            } else {
                craft.correctionOverlay.style.display = 'none';
            }
        } else if (craft.correctionOverlay) {
            craft.correctionOverlay.style.display = 'none';
        }

        // Clear fade group (craft trajectories are fully solid, no fade)
        if (craft.trajectoryFadeGroup) {
            craft.trajectoryFadeGroup.innerHTML = '';
        }
    }
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

    const width = svgWidth;
    const height = svgHeight;

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
            bodyListHtml += '<button id="cancel-dest-select-btn">Cancel</button>';
            infoDiv.innerHTML = bodyListHtml;
            infoDiv.dataset.transferState = 'selecting_destination';
            delete infoDiv.dataset.bodyName;
        }
        infoDiv.style.display = 'block';
        return;
    }

    // Check if we're scrubbed past arrival of a scheduled transfer
    const viewFrame = Math.round(timeViewOffset);
    const scrubPastArrival = transferState === 'scheduled' && transferBestTrajectory &&
        viewFrame >= transferScheduledFrame + transferBestTrajectory.length;
    // Check if we're scrubbed into the transit period (after launch, before arrival)
    const scrubInTransit = transferState === 'scheduled' && transferBestTrajectory &&
        transferScheduledFrame > 0 && viewFrame >= transferScheduledFrame && !scrubPastArrival;

    if (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') {
        if (!scrubPastArrival) {
            // Update info bar and buttons in the trajectory plot panel
            updateTrajectoryInfoBar();
        }
        delete infoDiv.dataset.transferState;
    }

    // Clear transfer state tracking when in 'none' state
    delete infoDiv.dataset.transferState;
    delete infoDiv.dataset.countdown;
    delete infoDiv.dataset.searchProgress;
    delete infoDiv.dataset.selectedTraj;

    // Handle selected craft display
    if (selectedCraft) {
        const craft = selectedCraft;
        const currentCraftId = infoDiv.dataset.craftId;
        const craftId = crafts.indexOf(craft).toString();

        // Determine craft location description
        let locationInfo = '';
        let transferInfo = '';

        // Treat the transfer craft as in-transit when scrubbed past its launch
        const craftVisuallyInTransit = scrubInTransit && craft === transferCraft;

        if (craft.state === 'orbiting' && !craftVisuallyInTransit) {
            locationInfo = `<div class="info-row">
                <span class="info-label">Orbiting:</span>
                <span class="info-value">${craft.parentBody.name}</span>
            </div>`;
        } else if (craft.state === 'free' || craftVisuallyInTransit) {
            const destBody = craft.destinationBody || (craftVisuallyInTransit ? transferDestinationBody : null);
            const fromBody = craft.launchedFromBody || (craftVisuallyInTransit ? craft.parentBody : null);
            if (destBody) {
                // In transfer flight
                let timeToArrival;
                if (craftVisuallyInTransit) {
                    const trajFrame = viewFrame - transferScheduledFrame;
                    const framesLeft = transferBestTrajectory.length - trajFrame;
                    timeToArrival = (framesLeft * PREDICTION_DT).toFixed(1);
                } else {
                    const framesLeft = craft.trajectoryBuffer.length;
                    timeToArrival = (framesLeft * PREDICTION_DT).toFixed(1);
                }

                locationInfo = `<div class="info-row">
                    <span class="info-label">From:</span>
                    <span class="info-value">${fromBody ? fromBody.name : 'Unknown'}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">To:</span>
                    <span class="info-value">${destBody.name}</span>
                </div>`;

                // Time to arrival
                transferInfo = `<div class="info-row">
                    <span class="info-label">Arrival in:</span>
                    <span class="info-value" id="craft-arrival">${timeToArrival}m</span>
                </div>`;

                // Time to correction (if applicable)
                if (craft.correctionParams && craft.correctionParams.duration > 0) {
                    const correctionStart = craft.correctionParams.startFrame;
                    const correctionEnd = correctionStart + craft.correctionParams.duration;

                    if (craft.flightFrame < correctionStart) {
                        // Correction hasn't started yet
                        const framesToCorrection = correctionStart - craft.flightFrame;
                        const timeToCorrection = (framesToCorrection * PREDICTION_DT).toFixed(1);
                        transferInfo += `<div class="info-row">
                            <span class="info-label">Correction in:</span>
                            <span class="info-value" id="craft-correction">${timeToCorrection}m</span>
                        </div>`;
                    } else if (craft.flightFrame < correctionEnd) {
                        // Currently correcting
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

        // Only rebuild if craft changed or craft state changed
        const currentCraftState = infoDiv.dataset.craftState;
        if (currentCraftId !== craftId || currentCraftState !== craft.state) {
            infoDiv.innerHTML = `
                <h3>Craft</h3>
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
            infoDiv.dataset.craftState = craft.state;
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

            if (arrivalEl && craft.destinationBody) {
                const framesLeft = craft.trajectoryBuffer.length;
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
        // Count orbiting craft for this body
        // When scrubbed past arrival, the transfer craft counts at the destination instead of source
        let orbitingCraftCount = crafts.filter(c => c.parentBody === selectedBody && c.state === 'orbiting').length;
        if (scrubPastArrival && transferCraft) {
            if (selectedBody === transferCraft.parentBody) orbitingCraftCount--;
            if (selectedBody === transferDestinationBody) orbitingCraftCount++;
        }

        // Check if we need to rebuild the panel structure (different body selected, craft count changed, or buffer ready state changed)
        const currentBodyName = infoDiv.dataset.bodyName;
        const currentCraftCount = parseInt(infoDiv.dataset.craftCount || '0', 10);
        const bufferReady = predictionBuffer.length >= PREDICTION_FRAMES;
        const currentBufferReady = infoDiv.dataset.bufferReady === 'true';
        const needsRebuild = currentBodyName !== selectedBody.name || currentCraftCount !== orbitingCraftCount || currentBufferReady !== bufferReady;

        if (needsRebuild) {
            let transferBtnHtml = '';
            if (orbitingCraftCount > 0) {
                // Disable transfer button until prediction buffer is fully initialized
                if (bufferReady) {
                    transferBtnHtml = `<button id="transfer-btn">${orbitingCraftCount} craft - Transfer</button>`;
                } else {
                    const progress = Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100);
                    transferBtnHtml = `<button id="transfer-btn" disabled>Propagating - ${progress}%</button>`;
                }
            }

            infoDiv.innerHTML = `
                <h3><span class="body-indicator" style="background-color: ${selectedBody.color}"></span>${selectedBody.name}</h3>
                ${transferBtnHtml}
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
            infoDiv.dataset.craftCount = orbitingCraftCount;
            infoDiv.dataset.bufferReady = bufferReady;
        } else {
            // Just update the dynamic values without rebuilding
            const posEl = document.getElementById('info-position');
            const speedEl = document.getElementById('info-speed');
            const kineticEl = document.getElementById('info-kinetic');
            if (posEl) posEl.textContent = `(${selectedBody.x.toFixed(0)}, ${selectedBody.y.toFixed(0)})`;
            if (speedEl) speedEl.textContent = selectedBody.speed.toFixed(1);
            if (kineticEl) kineticEl.textContent = selectedBody.kineticEnergy.toFixed(1);

            // Update propagation progress on transfer button if buffer not ready
            if (!bufferReady) {
                const transferBtn = document.getElementById('transfer-btn');
                if (transferBtn) {
                    const progress = Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100);
                    transferBtn.textContent = `Propagating - ${progress}%`;
                }
            }
        }
        infoDiv.style.display = 'block';
    } else {
        // Show tabbed list (Bodies / Trajectories) when none selected
        const freeCrafts = crafts.filter(c => c.state === 'free');
        // Include the transfer craft as visually in-transit when scrubbed past launch
        if (scrubInTransit && transferCraft && !freeCrafts.includes(transferCraft)) {
            freeCrafts.push(transferCraft);
        }
        const freeCraftCount = freeCrafts.length;
        const orbitingCountByBody = new Map();
        for (const craft of crafts) {
            if (craft.state === 'orbiting' && craft.parentBody) {
                // Skip the transfer craft if it's visually in transit
                if (scrubInTransit && craft === transferCraft) continue;
                orbitingCountByBody.set(craft.parentBody, (orbitingCountByBody.get(craft.parentBody) || 0) + 1);
            }
        }
        // When scrubbed past arrival, move the transfer craft count from source to destination
        if (scrubPastArrival && transferCraft && transferCraft.parentBody && transferDestinationBody) {
            const srcCount = orbitingCountByBody.get(transferCraft.parentBody) || 0;
            orbitingCountByBody.set(transferCraft.parentBody, Math.max(0, srcCount - 1));
            orbitingCountByBody.set(transferDestinationBody, (orbitingCountByBody.get(transferDestinationBody) || 0) + 1);
        }
        const orbitingCountKey = bodies.map(b => orbitingCountByBody.get(b) || 0).join(',');
        const prevCount = infoDiv.dataset.freeCraftCount;
        const prevOrbitingCounts = infoDiv.dataset.orbitingCounts;
        const prevTab = infoDiv.dataset.activeTab;

        // Rebuild if not already showing tabs, or if craft count or active tab changed
        if (!infoDiv.querySelector('.info-tabs') ||
            prevCount !== String(freeCraftCount) ||
            prevOrbitingCounts !== orbitingCountKey ||
            prevTab !== infoTabActive) {

            let html = '<div class="info-tabs">';
            html += `<div class="info-tab${infoTabActive === 'bodies' ? ' active' : ''}" data-tab="bodies">Bodies</div>`;
            html += `<div class="info-tab${infoTabActive === 'trajectories' ? ' active' : ''}" data-tab="trajectories">Trajectories <span class="info-tab-count">(${freeCraftCount})</span></div>`;
            html += '</div>';

            if (infoTabActive === 'bodies') {
                html += '<div class="body-list">';
                for (const body of bodies) {
                    const craftCount = orbitingCountByBody.get(body) || 0;
                    const craftCountDisplay = craftCount > 0 ? craftCount : '';
                    html += `
                        <div class="body-list-item" data-body-name="${body.name}">
                            <span class="body-indicator" style="background-color: ${body.color}"></span>
                            <span class="body-name">${body.name}</span>
                            <span class="body-craft-count">${craftCountDisplay}</span>
                        </div>
                    `;
                }
                html += '</div>';
            } else {
                html += '<div class="body-list">';
                if (freeCrafts.length === 0) {
                    html += '<div style="padding: 8px; color: var(--text-muted); font-size: 12px;">No craft in transit</div>';
                }
                for (const craft of freeCrafts) {
                    const isVisualTransit = scrubInTransit && craft === transferCraft;
                    const fromName = craft.launchedFromBody ? craft.launchedFromBody.name : (isVisualTransit && craft.parentBody ? craft.parentBody.name : '?');
                    const toName = craft.destinationBody ? craft.destinationBody.name : (isVisualTransit && transferDestinationBody ? transferDestinationBody.name : '?');
                    const label = `${fromName} → ${toName}`;
                    const idx = crafts.indexOf(craft);
                    html += `
                        <div class="body-list-item" data-craft-index="${idx}">
                            <span class="body-indicator" style="background-color: white; width: 8px; height: 8px;"></span>
                            <span class="body-name">${label}</span>
                        </div>
                    `;
                }
                html += '</div>';
            }

            infoDiv.innerHTML = html;
            infoDiv.dataset.freeCraftCount = freeCraftCount;
            infoDiv.dataset.orbitingCounts = orbitingCountKey;
            infoDiv.dataset.activeTab = infoTabActive;
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

// Find craft at screen position (for craft selection)
function findCraftAtPosition(screenX, screenY) {
    const world = screenToWorld(screenX, screenY);
    // Click radius is 3x the shown radius (CRAFT_DOT_RADIUS), in world units
    const clickRadius = (CRAFT_DOT_RADIUS * 3) / camera.zoom;

    for (const craft of crafts) {
        // Only select crafts in transit (free flight), not orbiting
        if (craft.state !== 'free') continue;

        const pos = craft.getPosition();
        const dx = world.x - pos.x;
        const dy = world.y - pos.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist <= clickRadius) {
            return craft;
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
            // This was a click, deselect both body and craft
            selectedBody = null;
            selectedCraft = null;
        } else {
            // User actually panned - pause auto-fit and stop tracking
            isAutoFitPaused = true;
            isTrackingSelectedBody = false;
            isTrackingSelectedCraft = false;
        }
    } else {
        // Check for craft click first (smaller targets get priority)
        const clickedCraft = findCraftAtPosition(x, y);
        if (clickedCraft) {
            selectedCraft = clickedCraft;
            selectedBody = null;
            isTrackingSelectedCraft = true;
            isTrackingSelectedBody = false;
            return;
        }

        // Click on a body
        const clicked = findBodyAtPosition(x, y);

        // If selecting destination for transfer
        if (transferState === 'selecting_destination' && clicked && clicked !== transferSourceBody) {
            transferDestinationBody = clicked;
            startTransferSearch();
        } else {
            // Normal body selection
            selectedBody = clicked;
            selectedCraft = null;
            isTrackingSelectedCraft = false;
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

    // User manually zooming - pause auto-fit and stop tracking
    isAutoFitPaused = true;
    isTrackingSelectedCraft = false;

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
        // Single touch - start drag/pan
        const x = touches[0].clientX - rect.left;
        const y = touches[0].clientY - rect.top;

        // Check if touching a body
        const touchedBody = findBodyAtPosition(x, y);
        if (touchedBody) {
            selectedBody = touchedBody;
            isTrackingSelectedBody = true;
        } else {
            // Start panning
            isDragging = true;
            dragStart = { x, y };
            cameraStart = { x: camera.x, y: camera.y };
        }

        touchState.active = true;
        touchState.lastTouches = [{ x, y }];
    } else if (touches.length === 2) {
        // Two finger touch - start pinch zoom
        isDragging = false;
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

        const dx = (x - dragStart.x) / camera.zoom;
        const dy = (y - dragStart.y) / camera.zoom;
        camera.x = cameraStart.x - dx;
        camera.y = cameraStart.y - dy;

        // User manually panning - pause auto-fit
        isAutoFitPaused = true;
        isTrackingSelectedBody = false;
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
            isAutoFitPaused = true;
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

            if (moved < 10) {
                // This was a tap - check for craft dot or trajectory, then deselect
                const tappedCraft = findCraftAtPosition(endX, endY);
                // Also check if tap hit a trajectory path via DOM hit-testing
                const elementAtTap = document.elementFromPoint(endTouch.clientX, endTouch.clientY);
                const trajectoryCraft = elementAtTap && elementAtTap._craft && elementAtTap._craft.state === 'free'
                    ? elementAtTap._craft : null;

                if (tappedCraft || trajectoryCraft) {
                    selectedCraft = tappedCraft || trajectoryCraft;
                    selectedBody = null;
                    isTrackingSelectedCraft = true;
                    isTrackingSelectedBody = false;
                } else {
                    selectedBody = null;
                    selectedCraft = null;
                }
            } else {
                // User actually panned - pause auto-fit and stop tracking
                isAutoFitPaused = true;
                isTrackingSelectedBody = false;
                isTrackingSelectedCraft = false;
            }
        }

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
    isTrackingSelectedCraft = false;
    selectedBody = null;
    selectedCraft = null;
}

// Update camera to track selected body or fit all
function updateCameraTracking() {
    if (isDragging) return;

    if (selectedCraft && isTrackingSelectedCraft && selectedCraft.state === 'free') {
        // Track selected craft - fit to trajectory and destination
        fitCraftTrajectory(selectedCraft);
    } else if (selectedBody && isTrackingSelectedBody) {
        // Track selected body (positions already set by syncToViewFrame)
        camera.x = selectedBody.x;
        camera.y = selectedBody.y;
    } else if (!selectedBody && !selectedCraft && !isAutoFitPaused) {
        // Auto-fit all bodies when nothing selected
        fitAllBodies();
    }

    // Update Fit All button active state - active when auto-fitting (no body selected and not paused)
    const fitAllBtn = document.getElementById('fit-all-btn');
    const isAutoFitActive = !selectedBody && !selectedCraft && !isAutoFitPaused;
    fitAllBtn.classList.toggle('active', isAutoFitActive);
}

// Fit camera to show craft trajectory and destination body
function fitCraftTrajectory(craft) {
    if (!craft || craft.state !== 'free') return;

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

    advanceTimeline(dt);
    extendCraftBuffers();
    updateTransferSearch();

    // Sync all body/craft state to the currently viewed frame (present or future)
    syncToViewFrame();
    updateCameraTracking();
    render();
    updateTrajectories();

    // Redraw time wheel and label if panel is open
    if (timeScrubPanelOpen) {
        drawTimeWheel();
        updateTimeScrubLabel();
    }

    // Update trajectory plot and info bar every frame when transfer is active
    const transferActive = transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled';
    if (transferActive) {
        // Hide plot when scrubbed past a scheduled launch (craft is visually in transit)
        const viewFrame = Math.round(timeViewOffset);
        if (transferState === 'scheduled' && transferScheduledFrame > 0 && viewFrame >= transferScheduledFrame) {
            trajectoryPlotContainer.style.display = 'none';
        } else {
            updateTrajectoryPlot();
            updateTrajectoryInfoBar();
        }
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
            console.log(`[CPU Benchmark] CPU: ${cpuPercent.toFixed(1)}% | Avg frame: ${avgFrameTime.toFixed(2)}ms | Frames: ${benchmarkFrameCount} | Elapsed: ${(elapsedMs/1000).toFixed(1)}`);

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

// Initialize
function init() {
    // Initialize worker pool for parallel transfer search
    initWorkerPool();

    svg.addEventListener('mousemove', handleMouseMove);
    svg.addEventListener('mousedown', handleMouseDown);
    svg.addEventListener('mouseup', handleMouseUp);
    svg.addEventListener('mouseleave', () => { isDragging = false; });
    svg.addEventListener('wheel', handleWheel, { passive: false });

    // Touch events for mobile
    svg.addEventListener('touchstart', handleTouchStart, { passive: false });
    svg.addEventListener('touchmove', handleTouchMove, { passive: false });
    svg.addEventListener('touchend', handleTouchEnd, { passive: false });
    svg.addEventListener('touchcancel', handleTouchEnd, { passive: false });

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

    // Handle clicks on craft trajectories
    trajectoriesLayer.addEventListener('click', (e) => {
        const target = e.target;
        // Check if clicked element is a craft trajectory with a craft reference
        if (target._craft && target._craft.state === 'free') {
            selectedCraft = target._craft;
            selectedBody = null;
            isTrackingSelectedCraft = true; // Start auto-fitting to trajectory
            e.stopPropagation(); // Prevent body deselection
        }
    });

    // Reset button
    document.getElementById('reset-btn').addEventListener('click', () => {
        initBodies();
        resetPredictions();
        resetTransferState();
        isPaused = false;
        timeViewOffset = 0;
        selectedBody = null;
        selectedCraft = null;
        hoveredBody = null;
        isAutoFitPaused = false;
        isTrackingSelectedBody = true;
        isTrackingSelectedCraft = false;
        camera = { x: 0, y: 0, zoom: 1 };
        updateTimeScrubLabel();
    });

    // Fit All button - fit all bodies but keep selection
    document.getElementById('fit-all-btn').addEventListener('click', () => {
        isTrackingSelectedBody = false;
        isTrackingSelectedCraft = false;
        isAutoFitPaused = false;
        fitAllBodies();
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

        // Handle cancel destination selection button click
        if (e.target.id === 'cancel-dest-select-btn') {
            resetTransferState();
            return;
        }

        // Handle tab click
        const tab = e.target.closest('.info-tab');
        if (tab && tab.dataset.tab) {
            infoTabActive = tab.dataset.tab;
            return;
        }

        // Handle body list item click
        const item = e.target.closest('.body-list-item');
        if (item) {
            // Check if it's a craft/trajectory item
            if (item.dataset.craftIndex !== undefined) {
                const craft = crafts[parseInt(item.dataset.craftIndex)];
                if (craft && craft.state === 'free') {
                    selectedCraft = craft;
                    selectedBody = null;
                    isTrackingSelectedCraft = true;
                    isTrackingSelectedBody = false;
                }
                return;
            }

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
    const WHEEL_RADIUS = 50;
    const WHEEL_CENTER_X = 60;
    const WHEEL_CENTER_Y = 60;
    // 15 degrees of rotation per single timestep
    const FRAMES_PER_RADIAN = 2 / (Math.PI / 12);

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
    const WHEEL_COAST_FRICTION = 0.97;  // velocity decay when free-spinning (long coast)
    const WHEEL_GRIP_FRICTION = 0.85;   // velocity decay when finger is on wheel (quick stop)
    const WHEEL_STOP_THRESHOLD = 0.0005; // min velocity before stopping (rad/ms) — snappy cutoff like a real wheel

    function getWheelAngle(clientX, clientY) {
        const rect = timeWheelSvg.getBoundingClientRect();
        const x = clientX - rect.left - WHEEL_CENTER_X;
        const y = clientY - rect.top - WHEEL_CENTER_Y;
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
            const svgX = (wheelTapStartX - rect.left) * (120 / rect.width);
            const svgY = (wheelTapStartY - rect.top) * (120 / rect.height);

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

    createComMarker();
    initBodies();

    lastTime = performance.now();
    requestAnimationFrame(gameLoop);
}

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
        if (!commitData) return;

        const branchEl = commitModalContent.querySelector('.commit-branch');
        const dateLineEl = commitModalContent.querySelector('.commit-date-line');
        const hashEl = commitModalContent.querySelector('.commit-hash');
        const messageEl = commitModalContent.querySelector('.commit-message');

        const date = new Date(commitData.commit.author.date);
        branchEl.textContent = branchName ? `Branch: ${branchName}` : '';
        dateLineEl.textContent = formatDate(date);

        const commitUrl = `https://github.com/${repoName}/commit/${commitHash}`;
        hashEl.innerHTML = `<a href="${commitUrl}" target="_blank" rel="noopener noreferrer">${commitHash}</a>`;
        messageEl.textContent = commitData.commit.message;

        commitModal.classList.add('visible');
    }

    // Hide modal
    function hideModal() {
        commitModal.classList.remove('visible');
    }

    // Event listeners
    commitInfoEl.addEventListener('click', () => {
        if (commitData) showModal();
    });

    commitModal.addEventListener('click', (e) => {
        if (e.target === commitModal || e.target.classList.contains('close-btn')) {
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
