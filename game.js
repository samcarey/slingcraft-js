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
const PREDICTION_TIME = 360; // Predict 360 seconds ahead
const SOLID_PREDICTION_TIME = 320; // First 320 seconds are solid
const PREDICTION_DT = 0.033; // Fixed timestep for prediction (~30fps)
const PREDICTION_FRAMES = Math.ceil(PREDICTION_TIME / PREDICTION_DT);
const SOLID_PREDICTION_FRAMES = Math.ceil(SOLID_PREDICTION_TIME / PREDICTION_DT);
const FADE_PREDICTION_FRAMES = PREDICTION_FRAMES - SOLID_PREDICTION_FRAMES;
const MAX_TRAJECTORY_POINTS = 100; // Max points to render for solid portion
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

// Accordion menu state
let accordionOrigin = null;       // Selected origin body
let accordionCraft = null;        // Selected craft object
let accordionDestination = null;  // Selected destination body
let accordionBuilt = false;       // Whether origin list has been built

// Planet lore and backstories
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

const destinationLore = {
    'Sol': 'The stellar core awaits — radiation shielding at maximum. A daring approach.',
    'Ember': 'Ember\'s docking ring glows faintly through the heat haze. Approach vector locked.',
    'Terra': 'Terra\'s orbital ring extends a welcome beacon. Atmospheric entry corridor standing by.',
    'Luna': 'Luna Station acknowledges your transponder. Crater-side berth assigned.',
    'Gaia': 'Gaia\'s canopy opens — bioluminescent landing pads illuminate the descent.',
    'Aria': 'Crystal spires glint in the distance. Aria\'s resonance guides your approach.',
    'Nyx': 'Dark-side approach confirmed. Nyx reveals nothing until you\'re already there.'
};
let speedMultiplier = 1;
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
        this.trajectoryPath.style.opacity = '0.3';
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
    predictionTimeAccum += dt * speedMultiplier;
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

                // Check if in correction phase (for visual feedback)
                // Note: correction is already applied in trajectoryBuffer, so we only set the flag here
                if (craft.correctionParams) {
                    const params = craft.correctionParams;
                    const inCorrectionPhase = craft.flightFrame >= params.startFrame &&
                                              craft.flightFrame < params.startFrame + params.duration;
                    craft.isCorrecting = inCorrectionPhase;
                } else {
                    craft.isCorrecting = false;
                }

                // Increment flight frame
                craft.flightFrame++;

                // Check for orbit insertion at end of transfer trajectory
                if (craft.trajectoryBuffer.length === 0 && craft.destinationBody) {
                    // Capture into orbit around destination body
                    const destBody = craft.destinationBody;

                    // Calculate orbital angle from craft position relative to destination
                    const dx = craft.x - destBody.x;
                    const dy = craft.y - destBody.y;
                    const orbitalAngle = Math.atan2(dy, dx);

                    // Determine orbit direction from incoming velocity
                    // Cross product of radius vector and relative velocity gives rotation sense
                    const relVx = craft.vx - destBody.vx;
                    const relVy = craft.vy - destBody.vy;
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
                    craft.vx = destBody.vx - orbitalDirection * orbitalSpeed * Math.sin(orbitalAngle);
                    craft.vy = destBody.vy + orbitalDirection * orbitalSpeed * Math.cos(orbitalAngle);

                    // Snap position to exact orbital altitude
                    craft.x = destBody.x + orbitRadius * Math.cos(orbitalAngle);
                    craft.y = destBody.y + orbitRadius * Math.sin(orbitalAngle);

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
            // Update orbital angle using orbitalDirection
            const orbitRadius = craft.parentBody.radius + craft.orbitalAltitude;
            // Angular velocity = orbital speed / orbit radius
            const orbitalSpeed = Math.sqrt(G * craft.parentBody.mass / orbitRadius);
            const angularVelocity = orbitalSpeed / orbitRadius;
            craft.orbitalAngle += craft.orbitalDirection * angularVelocity * dt * speedMultiplier;
            // Keep angle in [0, 2*PI] range
            if (craft.orbitalAngle > 2 * Math.PI) {
                craft.orbitalAngle -= 2 * Math.PI;
            } else if (craft.orbitalAngle < 0) {
                craft.orbitalAngle += 2 * Math.PI;
            }
        } else {
            // Free flight - position comes from trajectoryBuffer (popped in updatePhysics)
            // Here we just extend the buffer to maintain prediction length
            // BUT: if craft has a destination body, don't extend - trajectory ends at insertion

            if (!craft.destinationBody) {
                // Extend buffer to match predictionBuffer length (regular launch only)
                while (craft.trajectoryBuffer.length < predictionBuffer.length && predictionBuffer.length > 0) {
                    const lastState = craft.trajectoryBuffer.length > 0
                        ? craft.trajectoryBuffer[craft.trajectoryBuffer.length - 1]
                        : { x: craft.x, y: craft.y, vx: craft.vx, vy: craft.vy, isAccelerating: craft.isAccelerating };

                    const frameIndex = craft.trajectoryBuffer.length;
                    // Calculate the flight frame for this buffer position
                    // (current flight frame + buffer offset)
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
const TRANSFER_SEARCH_MIN_TIME = 5;  // Minimum time in the future to start searching (seconds)
const TRANSFER_SEARCH_MIN_FRAMES = Math.ceil(TRANSFER_SEARCH_MIN_TIME / PREDICTION_DT);
const MIN_TRAJECTORY_RUNWAY = 200;   // Minimum simulation time after launch to evaluate trajectory (seconds)
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
// 1 second of each other. Among nearby points, keep the one with earliest arrival.
// Returns array of {entry, originalIndex} sorted by launch time.
function getFilteredTrajectories() {
    const trajs = acceptableTrajectories;
    if (trajs.length === 0) return [];

    // Create indexed entries and sort by launch time
    const indexed = trajs.map((t, i) => ({ entry: t, originalIndex: i }));
    indexed.sort((a, b) => a.entry.launchFrame - b.entry.launchFrame);

    const THRESHOLD_SEC = 1.0;
    const filtered = [indexed[0]];

    for (let i = 1; i < indexed.length; i++) {
        const current = indexed[i];
        const last = filtered[filtered.length - 1];
        const launchDiffSec = (current.entry.launchFrame - last.entry.launchFrame) * PREDICTION_DT;

        if (launchDiffSec <= THRESHOLD_SEC) {
            // Within 1 second - keep the one with earlier arrival
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

    if (acceptableTrajectories.length === 0) {
        // Show container (for info bar) but clear the canvas
        const dpr = window.devicePixelRatio || 1;
        const rect = trajectoryPlotCanvas.getBoundingClientRect();
        trajectoryPlotCanvas.width = rect.width * dpr;
        trajectoryPlotCanvas.height = rect.height * dpr;
        trajectoryPlotCtx.clearRect(0, 0, trajectoryPlotCanvas.width, trajectoryPlotCanvas.height);
        return;
    }

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
    if (filtered.length === 0) return;

    // Compute data ranges from filtered trajectories
    let minLaunch = Infinity, maxLaunch = -Infinity;
    let minArrival = Infinity, maxArrival = -Infinity;
    for (const f of filtered) {
        const ls = f.entry.launchFrame * PREDICTION_DT;
        const as = f.entry.arrivalFrame * PREDICTION_DT;
        if (ls < minLaunch) minLaunch = ls;
        if (ls > maxLaunch) maxLaunch = ls;
        if (as < minArrival) minArrival = as;
        if (as > maxArrival) maxArrival = as;
    }

    // Add some padding to ranges
    const arrivalRange = maxArrival - minArrival || 1;
    const xMin = 0;
    const xMax = (predictionBuffer.length - MIN_TRAJECTORY_RUNWAY_FRAMES) * PREDICTION_DT;
    const yMin = minArrival - arrivalRange * 0.05;
    const yMax = maxArrival + arrivalRange * 0.05;

    // Plot area bounds (CSS pixels)
    const plotLeft = PLOT_PADDING_LEFT;
    const plotRight = w - PLOT_PADDING_RIGHT;
    const plotTop = PLOT_PADDING_TOP;
    const plotBottom = h - PLOT_PADDING_BOTTOM;
    const plotW = plotRight - plotLeft;
    const plotH = plotBottom - plotTop;

    // Map data to pixel coordinates
    function dataToPixel(launchSec, arrivalSec) {
        const px = plotLeft + ((launchSec - xMin) / (xMax - xMin)) * plotW;
        const py = plotBottom - ((arrivalSec - yMin) / (yMax - yMin)) * plotH;
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
    ctx.fillText('Launch (s)', (plotLeft + plotRight) / 2, h - 2);

    ctx.save();
    ctx.translate(12, (plotTop + plotBottom) / 2);
    ctx.rotate(-Math.PI / 2);
    ctx.fillText('Arrival (s)', 0, 0);
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
    // Find the filtered entry that matches the selected trajectory (or nearest)
    const clampedSelIdx = Math.min(selectedTrajectoryIndex, acceptableTrajectories.length - 1);
    let selFiltered = filtered[0];
    for (const f of filtered) {
        if (f.originalIndex === clampedSelIdx) {
            selFiltered = f;
            break;
        }
        // Pick the filtered entry closest by launch time to the selected trajectory
        const selLaunch = acceptableTrajectories[clampedSelIdx].launchFrame;
        if (Math.abs(f.entry.launchFrame - selLaunch) <
            Math.abs(selFiltered.entry.launchFrame - selLaunch)) {
            selFiltered = f;
        }
    }
    {
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

    const xMin = 0;
    const xMax = (predictionBuffer.length - MIN_TRAJECTORY_RUNWAY_FRAMES) * PREDICTION_DT;

    // Convert pixel to data space
    const dataX = xMin + ((x - plotLeft) / plotW) * (xMax - xMin);

    // Find nearest filtered trajectory by launch time, return its original index
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

// Update the plot and info bar once per second
setInterval(() => {
    const isActive = transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled';
    if (isActive) {
        if (acceptableTrajectories.length > 0) {
            updateTrajectoryPlot();
        }
        updateTrajectoryInfoBar();
    }
}, 1000);

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
            const launchSec = (transferBestFrame * PREDICTION_DT).toFixed(1);
            const arrivalSec = transferBestArrivalFrame === Infinity ? '--' : (transferBestArrivalFrame * PREDICTION_DT).toFixed(1);
            html += `<span><span class="info-label">Launch:</span> ${launchSec}s</span>`;
            html += `<span><span class="info-label">Arrival:</span> ${arrivalSec}s</span>`;
        }
        trajectoryInfoBar.innerHTML = html;

        scheduleLaunchBtn.disabled = acceptableTrajectories.length === 0;
        scheduleLaunchBtn.textContent = 'Schedule';
        scheduleLaunchBtn.style.display = '';
        cancelTransferBtn.textContent = 'Cancel';

    } else if (transferState === 'ready') {
        const launchSec = (transferBestFrame * PREDICTION_DT).toFixed(1);
        const arrivalSec = transferBestArrivalFrame === Infinity ? '--' : (transferBestArrivalFrame * PREDICTION_DT).toFixed(1);

        let html = `<span>Transfer to <strong>${transferDestinationBody.name}</strong></span>`;
        html += `<span><span class="info-label">Launch:</span> ${launchSec}s</span>`;
        html += `<span><span class="info-label">Arrival:</span> ${arrivalSec}s</span>`;
        html += `<span><span class="info-label">Score:</span> ${transferBestScore.toFixed(1)}</span>`;
        if (correctionDuration > 0) {
            const corrSec = (correctionDuration * PREDICTION_DT).toFixed(2);
            const corrDeg = (correctionAngle * 180 / Math.PI).toFixed(1);
            html += `<span><span class="info-label">Corr:</span> ${corrSec}s@${corrDeg}°</span>`;
        }
        trajectoryInfoBar.innerHTML = html;

        scheduleLaunchBtn.disabled = false;
        scheduleLaunchBtn.textContent = 'Schedule';
        scheduleLaunchBtn.style.display = '';
        cancelTransferBtn.textContent = 'Cancel';

    } else if (transferState === 'scheduled') {
        const launchSec = (transferScheduledFrame * PREDICTION_DT).toFixed(1);
        const arrivalSec = transferBestArrivalFrame === Infinity ? '--' : (transferBestArrivalFrame * PREDICTION_DT).toFixed(1);

        let html = `<span><strong>Launch Scheduled</strong> → ${transferDestinationBody.name}</span>`;
        html += `<span><span class="info-label">T-</span>${launchSec}s</span>`;
        html += `<span><span class="info-label">Arrival:</span> ${arrivalSec}s</span>`;
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
            const opacity = 0.3 * (1 - fadeProgress);

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
            // Hide trajectory
            craft.trajectoryPath.setAttribute('d', '');
            if (craft.trajectoryHitArea) craft.trajectoryHitArea.setAttribute('d', '');
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

        // Build solid path for entire trajectory (no fading for craft trajectories)
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
            for (let i = correctionStartFrame; i <= correctionEndFrame && i < craftPrediction.length; i++) {
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
    // Update accordion menu
    updateAccordionMenu();
}

// ===== Accordion Menu Logic =====

// Dirty tracking for accordion - only rebuild DOM when state changes
let _accordionLastOrigin = undefined;      // last origin body (or null)
let _accordionLastCraft = undefined;       // last selected craft (or null)
let _accordionLastDest = undefined;        // last destination body (or null)
let _accordionLastCraftCounts = '';        // serialised orbiting craft counts
let _accordionLastBufferReady = false;     // prediction buffer readiness
let _accordionLastPropProgress = -1;       // last propagation progress %
let _accordionDirty = true;               // force first build
let _accordionAnimating = false;          // true while selection animations are in progress

function markAccordionDirty() { _accordionDirty = true; }

// Sync dirty-tracking cache variables
function syncAccordionCache() {
    _accordionLastOrigin = accordionOrigin;
    _accordionLastCraft = accordionCraft;
    _accordionLastDest = accordionDestination;
    _accordionLastCraftCounts = getOrbitingCountKey();
    _accordionLastBufferReady = predictionBuffer.length >= PREDICTION_FRAMES;
    _accordionLastPropProgress = Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100);
    _accordionDirty = false;
}

// --- Accordion animation constants ---
const ACCORDION_SLIDE_MS = 250;
const ACCORDION_INFO_MS = 280;
const ACCORDION_INFO_DELAY = 100;

// FLIP animation: captures old positions, rebuilds DOM, then animates items to new positions
function flipAnimateList(listEl, buildFn) {
    if (!listEl) { buildFn(); return; }

    // Capture old positions keyed by body-name or craft-index
    const oldRects = new Map();
    const selector = '.accordion-planet-item, .accordion-craft-item, .accordion-dest-item';
    for (const el of listEl.querySelectorAll(selector)) {
        const key = el.dataset.bodyName || el.dataset.craftIndex;
        if (key !== undefined) {
            oldRects.set(key, el.getBoundingClientRect());
        }
    }

    // Rebuild DOM (new order, info cards start collapsed)
    buildFn();

    if (oldRects.size === 0) return;

    // Calculate deltas and apply inverse transforms
    const newItems = listEl.querySelectorAll(selector);
    const animating = [];

    for (const el of newItems) {
        const key = el.dataset.bodyName || el.dataset.craftIndex;
        if (key !== undefined && oldRects.has(key)) {
            const oldRect = oldRects.get(key);
            const newRect = el.getBoundingClientRect();
            const dy = oldRect.top - newRect.top;
            if (Math.abs(dy) > 1) {
                el.style.transform = `translateY(${dy}px)`;
                el.style.transition = 'none';
                animating.push(el);
            }
        }
    }

    if (animating.length === 0) return;

    // Force reflow then play animation
    void listEl.offsetHeight;
    for (const el of animating) {
        el.style.transition = `transform ${ACCORDION_SLIDE_MS}ms cubic-bezier(0.25, 0.46, 0.45, 0.94)`;
        el.style.transform = '';
    }

    // Clean up inline styles after animation
    setTimeout(() => {
        for (const el of animating) {
            el.style.transition = '';
            el.style.transform = '';
        }
    }, ACCORDION_SLIDE_MS + 20);
}

// Expand collapsed info cards within a list, adjusting parent section max-height
function expandInfoCards(listEl) {
    if (!listEl) return;
    const section = listEl.closest('.accordion-section');
    const cards = listEl.querySelectorAll(
        '.accordion-planet-info-inline:not(.expanded), .accordion-dest-lore-inline:not(.expanded)');

    for (const card of cards) {
        // Measure natural height by temporarily removing constraints
        const saved = card.style.maxHeight;
        card.style.transition = 'none';
        card.style.maxHeight = 'none';
        const fullHeight = card.scrollHeight;
        card.style.maxHeight = saved || '0px';
        void card.offsetHeight; // force reflow
        card.style.transition = '';

        // Trigger expansion
        card.classList.add('expanded');
        card.style.maxHeight = fullHeight + 'px';

        // Grow parent section to accommodate
        if (section && section.classList.contains('open')) {
            const curMax = parseInt(section.style.maxHeight) || section.scrollHeight;
            if (!isAccordionMobile()) {
                section.style.maxHeight = (curMax + fullHeight) + 'px';
            } else {
                section.style.maxHeight = (curMax + fullHeight) + 'px';
            }
        }
    }
}

// Collapse expanded info cards, returns a Promise that resolves when animation finishes
function collapseInfoCards(listEl) {
    if (!listEl) return Promise.resolve();
    const cards = listEl.querySelectorAll(
        '.accordion-planet-info-inline.expanded, .accordion-dest-lore-inline.expanded');
    if (cards.length === 0) return Promise.resolve();

    const section = listEl.closest('.accordion-section');

    for (const card of cards) {
        const curHeight = card.scrollHeight;
        card.classList.remove('expanded');
        card.style.maxHeight = '0px';

        // Shrink parent section
        if (section && section.classList.contains('open')) {
            const curMax = parseInt(section.style.maxHeight) || section.scrollHeight;
            section.style.maxHeight = Math.max(0, curMax - curHeight) + 'px';
        }
    }

    return new Promise(resolve => setTimeout(resolve, ACCORDION_INFO_MS));
}

// Re-measure an open section after content changes
function remeasureSection(section) {
    if (!section || !section.classList.contains('open')) return;
    requestAnimationFrame(() => {
        requestAnimationFrame(() => {
            if (isAccordionMobile()) {
                section.style.maxHeight = section.scrollHeight + 'px';
            } else {
                section.style.maxWidth = section.scrollWidth + 'px';
                section.style.maxHeight = section.scrollHeight + 'px';
            }
        });
    });
}

// Rebuild sub-lists (craft + dest) based on current accordion state
function rebuildSubLists() {
    if (accordionOrigin) {
        buildAccordionCraftList();
    } else {
        const craftList = document.getElementById('accordion-craft-list');
        if (craftList) craftList.innerHTML = '';
        const destList = document.getElementById('accordion-dest-list');
        if (destList) destList.innerHTML = '';
    }
    if (accordionCraft) {
        buildAccordionDestList();
    } else {
        const destList = document.getElementById('accordion-dest-list');
        if (destList) destList.innerHTML = '';
    }
}

function getOrbitingCountKey() {
    const counts = [];
    for (const body of bodies) {
        let n = 0;
        for (const c of crafts) {
            if (c.state === 'orbiting' && c.parentBody === body) n++;
        }
        counts.push(n);
    }
    return counts.join(',');
}

function buildAccordionOriginList() {
    const listEl = document.getElementById('accordion-origin-list');
    if (!listEl) return;

    const orbitingCountByBody = new Map();
    for (const craft of crafts) {
        if (craft.state === 'orbiting' && craft.parentBody) {
            orbitingCountByBody.set(craft.parentBody, (orbitingCountByBody.get(craft.parentBody) || 0) + 1);
        }
    }

    // Sort: selected planet first, then the rest in original order
    const sortedBodies = accordionOrigin
        ? [accordionOrigin, ...bodies.filter(b => b !== accordionOrigin)]
        : [...bodies];

    let html = '';
    for (const body of sortedBodies) {
        const craftCount = orbitingCountByBody.get(body) || 0;
        const isSelected = accordionOrigin === body;
        const isDimmed = accordionOrigin && !isSelected;
        const classes = ['accordion-planet-item'];
        if (isSelected) classes.push('selected-origin');
        if (isDimmed) classes.push('dimmed');

        html += `<div class="${classes.join(' ')}" data-body-name="${body.name}">
            <span class="accordion-planet-dot" style="background-color: ${body.color};"></span>
            <span class="accordion-planet-name">${body.name}</span>
            ${craftCount > 0 ? `<span class="accordion-craft-badge">${craftCount}</span>` : ''}
        </div>`;

        // Inline planet info immediately beneath the selected origin
        if (isSelected) {
            const lore = planetLore[body.name] || { desc: 'Unknown world.', stats: '' };
            const orbitingCraft = crafts.filter(c => c.parentBody === body && c.state === 'orbiting');
            html += `<div class="accordion-planet-info-inline">
                <div class="planet-info-stats">
                    <span class="info-label">Mass</span><span class="info-value">${body.mass.toFixed(1)}</span>
                    <span class="info-label">Radius</span><span class="info-value">${body.radius.toFixed(1)}</span>
                    <span class="info-label">Craft</span><span class="info-value">${orbitingCraft.length}</span>
                </div>
                <div class="planet-info-lore">${lore.desc}</div>
            </div>`;
        }
    }
    listEl.innerHTML = html;
}

function buildAccordionCraftList() {
    const listEl = document.getElementById('accordion-craft-list');
    if (!listEl || !accordionOrigin) return;

    const orbitingCraft = crafts.filter(c => c.parentBody === accordionOrigin && c.state === 'orbiting');
    const bufferReady = predictionBuffer.length >= PREDICTION_FRAMES;

    if (orbitingCraft.length === 0) {
        listEl.innerHTML = `<div class="accordion-no-craft">
            <span class="no-craft-badge">None</span>
            <span>No craft in orbit</span>
        </div>`;
        return;
    }

    let html = '';
    for (let i = 0; i < orbitingCraft.length; i++) {
        const craft = orbitingCraft[i];
        const idx = crafts.indexOf(craft);
        const isSelected = accordionCraft === craft;

        html += `<div class="accordion-craft-item${isSelected ? ' selected-craft' : ''}" data-craft-index="${idx}">
            <img src="spaceship.svg" class="accordion-craft-icon" alt="craft" />
            <span class="accordion-planet-name">Craft ${i + 1}</span>
        </div>`;
    }

    if (!bufferReady) {
        const progress = Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100);
        html += `<div class="accordion-propagation">
            <span>Propagating</span>
            <div class="propagation-bar"><div class="propagation-fill" style="width: ${progress}%"></div></div>
            <span>${progress}%</span>
        </div>`;
    }

    listEl.innerHTML = html;
}

function buildAccordionDestList() {
    const listEl = document.getElementById('accordion-dest-list');
    if (!listEl || !accordionOrigin) return;

    // Sort: selected destination first, then rest in original order (excluding origin)
    const availableBodies = bodies.filter(b => b !== accordionOrigin);
    const sortedDest = accordionDestination
        ? [accordionDestination, ...availableBodies.filter(b => b !== accordionDestination)]
        : availableBodies;

    let html = '';
    for (const body of sortedDest) {
        const isSelected = accordionDestination === body;

        html += `<div class="accordion-dest-item${isSelected ? ' selected-dest' : ''}" data-body-name="${body.name}">
            <span class="accordion-planet-dot" style="background-color: ${body.color};"></span>
            <span class="accordion-planet-name">${body.name}</span>
        </div>`;

        // Inline destination lore immediately beneath the selected destination
        if (isSelected) {
            const lore = destinationLore[body.name] || 'Destination locked.';
            html += `<div class="accordion-dest-lore-inline">${lore}</div>`;
        }
    }
    listEl.innerHTML = html;
}

function isAccordionMobile() {
    return window.matchMedia('(max-width: 768px)').matches;
}

function openSection(section) {
    if (!section) return;
    section.classList.add('open');
    // Double-rAF ensures DOM has laid out content before measuring
    requestAnimationFrame(() => {
        requestAnimationFrame(() => {
            if (isAccordionMobile()) {
                section.style.maxWidth = '';
                section.style.maxHeight = section.scrollHeight + 'px';
            } else {
                // Set both axes to measured values for tight, smooth animation
                section.style.maxWidth = section.scrollWidth + 'px';
                section.style.maxHeight = section.scrollHeight + 'px';
            }
        });
    });
}

function closeSection(section) {
    if (!section) return;
    section.classList.remove('open');
    section.classList.remove('collapsed');
    if (isAccordionMobile()) {
        section.style.maxWidth = '';
        section.style.maxHeight = '0';
    } else {
        section.style.maxWidth = '0';
        section.style.maxHeight = '0';
    }
}

function applyAccordionSections() {
    const originSection = document.getElementById('accordion-origin');
    const craftSection = document.getElementById('accordion-craft');
    const destSection = document.getElementById('accordion-dest');
    const launchSection = document.getElementById('accordion-launch-section');

    const hasOrigin = !!accordionOrigin;
    const hasCraft = !!accordionCraft;
    const hasDest = !!accordionDestination;

    // Determine overall state color for selected item borders
    const stateColor = hasDest
        ? 'var(--accordion-line-emerald)'
        : hasCraft
            ? 'var(--accordion-line-amber)'
            : null;

    // Update selected item borders to reflect state
    const selectedOrigin = originSection && originSection.querySelector('.selected-origin');
    if (selectedOrigin) {
        selectedOrigin.style.borderColor = stateColor || 'rgba(136, 170, 255, 0.3)';
    }
    const selectedCraft = craftSection && craftSection.querySelector('.selected-craft');
    if (selectedCraft) {
        selectedCraft.style.borderColor = stateColor || 'rgba(251, 191, 36, 0.3)';
    }
    const selectedDest = destSection && destSection.querySelector('.selected-dest');
    if (selectedDest) {
        selectedDest.style.borderColor = hasDest ? 'rgba(52, 211, 153, 0.4)' : 'rgba(52, 211, 153, 0.3)';
    }

    // Update section headers dynamically
    const originHeader = originSection && originSection.querySelector('.accordion-section-header');
    const craftHeader = craftSection && craftSection.querySelector('.accordion-section-header');
    const destHeader = destSection && destSection.querySelector('.accordion-section-header');

    if (originHeader) {
        originHeader.textContent = hasOrigin ? `Origin: ${accordionOrigin.name}` : 'Select Origin';
    }
    if (craftHeader) {
        craftHeader.textContent = hasCraft ? `Craft: Selected` : 'Select Craft';
    }
    if (destHeader) {
        destHeader.textContent = hasDest ? `Dest: ${accordionDestination.name}` : 'Select Destination';
    }

    // Origin section always open
    openSection(originSection);

    // Section 2: craft (shown when origin selected)
    if (hasOrigin) {
        openSection(craftSection);
    } else {
        closeSection(craftSection);
    }

    // Section 3: destination (shown when craft selected)
    if (hasCraft) {
        openSection(destSection);
    } else {
        closeSection(destSection);
    }

    // Section 4: launch (shown when all selected)
    if (hasOrigin && hasCraft && hasDest) {
        openSection(launchSection);
    } else {
        closeSection(launchSection);
    }

    // Mobile: auto-collapse completed sections, expand the active one
    if (isAccordionMobile()) {
        // Determine which section is currently "active" (the latest open one needing input)
        let activeSection = null;
        if (hasOrigin && hasCraft && hasDest) {
            activeSection = launchSection;
        } else if (hasCraft) {
            activeSection = destSection;
        } else if (hasOrigin) {
            activeSection = craftSection;
        } else {
            activeSection = originSection;
        }

        // Collapse all completed sections, expand the active one
        const allSections = [originSection, craftSection, destSection, launchSection];
        for (const sec of allSections) {
            if (!sec || !sec.classList.contains('open')) continue;
            if (sec === activeSection) {
                sec.classList.remove('collapsed');
            } else {
                sec.classList.add('collapsed');
            }
        }
    }
}

// Called from user interactions — forces a full rebuild + section update
function rebuildAccordion() {
    buildAccordionOriginList();
    if (accordionOrigin) {
        buildAccordionCraftList();
    } else {
        // Clear sub-sections when no origin
        const craftList = document.getElementById('accordion-craft-list');
        if (craftList) craftList.innerHTML = '';
        const destList = document.getElementById('accordion-dest-list');
        if (destList) destList.innerHTML = '';
    }
    if (accordionCraft) {
        buildAccordionDestList();
    } else {
        const destList = document.getElementById('accordion-dest-list');
        if (destList) destList.innerHTML = '';
    }
    applyAccordionSections();

    // Instantly expand any info cards (non-animated rebuild path)
    const originList = document.getElementById('accordion-origin-list');
    const destList2 = document.getElementById('accordion-dest-list');
    if (originList) {
        for (const card of originList.querySelectorAll('.accordion-planet-info-inline:not(.expanded)')) {
            card.classList.add('expanded');
            card.style.maxHeight = 'none';
        }
    }
    if (destList2) {
        for (const card of destList2.querySelectorAll('.accordion-dest-lore-inline:not(.expanded)')) {
            card.classList.add('expanded');
            card.style.maxHeight = 'none';
        }
    }

    syncAccordionCache();
}

// Called every render frame — only touches the DOM when something changed
function updateAccordionMenu() {
    if (_accordionAnimating) return; // Skip during selection animations

    const menu = document.getElementById('accordion-menu');
    if (!menu) return;

    // Hide accordion when transfer is actively searching/ready/scheduled
    if (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') {
        menu.classList.add('hidden-menu');
        return;
    }
    menu.classList.remove('hidden-menu');

    // If a craft in transit is selected, show the old panel for that
    if (selectedCraft && selectedCraft.state === 'free') {
        menu.classList.add('hidden-menu');
        const infoDiv = document.getElementById('selected-body-info');
        infoDiv.style.display = 'block';
        return;
    } else {
        const infoDiv = document.getElementById('selected-body-info');
        if (transferState === 'none') infoDiv.style.display = 'none';
    }

    // Check if anything actually changed
    const craftCountKey = getOrbitingCountKey();
    const bufferReady = predictionBuffer.length >= PREDICTION_FRAMES;
    const propProgress = Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100);

    const stateChanged =
        _accordionDirty ||
        _accordionLastOrigin !== accordionOrigin ||
        _accordionLastCraft !== accordionCraft ||
        _accordionLastDest !== accordionDestination ||
        _accordionLastCraftCounts !== craftCountKey ||
        _accordionLastBufferReady !== bufferReady ||
        (!bufferReady && _accordionLastPropProgress !== propProgress);

    if (!stateChanged) return; // Nothing changed, skip DOM work

    rebuildAccordion();
}

// Handle accordion origin selection (animated)
function handleAccordionOriginSelect(body) {
    if (_accordionAnimating) return;

    const listEl = document.getElementById('accordion-origin-list');
    const wasSelected = accordionOrigin === body;
    const hadSelection = !!accordionOrigin;

    function doAnimation() {
        _accordionAnimating = true;

        if (wasSelected) {
            // Deselect
            accordionOrigin = null;
            accordionCraft = null;
            accordionDestination = null;
            selectedBody = null;
            isTrackingSelectedBody = false;
        } else {
            // New / changed selection
            accordionOrigin = body;
            accordionCraft = null;
            accordionDestination = null;
            selectedBody = body;
            selectedCraft = null;
            isTrackingSelectedBody = true;
            isTrackingSelectedCraft = false;
        }

        // FLIP items to new positions
        flipAnimateList(listEl, () => buildAccordionOriginList());

        // Expand info card after short delay (if selecting)
        if (!wasSelected) {
            setTimeout(() => {
                expandInfoCards(listEl);
            }, ACCORDION_INFO_DELAY);
        }

        // Update sub-lists and sections
        rebuildSubLists();
        applyAccordionSections();
        syncAccordionCache();

        // Final cleanup: re-measure and unlock
        const totalMs = wasSelected
            ? ACCORDION_SLIDE_MS
            : (ACCORDION_INFO_DELAY + ACCORDION_INFO_MS);
        setTimeout(() => {
            _accordionAnimating = false;
            remeasureSection(listEl.closest('.accordion-section'));
        }, totalMs + 50);
    }

    // If there's an existing info card, collapse it first
    if (hadSelection) {
        _accordionAnimating = true;
        collapseInfoCards(listEl).then(() => {
            _accordionAnimating = false;
            doAnimation();
        });
    } else {
        doAnimation();
    }
}

// Handle accordion craft selection (no reorder animation needed)
function handleAccordionCraftSelect(craft) {
    if (_accordionAnimating) return;

    if (accordionCraft === craft) {
        accordionCraft = null;
        accordionDestination = null;
    } else {
        accordionCraft = craft;
        accordionDestination = null;
    }
    rebuildAccordion();
}

// Handle accordion destination selection (animated)
function handleAccordionDestSelect(body) {
    if (_accordionAnimating) return;

    const listEl = document.getElementById('accordion-dest-list');
    const wasSelected = accordionDestination === body;
    const hadSelection = !!accordionDestination;

    function doAnimation() {
        _accordionAnimating = true;

        if (wasSelected) {
            accordionDestination = null;
        } else {
            accordionDestination = body;
        }

        // FLIP items to new positions
        flipAnimateList(listEl, () => buildAccordionDestList());

        // Expand lore card after short delay (if selecting)
        if (!wasSelected) {
            setTimeout(() => {
                expandInfoCards(listEl);
            }, ACCORDION_INFO_DELAY);
        }

        // Update sections (may open/close launch)
        applyAccordionSections();
        syncAccordionCache();

        // Final cleanup
        const totalMs = wasSelected
            ? ACCORDION_SLIDE_MS
            : (ACCORDION_INFO_DELAY + ACCORDION_INFO_MS);
        setTimeout(() => {
            _accordionAnimating = false;
            remeasureSection(listEl.closest('.accordion-section'));
        }, totalMs + 50);
    }

    // If there's an existing lore card, collapse it first
    if (hadSelection) {
        _accordionAnimating = true;
        collapseInfoCards(listEl).then(() => {
            _accordionAnimating = false;
            doAnimation();
        });
    } else {
        doAnimation();
    }
}

// Handle accordion launch button click
function handleAccordionLaunch() {
    if (!accordionOrigin || !accordionCraft || !accordionDestination) return;

    // Set up transfer state to match existing logic
    transferSourceBody = accordionOrigin;
    transferCraft = accordionCraft;
    transferDestinationBody = accordionDestination;
    selectedBody = accordionOrigin;

    // Start transfer search (existing mechanism)
    startTransferSearch();

    // Reset accordion state
    accordionOrigin = null;
    accordionCraft = null;
    accordionDestination = null;
    markAccordionDirty();
}

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
    // Note: 'selecting_destination' is now handled by the accordion menu
    if (transferState === 'selecting_destination') {
        infoDiv.style.display = 'none';
        return;
    }

    if (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') {
        // Update info bar and buttons in the trajectory plot panel
        updateTrajectoryInfoBar();
        // Hide the side panel during these states
        infoDiv.style.display = 'none';
        delete infoDiv.dataset.transferState;
        return;
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

        if (craft.state === 'orbiting') {
            locationInfo = `<div class="info-row">
                <span class="info-label">Orbiting:</span>
                <span class="info-value">${craft.parentBody.name}</span>
            </div>`;
        } else if (craft.state === 'free') {
            if (craft.destinationBody) {
                // In transfer flight
                const framesLeft = craft.trajectoryBuffer.length;
                const timeToArrival = (framesLeft * PREDICTION_DT).toFixed(1);

                locationInfo = `<div class="info-row">
                    <span class="info-label">From:</span>
                    <span class="info-value">${craft.launchedFromBody ? craft.launchedFromBody.name : 'Unknown'}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">To:</span>
                    <span class="info-value">${craft.destinationBody.name}</span>
                </div>`;

                // Time to arrival
                transferInfo = `<div class="info-row">
                    <span class="info-label">Arrival in:</span>
                    <span class="info-value" id="craft-arrival">${timeToArrival}s</span>
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
                            <span class="info-value" id="craft-correction">${timeToCorrection}s</span>
                        </div>`;
                    } else if (craft.flightFrame < correctionEnd) {
                        // Currently correcting
                        const framesRemaining = correctionEnd - craft.flightFrame;
                        const timeRemaining = (framesRemaining * PREDICTION_DT).toFixed(1);
                        transferInfo += `<div class="info-row">
                            <span class="info-label">Correcting:</span>
                            <span class="info-value" id="craft-correction" style="color: red;">${timeRemaining}s left</span>
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
                arrivalEl.textContent = timeToArrival + 's';
            }

            if (correctionEl && craft.correctionParams) {
                const correctionStart = craft.correctionParams.startFrame;
                const correctionEnd = correctionStart + craft.correctionParams.duration;

                if (craft.flightFrame < correctionStart) {
                    const framesToCorrection = correctionStart - craft.flightFrame;
                    const timeToCorrection = (framesToCorrection * PREDICTION_DT).toFixed(1);
                    correctionEl.textContent = timeToCorrection + 's';
                    correctionEl.style.color = '';
                } else if (craft.flightFrame < correctionEnd) {
                    const framesRemaining = correctionEnd - craft.flightFrame;
                    const timeRemaining = (framesRemaining * PREDICTION_DT).toFixed(1);
                    correctionEl.textContent = timeRemaining + 's left';
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

    // The accordion menu now handles body selection and transfer initiation.
    // The old info panel is only used for in-transit craft display (handled above).
    // Hide the old panel; the accordion will show instead.
    infoDiv.style.display = 'none';
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
            // Reset accordion
            accordionOrigin = null;
            accordionCraft = null;
            accordionDestination = null;
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
                // Sync accordion: select this body as origin
                if (transferState === 'none') {
                    accordionOrigin = clicked;
                    accordionCraft = null;
                    accordionDestination = null;
                }
            } else {
                // Clicked empty space: deselect accordion
                accordionOrigin = null;
                accordionCraft = null;
                accordionDestination = null;
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
            // Sync accordion
            if (transferState === 'none') {
                accordionOrigin = touchedBody;
                accordionCraft = null;
                accordionDestination = null;
            }
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
                    // Reset accordion
                    accordionOrigin = null;
                    accordionCraft = null;
                    accordionDestination = null;
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
        // Track selected body
        camera.x = selectedBody.x;
        camera.y = selectedBody.y;
    } else if (!selectedBody && !selectedCraft && !isAutoFitPaused) {
        // Auto-fit all bodies when nothing selected
        fitAllBodies();
    }

    // Update popover trigger and Fit All active state
    const popoverTriggerEl = document.getElementById('popover-trigger');
    const isAutoFitActive = !selectedBody && !selectedCraft && !isAutoFitPaused;
    popoverTriggerEl.classList.toggle('active', isAutoFitActive);
    const fitAllItemEl = document.getElementById('fit-all-item');
    fitAllItemEl.classList.toggle('active', isAutoFitActive);
    const fitAllBadgeEl = document.getElementById('fit-all-badge');
    fitAllBadgeEl.classList.toggle('hidden', !isAutoFitActive);
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

    updatePhysics(dt);
    updateCrafts(dt);
    updateTransferSearch();
    updateCameraTracking();
    render();
    updateTrajectories();

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
            console.log(`[CPU Benchmark] CPU: ${cpuPercent.toFixed(1)}% | Avg frame: ${avgFrameTime.toFixed(2)}ms | Frames: ${benchmarkFrameCount} | Elapsed: ${(elapsedMs/1000).toFixed(1)}s`);

            // Reset counters for next interval
            benchmarkLastReportTime = timestamp;
            benchmarkTotalWorkTime = 0;
            benchmarkFrameCount = 0;
        }
    }

    requestAnimationFrame(gameLoop);
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

    // Helper to reset speed to 1x
    function resetSpeed() {
        speedMultiplier = 1;
        const speedBtn = document.getElementById('speed-btn');
        speedBtn.textContent = '1x';
        speedBtn.title = 'Speed: 1x';
        speedBtn.classList.remove('fast');
    }

    // Speed button - cycles through 1x, 2x, 4x, 8x, 16x
    document.getElementById('speed-btn').addEventListener('click', () => {
        if (speedMultiplier >= 16) {
            resetSpeed();
        } else {
            speedMultiplier *= 2;
            const speedBtn = document.getElementById('speed-btn');
            speedBtn.textContent = speedMultiplier + 'x';
            speedBtn.title = 'Speed: ' + speedMultiplier + 'x';
            speedBtn.classList.add('fast');
        }
        // Unpause if paused when fast forwarding
        if (isPaused && speedMultiplier > 1) {
            isPaused = false;
            document.getElementById('pause-btn').textContent = '⏸';
            document.getElementById('pause-btn').classList.remove('active');
        }
    });

    // Pause button
    document.getElementById('pause-btn').addEventListener('click', () => {
        isPaused = !isPaused;
        document.getElementById('pause-btn').textContent = isPaused ? '▶' : '⏸';
        document.getElementById('pause-btn').classList.toggle('active', isPaused);
        // Reset speed to 1x when using pause/play
        resetSpeed();
    });

    // Theme toggle
    const themeToggle = document.getElementById('theme-toggle');
    function getSystemTheme() {
        return window.matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark';
    }
    function getCurrentTheme() {
        return document.documentElement.getAttribute('data-theme') || getSystemTheme();
    }
    const savedTheme = localStorage.getItem('theme');
    if (savedTheme) {
        document.documentElement.setAttribute('data-theme', savedTheme);
    }
    themeToggle.addEventListener('click', () => {
        const current = getCurrentTheme();
        const next = current === 'dark' ? 'light' : 'dark';
        document.documentElement.setAttribute('data-theme', next);
        localStorage.setItem('theme', next);
    });

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
        resetSpeed();
        isPaused = false;
        document.getElementById('pause-btn').textContent = '⏸';
        document.getElementById('pause-btn').classList.remove('active');
        selectedBody = null;
        selectedCraft = null;
        hoveredBody = null;
        isAutoFitPaused = false;
        isTrackingSelectedBody = true;
        isTrackingSelectedCraft = false;
        accordionOrigin = null;
        accordionCraft = null;
        accordionDestination = null;
        accordionBuilt = false;
        camera = { x: 0, y: 0, zoom: 1 };
        closeControlsPopover();
    });

    // Fit All item in popover
    document.getElementById('fit-all-item').addEventListener('click', () => {
        isTrackingSelectedBody = false;
        isTrackingSelectedCraft = false;
        isAutoFitPaused = false;
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
