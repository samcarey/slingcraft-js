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
const PREDICTION_TIME = 90; // Predict 90 seconds ahead
const SOLID_PREDICTION_TIME = 60; // First 60 seconds are solid
const PREDICTION_DT = 0.033; // Fixed timestep for prediction (~30fps)
const PREDICTION_FRAMES = Math.ceil(PREDICTION_TIME / PREDICTION_DT);
const SOLID_PREDICTION_FRAMES = Math.ceil(SOLID_PREDICTION_TIME / PREDICTION_DT);
const MAX_TRAJECTORY_POINTS = 100; // Max points to render for solid portion
const MAX_CATCHUP_FRAMES = 5; // Max frames to simulate per render frame

// Game state
let bodies = [];
let selectedBody = null;
let hoveredBody = null;
let isPaused = false;
let lastTime = 0;

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
        this.trajectoryFadePath = null; // Single fade path with gradient
        this.trajectoryFadeGradient = null;
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

        // Create gradient for fade path (opacity fades from 0.6 to 0)
        this.trajectoryFadeGradient = document.createElementNS(SVG_NS, 'linearGradient');
        this.trajectoryFadeGradient.id = `trajectory-fade-${this.name}`;
        this.trajectoryFadeGradient.setAttribute('gradientUnits', 'userSpaceOnUse');

        const stopStart = document.createElementNS(SVG_NS, 'stop');
        stopStart.setAttribute('offset', '0%');
        stopStart.setAttribute('stop-color', strokeColor);
        stopStart.setAttribute('stop-opacity', '0.6');

        const stopEnd = document.createElementNS(SVG_NS, 'stop');
        stopEnd.setAttribute('offset', '100%');
        stopEnd.setAttribute('stop-color', strokeColor);
        stopEnd.setAttribute('stop-opacity', '0');

        this.trajectoryFadeGradient.appendChild(stopStart);
        this.trajectoryFadeGradient.appendChild(stopEnd);
        defs.appendChild(this.trajectoryFadeGradient);

        // Create single fade path with gradient stroke
        this.trajectoryFadePath = document.createElementNS(SVG_NS, 'path');
        this.trajectoryFadePath.setAttribute('class', 'trajectory-path');
        this.trajectoryFadePath.style.stroke = `url(#trajectory-fade-${this.name})`;
        trajectoriesLayer.appendChild(this.trajectoryFadePath);
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
        if (this.trajectoryFadePath) {
            this.trajectoryFadePath.remove();
        }
        if (this.trajectoryFadeGradient) {
            this.trajectoryFadeGradient.remove();
        }
        // Remove glow gradient from defs
        const gradient = defs.querySelector(`#glow-${this.name}`);
        if (gradient) {
            gradient.remove();
        }
    }
}

// Initialize bodies
function initBodies() {
    // Remove old body elements
    for (const body of bodies) {
        body.removeElements();
    }
    bodies = [];

    // Central large body (like a star/planet)
    const central = new CelestialBody(0, 0, 80, '#ffaa44', 'Sol');
    central.mass = 1000; // Override mass for central body
    central.createElements();
    bodies.push(central);

    // Orbiting body 1
    const body1 = new CelestialBody(200, 0, 25, '#4488ff', 'Terra');
    body1.mass = 50;
    // Calculate orbital velocity
    const dist1 = 200;
    const orbitalSpeed1 = Math.sqrt(G * central.mass / dist1);
    body1.vy = orbitalSpeed1;
    body1.createElements();
    bodies.push(body1);

    // Orbiting body 2
    const body2 = new CelestialBody(-350, 0, 35, '#88ff88', 'Gaia');
    body2.mass = 80;
    const dist2 = 350;
    const orbitalSpeed2 = Math.sqrt(G * central.mass / dist2);
    body2.vy = -orbitalSpeed2;
    body2.createElements();
    bodies.push(body2);

    // Small moon orbiting body 1
    const moon = new CelestialBody(200, -50, 10, '#aaaaaa', 'Luna');
    moon.mass = 5;
    const moonDist = 50;
    const moonOrbitalSpeed = Math.sqrt(G * body1.mass / moonDist);
    moon.vx = -moonOrbitalSpeed;
    moon.vy = orbitalSpeed1; // Also inherit parent's orbital velocity
    moon.createElements();
    bodies.push(moon);
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
        for (let i = sampleOffset; i < predictionBuffer.length; i += SAMPLE_INTERVAL) {
            const state = predictionBuffer[i][bodyIndex];
            points.push({
                screen: worldToScreen(state.x, state.y),
                frame: i
            });
        }

        // Build solid portion path (first 60 seconds)
        const startScreen = worldToScreen(body.x, body.y);
        let solidPath = `M ${startScreen.x} ${startScreen.y}`;

        let lastSolidPoint = null;
        for (const point of points) {
            if (point.frame >= SOLID_PREDICTION_FRAMES) break;
            solidPath += ` L ${point.screen.x} ${point.screen.y}`;
            lastSolidPoint = point;
        }
        body.trajectoryPath.setAttribute('d', solidPath);

        // Build fade path (last 30 seconds) with gradient
        if (!body.trajectoryFadePath || !body.trajectoryFadeGradient) continue;

        // Get fade points
        const fadePoints = points.filter(p => p.frame >= SOLID_PREDICTION_FRAMES);

        if (fadePoints.length === 0) {
            body.trajectoryFadePath.setAttribute('d', '');
            continue;
        }

        // Build fade path, starting from last solid point for continuity
        let fadePath = '';
        if (lastSolidPoint) {
            fadePath = `M ${lastSolidPoint.screen.x} ${lastSolidPoint.screen.y}`;
            for (const point of fadePoints) {
                fadePath += ` L ${point.screen.x} ${point.screen.y}`;
            }
        } else {
            fadePath = `M ${fadePoints[0].screen.x} ${fadePoints[0].screen.y}`;
            for (let i = 1; i < fadePoints.length; i++) {
                fadePath += ` L ${fadePoints[i].screen.x} ${fadePoints[i].screen.y}`;
            }
        }
        body.trajectoryFadePath.setAttribute('d', fadePath);

        // Update gradient coordinates from start to end of fade
        const gradientStart = lastSolidPoint ? lastSolidPoint.screen : fadePoints[0].screen;
        const gradientEnd = fadePoints[fadePoints.length - 1].screen;

        body.trajectoryFadeGradient.setAttribute('x1', gradientStart.x);
        body.trajectoryFadeGradient.setAttribute('y1', gradientStart.y);
        body.trajectoryFadeGradient.setAttribute('x2', gradientEnd.x);
        body.trajectoryFadeGradient.setAttribute('y2', gradientEnd.y);
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

    if (selectedBody) {
        infoDiv.innerHTML = `
            <h3><span class="body-indicator" style="background-color: ${selectedBody.color}"></span>${selectedBody.name}</h3>
            <div class="info-row">
                <span class="info-label">Mass:</span>
                <span class="info-value">${selectedBody.mass.toFixed(1)}</span>
            </div>
            <div class="info-row">
                <span class="info-label">Radius:</span>
                <span class="info-value">${selectedBody.radius.toFixed(1)}</span>
            </div>
            <div class="info-row">
                <span class="info-label">Position:</span>
                <span class="info-value">(${selectedBody.x.toFixed(0)}, ${selectedBody.y.toFixed(0)})</span>
            </div>
            <div class="info-row">
                <span class="info-label">Speed:</span>
                <span class="info-value">${selectedBody.speed.toFixed(1)}</span>
            </div>
            <div class="info-row">
                <span class="info-label">Kinetic E:</span>
                <span class="info-value">${selectedBody.kineticEnergy.toFixed(1)}</span>
            </div>
        `;
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
        }
        infoDiv.style.display = 'block';
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
        // Click on a body to select and start tracking it
        const clicked = findBodyAtPosition(x, y);
        selectedBody = clicked;
        if (clicked) {
            isTrackingSelectedBody = true;
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

// Calculate bounding box of all bodies
function calculateBoundingBox() {
    if (bodies.length === 0) return { minX: 0, maxX: 0, minY: 0, maxY: 0 };

    let minX = Infinity, maxX = -Infinity;
    let minY = Infinity, maxY = -Infinity;

    for (const body of bodies) {
        minX = Math.min(minX, body.x - body.radius);
        maxX = Math.max(maxX, body.x + body.radius);
        minY = Math.min(minY, body.y - body.radius);
        maxY = Math.max(maxY, body.y + body.radius);
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

    // Body list click handler (event delegation)
    document.getElementById('selected-body-info').addEventListener('click', (e) => {
        const item = e.target.closest('.body-list-item');
        if (item) {
            const bodyName = item.dataset.bodyName;
            const body = bodies.find(b => b.name === bodyName);
            if (body) {
                selectedBody = body;
                isTrackingSelectedBody = true;
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
