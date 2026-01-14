// SlingCraft - JavaScript Version (SVG Rendering)
// A space simulation with N-body gravitational physics

const svg = document.getElementById('game-svg');
const starsLayer = document.getElementById('stars-layer');
const bodiesLayer = document.getElementById('bodies-layer');
const uiLayer = document.getElementById('ui-layer');
const defs = svg.querySelector('defs');

// Constants
const G = 50.0; // Gravitational constant
const MIN_DISTANCE = 10; // Minimum distance to prevent singularities
const DENSITY = 0.001; // Default density for mass calculation

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
        this.circleElement.dataset.bodyName = this.name;
        this.group.appendChild(this.circleElement);

        // Create label
        this.labelElement = document.createElementNS(SVG_NS, 'text');
        this.labelElement.setAttribute('class', 'body-label');
        this.labelElement.textContent = this.name;
        this.group.appendChild(this.labelElement);

        bodiesLayer.appendChild(this.group);
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
        // Remove gradient from defs
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

// Update physics
function updatePhysics(dt) {
    if (isPaused) return;

    // Cap dt to prevent instability
    dt = Math.min(dt, 0.033);

    // Calculate accelerations for all bodies first
    const accelerations = bodies.map(body => calculateGravity(body, bodies));

    // Update velocities and positions
    for (let i = 0; i < bodies.length; i++) {
        const body = bodies[i];
        const { ax, ay } = accelerations[i];

        // Update velocity
        body.vx += ax * dt;
        body.vy += ay * dt;

        // Update position
        body.x += body.vx * dt;
        body.y += body.vy * dt;
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

// Stars - using tiled SVG pattern for performance
let starPattern = null;
let starBackground = null;

function initStars() {
    // Clear existing
    starsLayer.innerHTML = '';

    // Create a pattern with random stars
    const patternSize = 200;
    const starsPerTile = 30;

    starPattern = document.createElementNS(SVG_NS, 'pattern');
    starPattern.setAttribute('id', 'star-pattern');
    starPattern.setAttribute('patternUnits', 'userSpaceOnUse');
    starPattern.setAttribute('width', patternSize);
    starPattern.setAttribute('height', patternSize);

    // Use seeded random for consistent pattern
    const seed = 12345;
    let rng = seed;
    const random = () => {
        rng = (rng * 1103515245 + 12345) & 0x7fffffff;
        return rng / 0x7fffffff;
    };

    // Add stars to the pattern
    for (let i = 0; i < starsPerTile; i++) {
        const star = document.createElementNS(SVG_NS, 'circle');
        star.setAttribute('cx', random() * patternSize);
        star.setAttribute('cy', random() * patternSize);
        star.setAttribute('r', random() * 1.5 + 0.5);
        star.setAttribute('fill', 'white');
        star.setAttribute('fill-opacity', random() * 0.5 + 0.2);
        starPattern.appendChild(star);
    }

    defs.appendChild(starPattern);

    // Create background rectangle that uses the pattern
    starBackground = document.createElementNS(SVG_NS, 'rect');
    starBackground.setAttribute('fill', 'url(#star-pattern)');
    starsLayer.appendChild(starBackground);
}

function updateStars() {
    if (!starBackground) return;

    const width = svg.clientWidth;
    const height = svg.clientHeight;

    // Make the background large enough to cover the viewport with some margin for panning
    const margin = 400;
    starBackground.setAttribute('x', -margin);
    starBackground.setAttribute('y', -margin);
    starBackground.setAttribute('width', width + margin * 2);
    starBackground.setAttribute('height', height + margin * 2);

    // Offset the pattern based on camera position (parallax - stars move slower)
    const parallaxFactor = 0.1; // Stars move at 10% of camera speed
    const offsetX = -camera.x * camera.zoom * parallaxFactor;
    const offsetY = -camera.y * camera.zoom * parallaxFactor;
    starPattern.setAttribute('patternTransform', `translate(${offsetX}, ${offsetY})`);
}

// Render the scene
function render() {
    // Update stars
    updateStars();

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
    document.getElementById('zoom-level').textContent = Math.round(camera.zoom * 100) + '%';

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
    } else {
        infoDiv.innerHTML = '<p style="color: #666; font-style: italic;">Click a body to select it</p>';
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
        }
    } else {
        // Click on a body to select
        const clicked = findBodyAtPosition(x, y);
        selectedBody = clicked;
    }

    isDragging = false;
    svg.style.cursor = hoveredBody ? 'pointer' : 'grab';
}

function handleWheel(e) {
    e.preventDefault();

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

// Update camera to track selected body
function updateCameraTracking() {
    if (selectedBody && !isDragging) {
        camera.x = selectedBody.x;
        camera.y = selectedBody.y;
    }
}

// Main game loop
function gameLoop(timestamp) {
    const dt = (timestamp - lastTime) / 1000;
    lastTime = timestamp;

    updatePhysics(dt);
    updateCameraTracking();
    render();

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
        document.getElementById('pause-btn').textContent = isPaused ? 'Resume' : 'Pause';
        document.getElementById('pause-btn').classList.toggle('active', isPaused);
    });

    // Reset button
    document.getElementById('reset-btn').addEventListener('click', () => {
        initBodies();
        selectedBody = null;
        hoveredBody = null;
        camera = { x: 0, y: 0, zoom: 1 };
    });

    // Center button - center on selected body or center of mass
    document.getElementById('center-btn').addEventListener('click', () => {
        if (selectedBody) {
            camera.x = selectedBody.x;
            camera.y = selectedBody.y;
        } else {
            const com = calculateCenterOfMass();
            camera.x = com.x;
            camera.y = com.y;
        }
    });

    initStars();
    createComMarker();
    initBodies();

    lastTime = performance.now();
    requestAnimationFrame(gameLoop);
}

// Start the game
init();
