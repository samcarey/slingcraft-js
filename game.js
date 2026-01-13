// SlingCraft - JavaScript Version
// A space simulation with N-body gravitational physics

const canvas = document.getElementById('game-canvas');
const ctx = canvas.getContext('2d');

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
    }

    get kineticEnergy() {
        const speed = Math.sqrt(this.vx * this.vx + this.vy * this.vy);
        return 0.5 * this.mass * speed * speed;
    }

    get speed() {
        return Math.sqrt(this.vx * this.vx + this.vy * this.vy);
    }
}

// Initialize bodies
function initBodies() {
    bodies = [];

    // Central large body (like a star/planet)
    const central = new CelestialBody(0, 0, 80, '#ffaa44', 'Sol');
    central.mass = 1000; // Override mass for central body
    bodies.push(central);

    // Orbiting body 1
    const body1 = new CelestialBody(200, 0, 25, '#4488ff', 'Terra');
    body1.mass = 50;
    // Calculate orbital velocity
    const dist1 = 200;
    const orbitalSpeed1 = Math.sqrt(G * central.mass / dist1);
    body1.vy = orbitalSpeed1;
    bodies.push(body1);

    // Orbiting body 2
    const body2 = new CelestialBody(-350, 0, 35, '#88ff88', 'Gaia');
    body2.mass = 80;
    const dist2 = 350;
    const orbitalSpeed2 = Math.sqrt(G * central.mass / dist2);
    body2.vy = -orbitalSpeed2;
    bodies.push(body2);

    // Small moon orbiting body 1
    const moon = new CelestialBody(200, -50, 10, '#aaaaaa', 'Luna');
    moon.mass = 5;
    const moonDist = 50;
    const moonOrbitalSpeed = Math.sqrt(G * body1.mass / moonDist);
    moon.vx = -moonOrbitalSpeed;
    moon.vy = orbitalSpeed1; // Also inherit parent's orbital velocity
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
    return {
        x: (x - camera.x) * camera.zoom + canvas.width / 2,
        y: (y - camera.y) * camera.zoom + canvas.height / 2
    };
}

// Convert screen coordinates to world coordinates
function screenToWorld(screenX, screenY) {
    return {
        x: (screenX - canvas.width / 2) / camera.zoom + camera.x,
        y: (screenY - canvas.height / 2) / camera.zoom + camera.y
    };
}

// Render the scene
function render() {
    // Clear canvas
    ctx.fillStyle = '#0a0a0f';
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    // Draw stars background
    drawStars();

    // Draw center of mass
    const com = calculateCenterOfMass();
    const comScreen = worldToScreen(com.x, com.y);
    ctx.fillStyle = 'rgba(255, 255, 255, 0.5)';
    ctx.beginPath();
    ctx.arc(comScreen.x, comScreen.y, 3, 0, Math.PI * 2);
    ctx.fill();

    // Draw bodies
    for (const body of bodies) {
        drawBody(body);
    }

    // Update info panel
    updateInfoPanel();
}

// Draw starfield background
let stars = [];
function initStars() {
    stars = [];
    for (let i = 0; i < 200; i++) {
        stars.push({
            x: Math.random() * 2000 - 1000,
            y: Math.random() * 2000 - 1000,
            brightness: Math.random() * 0.5 + 0.2,
            size: Math.random() * 1.5 + 0.5
        });
    }
}

function drawStars() {
    for (const star of stars) {
        const screen = worldToScreen(star.x, star.y);
        ctx.fillStyle = `rgba(255, 255, 255, ${star.brightness})`;
        ctx.beginPath();
        ctx.arc(screen.x, screen.y, star.size, 0, Math.PI * 2);
        ctx.fill();
    }
}

// Draw a celestial body
function drawBody(body) {
    const screen = worldToScreen(body.x, body.y);
    const screenRadius = body.radius * camera.zoom;

    // Draw glow effect
    const gradient = ctx.createRadialGradient(
        screen.x, screen.y, screenRadius * 0.5,
        screen.x, screen.y, screenRadius * 2
    );
    gradient.addColorStop(0, body.color + '40');
    gradient.addColorStop(1, 'transparent');
    ctx.fillStyle = gradient;
    ctx.beginPath();
    ctx.arc(screen.x, screen.y, screenRadius * 2, 0, Math.PI * 2);
    ctx.fill();

    // Draw body
    ctx.fillStyle = body.color;
    ctx.beginPath();
    ctx.arc(screen.x, screen.y, screenRadius, 0, Math.PI * 2);
    ctx.fill();

    // Draw highlight for hovered body
    if (body === hoveredBody) {
        ctx.strokeStyle = 'rgba(255, 255, 255, 0.5)';
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.arc(screen.x, screen.y, screenRadius + 5, 0, Math.PI * 2);
        ctx.stroke();
    }

    // Draw selection ring for selected body
    if (body === selectedBody) {
        ctx.strokeStyle = '#ffffff';
        ctx.lineWidth = 2;
        ctx.setLineDash([5, 5]);
        ctx.beginPath();
        ctx.arc(screen.x, screen.y, screenRadius + 10, 0, Math.PI * 2);
        ctx.stroke();
        ctx.setLineDash([]);
    }

    // Draw name label
    ctx.fillStyle = '#ffffff';
    ctx.font = '12px sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText(body.name, screen.x, screen.y + screenRadius + 20);
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
    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    hoveredBody = findBodyAtPosition(x, y);
    canvas.style.cursor = hoveredBody ? 'pointer' : 'default';
}

function handleClick(e) {
    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    const clicked = findBodyAtPosition(x, y);
    selectedBody = clicked;
}

function handleResize() {
    canvas.width = canvas.parentElement.clientWidth - 280; // Account for info panel
    canvas.height = window.innerHeight;
}

// Main game loop
function gameLoop(timestamp) {
    const dt = (timestamp - lastTime) / 1000;
    lastTime = timestamp;

    updatePhysics(dt);
    render();

    requestAnimationFrame(gameLoop);
}

// Initialize
function init() {
    handleResize();
    window.addEventListener('resize', handleResize);

    canvas.addEventListener('mousemove', handleMouseMove);
    canvas.addEventListener('click', handleClick);

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

    initStars();
    initBodies();

    lastTime = performance.now();
    requestAnimationFrame(gameLoop);
}

// Start the game
init();
