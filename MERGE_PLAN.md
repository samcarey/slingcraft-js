# Merge Plan: Thomas's UI Overhaul into Sam's Functional Codebase

## Goal

Bring all of Thomas Spooner's UI/visual enhancements from branch `origin/claude/add-ui-control-buttons-CRIrH` (commit `2e5b6b1`) into Sam Carey's functional codebase on branch `claude/merge-ui-functional-changes-NSSwf` (commit `d305b62`), while preserving every functional/game-logic feature Sam has added.

**The result should be:** Thomas's polished, glassmorphic UI driving Sam's squadron-based, time-scrubbing, scheduled-transfer game engine.

---

## Branch Context

- **Sam's branch (HEAD, `d305b62`)** — 50 commits of functional changes on top of `origin/main`:
  - Squadron system (`class Squadron`) replacing individual craft — groups of craft move together
  - `scheduledTransfers[]` array — transfers are scheduled with a countdown, not instant
  - `advanceTimeline(dt)` / `syncToViewFrame()` — decoupled physics from rendering; bodies and craft positions are computed from the prediction buffer at the viewed frame
  - Time scrubbing with scroll-wheel input, momentum physics, virtual arrival dot aggregation
  - `transferCount` / transfer quantity slider — user picks how many craft to send
  - `timeViewOffset` — looking into the future via the prediction buffer
  - Debug overlay (`renderDebugOverlay()`) and log buffer system
  - `searchTrajectoryPath` / `searchCorrectionOverlay` — dedicated SVG elements for the search trajectory
  - Prediction constants differ: `PREDICTION_TIME=1800`, `PREDICTION_DT=0.1` (minutes), `MAX_TRAJECTORY_POINTS=400`

- **Thomas's branch (`2e5b6b1`)** — UI overhaul built on the older codebase:
  - Glassmorphic accordion menu (origin → craft → destination → launch flow)
  - Tailwind CSS CDN integration
  - Controls popover (three-dot menu containing Reset/Fit All)
  - Speed multiplier buttons (1x–16x) + Pause/Play toggle
  - `spaceship.svg` craft icon asset
  - Planet lore system (`planetLore{}`, `destinationLore{}`)
  - Removed: time scrub UI, transfer slider, squadron count labels, log viewer
  - Uses the older craft system (`crafts[]` array of individual `Craft` objects, not squadrons)
  - Prediction constants differ: `PREDICTION_TIME=360`, `PREDICTION_DT=0.033` (seconds)

**Key conflict:** Thomas's branch uses the old `crafts[]` / `Craft` object model. Sam's branch replaced this with `squadrons[]` / `Squadron` class. Thomas's accordion functions reference `crafts[]`, `craft.state`, `craft.parentBody` — these must be rewritten to use `squadrons[]`, `Squadron`, `findBodySquadron()`, etc.

---

## Files to Modify

| File | Action | Description |
|------|--------|-------------|
| `index.html` | Edit | Add Tailwind CDN, glassmorphism CSS, accordion HTML, popover controls HTML (no speed/pause buttons) |
| `game.js` | Edit | Add accordion state + functions, popover logic, adapt to squadron system (no speed/pause logic) |
| `spaceship.svg` | Create (copy) | New asset from Thomas's branch |

---

## Phase 1: Add CSS and Assets to `index.html`

### Step 1.1: Add Tailwind CSS CDN

Insert before the `<style>` tag in `<head>`:

```html
<script src="https://cdn.tailwindcss.com"></script>
<script>
    tailwind.config = {
        corePlugins: { preflight: false },
        darkMode: 'media',
    }
</script>
```

**Caveat:** Tailwind CDN adds ~300KB. This is acceptable for a game demo but consider self-hosting or removing if bundle size matters later.

### Step 1.2: Add Glassmorphism CSS Variables

Add to the `:root` block (dark mode), after the existing `--trajectory-mix: white;` line:

```css
/* Glassmorphic accordion */
--glass-bg: rgba(15, 15, 25, 0.65);
--glass-border: rgba(255, 255, 255, 0.12);
--glass-shadow: rgba(0, 0, 0, 0.4);
--glass-highlight: rgba(255, 255, 255, 0.04);
--accordion-line-rose: #fb7185;
--accordion-line-amber: #fbbf24;
--accordion-line-emerald: #34d399;
```

Add to the `@media (prefers-color-scheme: light)` `:root` block, after `--trajectory-mix: black;`:

```css
/* Glassmorphic accordion light */
--glass-bg: rgba(255, 255, 255, 0.55);
--glass-border: rgba(0, 0, 0, 0.10);
--glass-shadow: rgba(0, 0, 0, 0.08);
--glass-highlight: rgba(255, 255, 255, 0.5);
--accordion-line-rose: #e11d48;
--accordion-line-amber: #d97706;
--accordion-line-emerald: #059669;
```

### Step 1.3: Add All Accordion CSS

Copy the entire accordion CSS block from Thomas's `index.html` lines 269–647 (from `/* ===== Glassmorphic Accordion Menu ===== */` through the mobile `@media (max-width: 768px)` block). Insert it in Sam's `index.html` just before the `/* Controls - upper right corner */` comment.

This includes styles for:
- `#accordion-menu` (glassmorphic container with backdrop-filter)
- `.accordion-section` (expand/collapse animation)
- `.accordion-section-header`
- `.accordion-planet-item`, `.accordion-planet-dot`, `.accordion-planet-name`
- `.accordion-craft-badge`
- `.accordion-planet-info-inline`, `.planet-info-stats`, `.planet-info-lore`
- `.accordion-craft-item`, `.accordion-craft-icon`, `.accordion-no-craft`, `.no-craft-badge`
- `.accordion-dest-item`, `.accordion-dest-lore-inline`
- `.accordion-launch-wrap`, `#accordion-launch-btn`
- `.accordion-propagation`, `.propagation-bar`, `.propagation-fill`
- Mobile responsive overrides (`@media (max-width: 768px)`)

### Step 1.4: Add Controls Popover CSS

Copy the popover CSS from Thomas's `index.html` lines 684–764 (from `/* Controls popover */` through `#speed-btn.fast`). Insert after the existing `button.active` block.

This includes:
- `#controls-popover`
- `.popover-content`, `.popover-item`
- `#fit-all-badge`, `#fit-all-item.active`
- `#pause-btn.active`, `#speed-btn`, `#speed-btn.fast`

### Step 1.5: Copy `spaceship.svg`

Copy `spaceship.svg` from Thomas's branch:
```bash
git show origin/claude/add-ui-control-buttons-CRIrH:spaceship.svg > spaceship.svg
```

---

## Phase 2: Add HTML Structure to `index.html`

### Step 2.1: Add Accordion Menu HTML

Insert the accordion menu HTML after the `#body-details-dropdown` div and before the `#selected-body-info` div. Copy from Thomas's `index.html` lines 1196–1222:

```html
<!-- Glassmorphic Accordion Menu -->
<div id="accordion-menu">
    <div id="accordion-origin" class="accordion-section open">
        <div class="accordion-section-header">Select Origin</div>
        <div id="accordion-origin-list"></div>
    </div>
    <div id="accordion-craft" class="accordion-section">
        <div class="accordion-section-header">Select Craft</div>
        <div id="accordion-craft-list"></div>
    </div>
    <div id="accordion-dest" class="accordion-section">
        <div class="accordion-section-header">Select Dest</div>
        <div id="accordion-dest-list"></div>
    </div>
    <div id="accordion-launch-section" class="accordion-section">
        <div class="accordion-section-header">Ready</div>
        <div class="accordion-launch-wrap">
            <button id="accordion-launch-btn">Launch Transfer</button>
        </div>
    </div>
</div>
```

**KEEP** Sam's existing `#selected-body-info` div — it's still used for in-transit craft display and the body list panel. The accordion will hide it when active (controlled by `updateAccordionMenu()`).

### Step 2.2: Replace Upper-Right Controls with Thomas's Popover Structure

Replace the current `#controls` div:
```html
<!-- OLD (Sam's) -->
<div id="controls">
    <button id="reset-btn" title="Reset">↺</button>
    <button id="fit-all-btn" title="Fit All">⤢</button>
</div>
```

With Thomas's version (excluding speed/pause buttons — intentionally removed by Sam):
```html
<div id="controls">
    <div id="controls-popover">
        <button id="popover-trigger" type="button" title="More controls">
            <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" style="width: 20px; height: 20px;">
                <path fill-rule="evenodd" d="M5.22 8.22a.75.75 0 0 1 1.06 0L10 11.94l3.72-3.72a.75.75 0 1 1 1.06 1.06l-4.25 4.25a.75.75 0 0 1-1.06 0L5.22 9.28a.75.75 0 0 1 0-1.06Z" clip-rule="evenodd" />
            </svg>
        </button>
        <div id="popover-panel" class="absolute right-0 z-10 mt-2 hidden w-72 opacity-0 translate-y-1 transition-all duration-200 ease-out">
            <div class="popover-content p-3 text-sm">
                <div id="reset-item" role="button" tabindex="0" class="popover-item cursor-pointer p-3">
                    <div class="item-name">Reset</div>
                    <p class="item-desc">Refresh and re-render the simulation from its initial state</p>
                </div>
                <div id="fit-all-item" role="button" tabindex="0" class="popover-item cursor-pointer p-3">
                    <div class="flex items-center gap-2">
                        <span class="item-name">Fit All</span>
                        <span id="fit-all-badge" class="hidden">Active</span>
                    </div>
                    <p class="item-desc">Auto-center and zoom to show all planetary bodies</p>
                </div>
            </div>
        </div>
    </div>
</div>
```

**KEEP** Sam's time scrub container (`#time-scrub-container`, `#time-scrub-panel`) — Thomas removed these but Sam's version has significant functional improvements.

### Step 2.3: Keep Sam's Transfer Controls

**DO NOT** remove or restructure:
- `#trajectory-plot-container` (with canvas, info bar)
- `#transfer-controls-panel` (with trajectory controls, slider, schedule button)
- `#transfer-launch-controls` (with quantity slider)
- `#time-scrub-container` and `#time-scrub-panel`
- `#commit-modal` with tabs (Build Info + Logs)

These contain functional features that Thomas's branch lacks.

### Step 2.4: Add Accordion Event Delegation Script

After the `<script src="game.js?v=3"></script>` tag, add the inline script from Thomas's `index.html` lines 1277–1317. **Adapt it for squadrons:**

```html
<script>
(function initAccordionEvents() {
    const menu = document.getElementById('accordion-menu');
    if (!menu) return;

    menu.addEventListener('click', (e) => {
        // Origin planet click
        const originItem = e.target.closest('#accordion-origin-list .accordion-planet-item');
        if (originItem) {
            const bodyName = originItem.dataset.bodyName;
            const body = bodies.find(b => b.name === bodyName);
            if (body) handleAccordionOriginSelect(body);
            return;
        }

        // Craft (squadron) item click
        const craftItem = e.target.closest('#accordion-craft-list .accordion-craft-item');
        if (craftItem) {
            const idx = parseInt(craftItem.dataset.squadronIndex);
            const sq = squadrons[idx];
            if (sq) handleAccordionCraftSelect(sq);
            return;
        }

        // Destination planet click
        const destItem = e.target.closest('#accordion-dest-list .accordion-dest-item');
        if (destItem) {
            const bodyName = destItem.dataset.bodyName;
            const body = bodies.find(b => b.name === bodyName);
            if (body) handleAccordionDestSelect(body);
            return;
        }

        // Launch button
        if (e.target.id === 'accordion-launch-btn') {
            handleAccordionLaunch();
            return;
        }
    });
})();
</script>
```

**Key change from Thomas:** `craftItem.dataset.craftIndex` → `craftItem.dataset.squadronIndex`, and `crafts[idx]` → `squadrons[idx]`.

---

## Phase 3: Add Accordion + Controls Logic to `game.js`

### Step 3.1: Add Planet Lore Data

Copy `planetLore` and `destinationLore` objects from Thomas's `game.js` lines 48–87. Add them near the top of Sam's `game.js`, after the game state variables.

**Caveat:** Sam's `game.js` doesn't have these objects. They're purely cosmetic data used by the accordion to show planet descriptions.

### Step 3.2: Add Accordion State Variables

Add near the existing state variables (after `let isPaused = false;`):

```javascript
// Accordion menu state
let accordionOrigin = null;       // Selected origin body
let accordionCraft = null;        // Selected squadron (was "craft" in Thomas's version)
let accordionDestination = null;  // Selected destination body
let accordionBuilt = false;

// Dirty tracking for accordion
let _accordionLastOrigin = undefined;
let _accordionLastCraft = undefined;
let _accordionLastDest = undefined;
let _accordionLastCraftCounts = '';
let _accordionLastBufferReady = false;
let _accordionLastPropProgress = -1;
let _accordionDirty = true;
```

### Step 3.3: Port Accordion Helper Functions

Copy from Thomas's `game.js` and adapt for squadrons. The key adaptations:

#### `getOrbitingCountKey()` (Thomas's line ~2889)
Copy as-is but change `crafts` → `squadrons` and `craft.state` → `sq.state`:

```javascript
function getOrbitingCountKey() {
    const counts = [];
    for (const body of bodies) {
        const sq = findBodySquadron(body);
        const n = sq ? sq.count : 0;
        counts.push(n);
    }
    return counts.join(',');
}
```

**Difference from Thomas:** Thomas iterates `crafts` counting individual craft per body. Sam uses `findBodySquadron(body)` which returns the single orbiting squadron for a body (Sam's design: one squadron per body).

#### `markAccordionDirty()` (simple flag setter)
```javascript
function markAccordionDirty() { _accordionDirty = true; }
```

#### `buildAccordionOriginList()` (Thomas's line 2905)

Adapt to use squadrons instead of crafts:

```javascript
function buildAccordionOriginList() {
    const listEl = document.getElementById('accordion-origin-list');
    if (!listEl) return;

    const sortedBodies = accordionOrigin
        ? [accordionOrigin, ...bodies.filter(b => b !== accordionOrigin)]
        : [...bodies];

    let html = '';
    for (const body of sortedBodies) {
        // Use findBodySquadron for craft count (Sam's squadron system)
        const sq = findBodySquadron(body);
        const craftCount = sq ? sq.count : 0;
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

        if (isSelected) {
            const lore = planetLore[body.name] || { desc: 'Unknown world.', stats: '' };
            html += `<div class="accordion-planet-info-inline">
                <div class="planet-info-stats">
                    <span class="info-label">Mass</span><span class="info-value">${body.mass.toFixed(1)}</span>
                    <span class="info-label">Radius</span><span class="info-value">${body.radius.toFixed(1)}</span>
                    <span class="info-label">Craft</span><span class="info-value">${craftCount}</span>
                </div>
                <div class="planet-info-lore">${lore.desc}</div>
            </div>`;
        }
    }
    listEl.innerHTML = html;
}
```

#### `buildAccordionCraftList()` (Thomas's line 2953)

**Major rewrite needed.** Thomas iterates individual `crafts[]` filtered by `parentBody`. Sam has one `Squadron` per body. The accordion needs to show the squadron (with its count) rather than individual craft:

```javascript
function buildAccordionCraftList() {
    const listEl = document.getElementById('accordion-craft-list');
    if (!listEl || !accordionOrigin) return;

    const sq = findBodySquadron(accordionOrigin);
    const bufferReady = predictionBuffer.length >= PREDICTION_FRAMES;

    if (!sq || sq.count === 0) {
        listEl.innerHTML = `<div class="accordion-no-craft">
            <span class="no-craft-badge">None</span>
            <span>No craft in orbit</span>
        </div>`;
        return;
    }

    // Show the single orbiting squadron
    const idx = squadrons.indexOf(sq);
    const isSelected = accordionCraft === sq;
    let html = `<div class="accordion-craft-item${isSelected ? ' selected-craft' : ''}" data-squadron-index="${idx}">
        <img src="spaceship.svg" class="accordion-craft-icon" alt="craft" />
        <span class="accordion-planet-name">Squadron (${sq.count} craft)</span>
    </div>`;

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
```

**Key difference:** Instead of listing N individual craft objects, we show one squadron entry with its count. The `data-squadron-index` attribute replaces `data-craft-index`.

#### `buildAccordionDestList()` (Thomas's line 2992)

Copy nearly as-is — it only references `bodies[]` and `accordionDestination`, no craft-specific logic. Just ensure `destinationLore` is available.

#### `isAccordionMobile()`, `openSection()`, `closeSection()`, `applyAccordionSections()`, `rebuildAccordion()`

Copy as-is from Thomas's `game.js` lines 3020–3153. These are purely UI layout functions with no craft/squadron dependencies.

#### `updateAccordionMenu()` (Thomas's line 3156)

Copy from Thomas's `game.js` and make these adaptations:

1. Change `selectedCraft` references to `selectedSquadron`
2. Change `isTrackingSelectedCraft` to `isTrackingSelectedSquadron`
3. Add handling for the `'scheduled'` transfer state (Thomas didn't have this):
   ```javascript
   if (transferState === 'searching' || transferState === 'ready' || transferState === 'scheduled') {
       menu.classList.add('hidden-menu');
       return;
   }
   ```
4. Add the call to `updateAccordionMenu()` in the `render()` function (at the end, after `updateInfoPanel()`).

### Step 3.4: Port Accordion Event Handlers

#### `handleAccordionOriginSelect(body)` (Thomas's line 3198)

Adapt to use `selectedSquadron` instead of `selectedCraft`:

```javascript
function handleAccordionOriginSelect(body) {
    if (accordionOrigin === body) {
        accordionOrigin = null;
        accordionCraft = null;
        accordionDestination = null;
        selectedBody = null;
        isTrackingSelectedBody = false;
    } else {
        accordionOrigin = body;
        accordionCraft = null;
        accordionDestination = null;
        selectedBody = body;
        selectedSquadron = null;
        isTrackingSelectedBody = true;
        isTrackingSelectedSquadron = false;
    }
    rebuildAccordion();
}
```

#### `handleAccordionCraftSelect(sq)` (Thomas's line 3220)

Change parameter from `craft` to `sq` (squadron):

```javascript
function handleAccordionCraftSelect(sq) {
    if (accordionCraft === sq) {
        accordionCraft = null;
        accordionDestination = null;
    } else {
        accordionCraft = sq;
        accordionDestination = null;
    }
    rebuildAccordion();
}
```

#### `handleAccordionDestSelect(body)` — Copy as-is from Thomas.

#### `handleAccordionLaunch()` (Thomas's line 3242)

**Major rewrite needed.** Thomas sets `transferCraft = accordionCraft` (a single craft). Sam's codebase doesn't have `transferCraft` — instead it uses `transferCount` and works with squadrons. Adapt:

```javascript
function handleAccordionLaunch() {
    if (!accordionOrigin || !accordionCraft || !accordionDestination) return;

    // Set up transfer state to match Sam's existing transfer flow
    transferSourceBody = accordionOrigin;
    transferDestinationBody = accordionDestination;
    transferCount = accordionCraft.count; // Send the whole squadron by default
    selectedBody = accordionOrigin;

    // Start transfer search (Sam's existing mechanism)
    startTransferSearch();

    // Reset accordion state
    accordionOrigin = null;
    accordionCraft = null;
    accordionDestination = null;
    markAccordionDirty();
}
```

**Caveat:** After the accordion triggers `startTransferSearch()`, the flow continues through Sam's existing trajectory plot + slider UI. The user picks the trajectory, adjusts quantity with the slider, and hits Schedule. This is intentional — the accordion replaces only the *selection* phase, not the *trajectory-picking/scheduling* phase.

### Step 3.5: ~~Port Speed Multiplier System~~ — SKIPPED (DO NOT IMPLEMENT)

**Status:** INTENTIONALLY EXCLUDED.

Sam removed the speed control and pause buttons on purpose before the merge. The time scrubber replaces this functionality. Do NOT re-add `isPaused`, `userSpeedMultiplier`, `resetSpeed()`, speed-btn, or pause-btn elements. The `SIM_SPEED` constant rename was kept since it clarifies the code.

### Step 3.6: Port Controls Popover Logic

Add the popover open/close functions and event listeners from Thomas's `game.js` lines 4083–4149. These are pure UI and can be copied nearly verbatim. The Reset handler needs adaptation:

```javascript
// Reset item in popover
document.getElementById('reset-item').addEventListener('click', () => {
    initBodies();
    resetPredictions();
    resetTransferState();
    selectedBody = null;
    selectedSquadron = null;     // was selectedCraft in Thomas's
    hoveredBody = null;
    isAutoFitPaused = false;
    isTrackingSelectedBody = true;
    isTrackingSelectedSquadron = false;  // was isTrackingSelectedCraft in Thomas's
    accordionOrigin = null;
    accordionCraft = null;
    accordionDestination = null;
    accordionBuilt = false;
    // Reset time scrub state (Sam's feature, Thomas doesn't have)
    timeViewOffset = 0;
    timeScrubPanelOpen = false;
    const scrubPanel = document.getElementById('time-scrub-panel');
    if (scrubPanel) scrubPanel.classList.remove('visible');
    // Reset squadrons
    for (const sq of squadrons) sq.removeElements();
    squadrons.length = 0;
    scheduledTransfers.length = 0;
    camera = { x: 0, y: 0, zoom: 1 };
    closeControlsPopover();
});
```

**Changes from Thomas:**
- `selectedCraft` → `selectedSquadron`
- `isTrackingSelectedCraft` → `isTrackingSelectedSquadron`
- Added squadron cleanup (`sq.removeElements()`, clear `squadrons[]`, clear `scheduledTransfers[]`)
- Added time scrub state reset

Fit All handler can be copied nearly as-is, just changing `isTrackingSelectedCraft` → `isTrackingSelectedSquadron`.

### Step 3.7: Wire `updateAccordionMenu()` into Render Loop

In Sam's `render()` function (around line 3446), add at the end:

```javascript
function render() {
    renderGrid();
    updateComMarker();
    for (const body of bodies) { body.updateElements(); }
    for (const sq of squadrons) { sq.updateElements(); }
    updateInfoPanel();
    updateAccordionMenu();  // <-- ADD THIS LINE
}
```

---

## Phase 4: Reconcile Layout Conflicts and Remove Duplicates

### Step 4.1: Remove Old Standalone Reset/Fit All Buttons

Remove the old `#reset-btn` and `#fit-all-btn` event listeners from `game.js` (they're now in the popover). Also remove the `#reset-btn` CSS padding rule:
```css
/* REMOVE: */
#reset-btn {
    padding-bottom: 4px;
}
```

Search for `document.getElementById('reset-btn')` and `document.getElementById('fit-all-btn')` in `game.js` and remove or redirect those event listeners.

### Step 4.2: Fix Layout Overlap

Both the accordion menu (`bottom: 20px; left: 20px`) and the transfer controls panel (`bottom: 20px; left: 20px`) occupy the same position. They never show simultaneously (the accordion hides during transfer states), so this is fine. But verify:

- `#accordion-menu` has `z-index: 10`
- `#transfer-controls-panel` should have `z-index: 10` or higher
- `#selected-body-info` (same position) is hidden by `updateAccordionMenu()` when the accordion is visible

### Step 4.3: Adjust Trajectory Plot Position

Sam's `#trajectory-plot-container` is at `top: 66px` (full width at top). Thomas moved it to `bottom: 10px`. **Keep Sam's position** (`top: 66px`) since it works well with the bottom-left accordion. If the accordion obscures it on mobile, add:

```css
@media (max-width: 768px) {
    #trajectory-plot-container {
        top: 56px;
        left: 5px;
        right: 5px;
    }
}
```

### Step 4.4: Hide Old Body Info When Accordion Is Active

The `updateAccordionMenu()` function (ported in Step 3.3) already handles this — it sets `#selected-body-info` `display: none` when the accordion is visible. Verify this works correctly with Sam's `updateInfoPanel()` which also manages that div.

**Potential conflict:** Both `updateInfoPanel()` and `updateAccordionMenu()` set `infoDiv.style.display`. The accordion should take priority when `transferState === 'none'`. Ensure `updateAccordionMenu()` runs AFTER `updateInfoPanel()` in `render()` so it gets the last word.

---

## Phase 5: Testing Checklist

After implementation, verify each of these:

1. **Accordion menu displays** — planets listed with correct colors and craft counts
2. **Accordion selection flow** — origin → craft → destination → launch button
3. **Craft counts match squadron counts** — `findBodySquadron()` returns correct counts
4. **Launch triggers transfer search** — clicking Launch Transfer opens the trajectory plot
5. **Transfer slider still works** — after selecting a trajectory, quantity slider adjusts `transferCount`
6. **Schedule button creates a scheduled transfer** — countdown, launch, transit, arrival all work
7. **Time scrubber still works** — lower-right clock button opens panel, wheel scrolls time
8. ~~**Speed multiplier works**~~ — SKIPPED (intentionally removed)
9. ~~**Pause/Play works**~~ — SKIPPED (intentionally removed)
10. **Popover works** — three-dot menu opens, Reset and Fit All function correctly
11. **Reset clears all state** — squadrons removed, accordion reset, time scrub reset
12. **Mobile responsive** — accordion stacks vertically on small screens
13. **Dark/light mode** — glassmorphism variables apply correctly in both themes
14. **No console errors** — no references to undefined `crafts[]`, `selectedCraft`, or `isTrackingSelectedCraft`
15. **Squadron arrival** — craft arrive at destination, squadron merges/converts correctly
16. **Scheduled transfer countdown** — scrubbing shows pre-launch position, in-transit dots, post-arrival dots
17. **Debug overlay** — still renders when enabled
18. **Log viewer** — still accessible from Build Info modal Logs tab
19. **CPU benchmark** — still reports in console

---

## Summary of Variable Renaming (Thomas → Sam)

These are the critical renames needed throughout the ported code:

| Thomas's code | Sam's code | Reason |
|---------------|------------|--------|
| `crafts` | `squadrons` | Sam renamed to squadron system |
| `selectedCraft` | `selectedSquadron` | Same |
| `isTrackingSelectedCraft` | `isTrackingSelectedSquadron` | Same |
| `craft.parentBody` | `sq.parentBody` | Same field, different variable name convention |
| `craft.state === 'orbiting'` | `sq.state === 'orbiting'` | Same |
| `crafts.indexOf(craft)` | `squadrons.indexOf(sq)` | Same |
| `data-craft-index` | `data-squadron-index` | HTML attribute |
| `transferCraft = craft` | *(removed — use transferCount instead)* | Sam removed per-craft transfer tracking |
| `speedMultiplier` (Thomas: user toggle) | `userSpeedMultiplier` | Sam's `speedMultiplier` is a constant, rename to `SIM_SPEED` |

---

## Risk Areas

1. ~~**`speedMultiplier` name collision**~~ — RESOLVED. Sam's `speedMultiplier` renamed to `SIM_SPEED`. Thomas's speed/pause system intentionally excluded (Sam removed those buttons before the merge; the time scrubber replaces them).

2. **Dual control paths for launching** — The accordion's "Launch Transfer" button and the existing body-info panel's "Transfer" button both initiate transfers. Decision: keep both paths working. The accordion is the primary UI; the old panel is a fallback when a free craft is selected.

3. **`updateInfoPanel()` vs `updateAccordionMenu()` display conflicts** — Both manage `#selected-body-info` visibility. Ensure `updateAccordionMenu()` runs last in `render()`.

4. **Missing `planetLore` / `destinationLore`** — Sam's `game.js` doesn't have these. They must be added before the accordion functions that reference them.

5. **`transferCraft` variable** — Thomas's code sets `transferCraft = accordionCraft` in `handleAccordionLaunch()`. Sam's code still has a `transferCraft` variable but it's not used the same way. Need to verify Sam's `startTransferSearch()` doesn't depend on `transferCraft` being set, or set it appropriately.

6. **Tailwind CSS classes on popover** — The popover panel uses Tailwind utility classes (`absolute`, `right-0`, `hidden`, `w-72`, `opacity-0`, etc.). These require the Tailwind CDN to be loaded. Make sure Step 1.1 is done first.
