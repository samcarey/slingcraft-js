# Plan: Quantity-Based Craft System

## Overview

Replace individual craft instances with a quantity-based system. Bodies hold a
count of craft. Transfers launch a **squadron** (N craft moving as one unit)
from a body to a destination. Squadrons display as a single dot with a count
label beside it.

---

## Phase 3: Quantity-Based Craft Rework

### 3.1 Add craft count to CelestialBody

Add `craftCount` property to CelestialBody:
```javascript
this.craftCount = 0;
```

In `initBodies()`, set `ember.craftCount = 1` (or whatever starting amount).

### 3.2 Rework Craft class → Squadron class

Rename `Craft` to `Squadron`. A squadron represents craft **in transit** (or
with planned transfers). Key changes:

- Add `count` property (how many craft in this squadron)
- Remove `id`, `name`, `color` individual-craft properties
- Keep `state`, `parentBody`, `orbitalAngle`, `orbitalDirection` (for
  launch/arrival transitions)
- Keep `trajectoryBuffer`, `plannedTransfers`, all flight state
- Keep `createElements()` but add a **count label** (SVG text beside the dot)
- `removeElements()` also removes the label

Constructor: `constructor(parentBody, count, orbitalAltitude)`

### 3.3 Count label rendering

Add an SVG `<text>` element next to the craft dot showing the squadron count.
Position it offset from the dot. Only show when count > 1. Update position in
`updateElements()`.

### 3.4 Rework body info panel

Replace the per-craft list with:
- Show craft count at body: "N craft orbiting"
- **Transfer button**: Shows when craftCount > 0. On click, prompt for how many
  to send (number input or slider, 1 to craftCount).
- **Build button**: Add N craft to body (simple increment)

### 3.5 Transfer flow with quantity

When user clicks Transfer on body panel:
1. Show a quantity picker (1 to body.craftCount + any orbiting squadron counts
   at that body at the viewed frame)
2. User selects count, then selects destination body
3. Transfer search runs as before (trajectory is same regardless of count)
4. On schedule: create a new Squadron with the selected count, deduct from the
   body's craftCount, push transfer to squadron's plannedTransfers

### 3.6 Squadron creation on transfer schedule

When user schedules a transfer:
- Deduct `transferCount` from source body's effective craft count (either
  `body.craftCount` or from a squadron that has arrived at that body via
  planned transfers)
- Create `new Squadron(sourceBody, transferCount)`
- Push the planned transfer entry onto the squadron
- The squadron exists only while it has planned transfers or is in free flight
- On arrival (orbit insertion in `advanceTimeline`), add `squadron.count` to
  `destinationBody.craftCount` and destroy the squadron

### 3.7 Update advanceTimeline

When a squadron arrives (trajectoryBuffer empties with destinationBody set):
- `destinationBody.craftCount += squadron.count`
- `squadron.removeElements()`
- Remove from `crafts[]` (now `squadrons[]`)

When a squadron's planned transfer launches:
- Same as before: `launchWithTrajectory()`

### 3.8 Update syncToViewFrame

For squadrons with planned transfers (orbiting state):
- Same queue walk as before for positioning
- Virtual state at viewed frame: if past arrival of last planned transfer,
  the squadron's craft are "at" the destination body — show as part of that
  body's count, not as a separate dot

### 3.9 Trajectory rendering

Same as current — each squadron has its own trajectory path. No need for
per-craft colors since squadrons are temporary transit objects. Use a single
color (white) or subtle variation.

### 3.10 No-selection panel (Bodies tab)

Show craft counts per body in the body list. The "Trajectories" tab shows
active squadrons with their counts and routes.

### 3.11 Clean up Phase 2 artifacts

Remove:
- `nextCraftId`, `CRAFT_COLORS`
- Individual craft name/color properties
- Per-craft transfer/delete buttons in body panel
- `craft-list`, `craft-list-item`, `craft-indicator` CSS

---

## Implementation Order & Status

1. ~~**Phase 1.1-1.2**: Data structure + syncToViewFrame rewrite~~ **DONE**
2. ~~**Phase 1.3-1.4**: Schedule → queue push + advanceTimeline commit~~ **DONE**
3. ~~**Phase 1.5-1.6**: Frame maintenance + undo~~ **DONE**
4. ~~**Phase 1.7-1.8**: Transfer button handler rewrite~~ **DONE**
5. ~~**Phase 1.9-1.10**: Trajectory rendering + info panel updates~~ **DONE**
6. ~~**Phase 1.11**: Clean up old globals~~ **DONE**
7. ~~**Phase 2 (all)**: Multiple crafts~~ **DONE** (superseded by Phase 3)
8. **Phase 3.1-3.3**: CelestialBody craftCount + Squadron class + count label — NOT STARTED
9. **Phase 3.4-3.5**: Body info panel rework + quantity picker — NOT STARTED
10. **Phase 3.6-3.7**: Squadron creation on schedule + advanceTimeline arrival — NOT STARTED
11. **Phase 3.8-3.11**: syncToViewFrame + rendering + cleanup — NOT STARTED

### Bug fixes applied after Phase 1 completion

- **Chained transfer search origin fix**: `dispatchNextBatch()` was using
  `transferCraft.parentBody` (the craft's actual/physical body) instead of
  `transferSourceBody` (the virtual body from the queue walk). This caused
  the second transfer search to compute trajectories originating from the
  wrong body. Fixed by:
  - Using `transferSourceBody` as the source body in `dispatchNextBatch()`
  - Deriving `baseOrbitalAngle` and `orbitalDirection` from the last entry
    in `plannedTransfers` instead of from `transferCraft` directly
  - Starting the search from after the last planned transfer's arrival frame
    (`lastTransfer.launchFrame + lastTransfer.trajectory.length`)
