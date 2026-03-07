# Plan: Chained Transfers & Multiple Crafts

## Overview

Replace the single-transfer global state with a per-craft queue of planned
transfers. Support multiple crafts. Transfers remain speculative/undoable until
real time advances past their launch frame.

---

## Phase 1: Per-Craft Planned Transfer Queue

### 1.1 Data structure

Add `plannedTransfers` array to the Craft class (constructor, ~line 272):

```javascript
this.plannedTransfers = [];
// Each entry:
// {
//   sourceBody,
//   destinationBody,
//   trajectory,          // [{x, y, vx, vy, isAccelerating}, ...]
//   launchFrame,         // buffer-relative frame index for launch
//   insertionFrame,      // index within trajectory of orbit insertion
//   orbitalAngle,        // computed angle at insertion
//   orbitalDirection,    // +1 or -1
//   correctionParams,    // {angle, duration, startFrame} or null
//   sampleOffset,        // for rendering alignment
// }
```

### 1.2 Rewrite `syncToViewFrame` (~line 896)

Replace the three hard-coded cases with a queue walk:

```
for each craft:
  body = craft.parentBody
  baseAngle = craft.orbitalAngle
  baseFrame = 0   // frame from which orbiting angle is computed

  for each transfer in craft.plannedTransfers:
    if frameIndex < transfer.launchFrame:
      → render orbiting `body` (advance baseAngle by frameIndex - baseFrame)
      done

    trajFrame = frameIndex - transfer.launchFrame
    if trajFrame < transfer.trajectory.length:
      → render at transfer.trajectory[trajFrame]
      done

    // Past arrival — now orbiting destination
    body = transfer.destinationBody
    baseAngle = transfer.orbitalAngle
    baseFrame = transfer.launchFrame + transfer.trajectory.length

  // Past all planned transfers — orbiting last body
  → render orbiting `body` (advance baseAngle by frameIndex - baseFrame)
```

Also set `craft.isCorrecting` based on whichever transfer is active at the
viewed frame and its `correctionParams`.

### 1.3 Change "Schedule" to push onto queue

When the user clicks Schedule (currently sets `transferState = 'scheduled'`):
- Compute `orbitalAngle` and `orbitalDirection` at insertion (same math as
  current `syncToViewFrame` past-arrival case, ~lines 928-945).
- Push a new entry onto `transferCraft.plannedTransfers`.
- Call `resetTransferState()` to free the search UI for the next transfer.
- Do NOT change `craft.state` or `craft.parentBody` — those only change when
  time actually advances past launch.

### 1.4 Update `advanceTimeline` (~line 714)

For each craft with `plannedTransfers.length > 0`:
- Decrement `plannedTransfers[i].launchFrame` for all entries (same as buffer
  shift).
- When `plannedTransfers[0].launchFrame <= 0`:
  - Call `craft.launchWithTrajectory(...)` using that entry's data.
  - Remove entry 0 from the array (shift).
  - This is the irreversible commit — the craft is now physically in flight.

When `craft.trajectoryBuffer` empties and `craft.destinationBody` is set
(existing orbit insertion logic, ~line 752):
- Perform the existing state transition to `'orbiting'`.
- If `plannedTransfers[0]` exists and its `launchFrame` is coming up, the
  cycle continues naturally.

### 1.5 Frame index maintenance

In `updateAcceptableTrajectoriesOnShift()` (~line 2446), add:

```javascript
for (const craft of crafts) {
  for (const t of craft.plannedTransfers) {
    t.launchFrame--;
  }
}
```

### 1.6 Scrub-back undo

When the user scrubs backward and initiates a new transfer that conflicts with
an existing planned transfer:
- Determine which `plannedTransfers` entry the viewed frame falls before.
- Truncate `plannedTransfers` from that index onward (remove that transfer and
  all later ones).
- The craft visually reverts to orbiting whichever body it was at before the
  removed transfer.

Trigger: when user clicks Transfer button while viewing a frame that's before
an existing planned transfer's launch, or on a body that doesn't match the
chain's expected position at that time.

### 1.7 Delete `commitScheduledArrival()`

No longer needed. The transfer button handler just needs to determine the
craft's virtual body at the viewed frame by walking the queue, then start a
search from there.

### 1.8 Transfer button handler (~line 4240)

Rewrite to:
1. Determine which craft is "virtually" at `selectedBody` at the viewed frame
   by walking each craft's `plannedTransfers`.
2. If found, truncate any planned transfers after the viewed frame.
3. Set `transferState = 'selecting_destination'` with that craft.

### 1.9 Trajectory rendering

Update `drawCraftTrajectory()` to render ALL planned transfer trajectories for
each craft, not just the single `transferBestTrajectory`. Each segment should
be drawn as a separate path. The currently-active-search trajectory (if any)
renders on top as it does now.

### 1.10 Craft info panel (~line 3118)

When a craft is selected, show:
- Current actual state (orbiting/free).
- List of planned transfers with launch times.
- Which segment is being viewed (based on scrub position).

### 1.11 Remove single-transfer globals

After migration, remove these globals (they become per-queue-entry or
search-only):
- `transferScheduledFrame` → `plannedTransfers[i].launchFrame`
- `transferBestTrajectory` → only used during search, pushed to queue on schedule
- `transferInsertionFrame` → `plannedTransfers[i].insertionFrame`
- `transferBestArrivalFrame` → computed from launchFrame + trajectory.length

Keep these as search-UI-only (not per-entry):
- `transferState` (but remove `'scheduled'` value — it becomes queue entries)
- `transferSourceBody`, `transferDestinationBody`, `transferCraft`
- `transferBestScore`, `transferBestFrame`, `transferSearchFrame`
- `acceptableTrajectories`, `selectedTrajectoryIndex`
- `correctionAngle`, `correctionDuration`, `correctionStartFrame`

---

## Phase 2: Multiple Crafts

### 2.1 Craft creation

Add a "Build Craft" button to the body info panel (near the Transfer button,
~line 3290). Clicking it:
- Creates `new Craft(selectedBody)`.
- Calls `craft.createElements()`.
- Pushes onto `crafts[]`.
- Each body can have multiple crafts orbiting it.

### 2.2 Craft naming / identification

Add `craft.name` or `craft.id` property. Auto-assign sequential names
(e.g. "Craft 1", "Craft 2") or let user rename.

### 2.3 Craft selection

Currently `findCraftAtPosition()` (~line 3454) only finds free-flying crafts.
Extend to also find orbiting crafts:
- Render orbiting crafts as distinct clickable dots at their orbital positions.
- Clicking selects that craft (`selectedCraft = craft`).
- Ensure visual distinction when multiple crafts orbit the same body (spread
  them or show a count badge).

### 2.4 Per-craft trajectory rendering

Each craft already has its own `trajectoryPath` and `trajectoryBuffer` SVG
elements. Extend so that each craft's `plannedTransfers` trajectories are also
rendered with per-craft coloring or styling to distinguish them.

### 2.5 Transfer button scoping

The Transfer button should work for whichever craft is selected (or the first
orbiting craft at the selected body if none is explicitly selected). When
multiple crafts orbit a body, the user should select which one to transfer.

### 2.6 Body info panel: craft list

Show a list of crafts at the selected body in the info panel:
- Each craft as a clickable item.
- Indicate state: orbiting, in transit, planned transfers pending.
- Clicking selects that craft for transfer or inspection.

### 2.7 Craft deletion

Add ability to delete/decommission a craft:
- Remove from `crafts[]`.
- Call `craft.removeElements()` (already exists, ~line 424).
- Clear any planned transfers.
- If it was `selectedCraft` or `transferCraft`, clear those references.

---

## Implementation Order & Status

1. ~~**Phase 1.1-1.2**: Data structure + syncToViewFrame rewrite (core change)~~ **DONE**
2. ~~**Phase 1.3-1.4**: Schedule → queue push + advanceTimeline commit~~ **DONE**
3. ~~**Phase 1.5-1.6**: Frame maintenance + undo~~ **DONE**
4. ~~**Phase 1.7-1.8**: Transfer button handler rewrite~~ **DONE**
5. ~~**Phase 1.9-1.10**: Trajectory rendering + info panel updates~~ **DONE**
6. ~~**Phase 1.11**: Clean up old globals~~ **DONE**
7. **Phase 2.1-2.2**: Craft creation + naming — NOT STARTED
8. **Phase 2.3-2.4**: Selection + per-craft rendering — NOT STARTED
9. **Phase 2.5-2.7**: Transfer scoping, craft list, deletion — NOT STARTED

Phase 1 is complete. Phase 2 (multiple crafts) has not been started.

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
