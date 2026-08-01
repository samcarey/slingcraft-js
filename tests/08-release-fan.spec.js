const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

/**
 * The transfer picker: craft leave from any point on their orbit, so the search
 * sweeps release angles at the moment on the clock and fans the results across the
 * map, where the player drags a finger over them to choose.
 *
 * Everything here uses g.dragReal() rather than g.dragTouch(). The fan is drawn over
 * the whole map, including the parts the panels cover, and synthetic events aimed at
 * the SVG would "touch" points no finger can reach — which is exactly the bug that
 * shipped the first time this was built.
 */
test.describe('the fan of release angles', () => {
    test('craft at a body are a number beside it, with no orbiting dot', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();

        const shown = await page.evaluate(() => bodies
            .filter((b) => b.craftCount > 0)
            .map((b) => {
                const el = b.craftCountElement;
                const box = el.getBBox();
                const cs = getComputedStyle(el);
                const centre = bodyScreenPos(b);
                return {
                    name: b.name,
                    count: b.craftCount,
                    text: el.textContent,
                    visible: el.style.display !== 'none',
                    fontPx: parseFloat(cs.fontSize),
                    // A contrasting outline is what keeps the number readable over grid
                    // lines, trajectories and other bodies.
                    stroke: cs.stroke,
                    strokeWidth: parseFloat(cs.strokeWidth),
                    paintOrder: cs.paintOrder,
                    fill: cs.fill,
                    // Left edge of the number against the right edge of the disc.
                    gap: box.x - (centre.x + bodyScreenRadius(b)),
                    // Bottom of the digits IS the baseline: they have no descenders, so
                    // the y attribute is where the number ends. getBBox is no use for this
                    // — it reports the font's em box, which reserves descender room the
                    // digits never occupy, and would read several px low.
                    baselineVsCentre: parseFloat(el.getAttribute('y')) - centre.y,
                    topVsCentre: box.y - centre.y,
                    height: box.height,
                };
            }));

        expect(shown.length, 'the starting fleet should be showing somewhere').toBeGreaterThan(0);
        for (const s of shown) {
            expect(s.text, `${s.name} label`).toBe(String(s.count));
            expect(s.visible).toBe(true);
            // "Big font": clearly larger than the body's own name label at 12px.
            expect(s.fontPx, `${s.name} count should be large`).toBeGreaterThanOrEqual(18);
            // To the RIGHT of the body, a fixed short distance off the rim.
            expect(s.gap, `${s.name} count should clear the disc on the right`).toBeGreaterThan(0);
            expect(s.gap, `${s.name} count should hug the rim`).toBeLessThan(10);
            // Bottom of the number sits on the body's centre line, so it rises from it.
            expect(Math.abs(s.baselineVsCentre), `${s.name} count should be bottom-aligned to centre`)
                .toBeLessThan(0.5);
            // And therefore the whole number is above the centre, not straddling it.
            expect(s.topVsCentre, `${s.name} count should sit above the centre line`).toBeLessThan(-6);
            expect(s.height, `${s.name} count should have real height`).toBeGreaterThan(8);
            // Outlined, and the outline sits BEHIND the fill — without paint-order the
            // stroke is painted over the glyphs and eats half their weight.
            expect(s.strokeWidth, `${s.name} count should be outlined`).toBeGreaterThan(1);
            expect(s.paintOrder, `${s.name} outline must not cut into the glyphs`)
                .toContain('stroke');
            expect(s.stroke, `${s.name} outline should contrast with the text`).not.toBe(s.fill);
        }

        // Nothing on the map may cover the number: it lives in the topmost layer, past
        // the bodies, trajectories and squadrons.
        const layering = await page.evaluate(() => {
            const order = Array.from(document.getElementById('game-svg').children).map((c) => c.id);
            const el = bodies.find((b) => b.craftCount > 0).craftCountElement;
            const layerOf = (n) => { while (n && !n.id) n = n.parentNode; return n ? n.id : null; };
            return { order, countsLayer: layerOf(el) };
        });
        expect(layering.countsLayer, 'craft totals belong to the topmost layer').toBe('ui-layer');
        expect(layering.order.indexOf('ui-layer'), 'ui-layer is drawn last')
            .toBe(layering.order.length - 1);

        // The outline is the page colour, so it follows the theme and reads as the map
        // parting around the number rather than as a border drawn on it.
        const outline = await page.evaluate(() => {
            const el = bodies.find((b) => b.craftCount > 0).craftCountElement;
            const bg = getComputedStyle(document.documentElement).getPropertyValue('--bg-color').trim();
            return { stroke: getComputedStyle(el).stroke, bg };
        });
        const rgb = (hex) => {
            const n = parseInt(hex.slice(1), 16);
            return `rgb(${(n >> 16) & 255}, ${(n >> 8) & 255}, ${n & 255})`;
        };
        expect(outline.stroke, 'outline should be the page colour behind the grid')
            .toBe(rgb(outline.bg));

        // No dot: a parked fleet has no orbital phase, so there is no position to draw.
        expect(await page.locator('.craft-dot').count(), 'parked craft must not draw a dot').toBe(0);
        expect(await page.evaluate(() => squadrons.length), 'a squadron only exists in flight').toBe(0);

        console.log(`COUNTS ${JSON.stringify(shown.map((s) => `${s.name}:${s.text}@${s.fontPx}px`))}`);
        await g.shot('craft-counts');
        g.assertNoPageErrors();
    });

    test('a transfer scans release angles and plots every viable one', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const fan = await g.fan();
        expect(fan.count, 'at least one route').toBeGreaterThan(0);
        expect(fan.scanning).toBe(false);
        expect(fan.highlight, 'a route is picked by default').toBeGreaterThanOrEqual(0);

        // Sorted earliest-arrival first, and the default pick is the quickest.
        const mins = fan.routes.map((r) => r.minutes);
        expect(mins, 'routes are ordered by arrival').toEqual([...mins].sort((a, b) => a - b));
        expect(fan.highlight).toBe(0);

        // Distinct release angles, not the same route drawn many times.
        const angles = fan.routes.map((r) => r.releaseDeg);
        expect(new Set(angles).size, 'each route is its own release angle').toBe(angles.length);

        // Every route captures within tolerance — "viable" has to mean something.
        for (const r of fan.routes) {
            expect(r.error, `route at ${r.releaseDeg}deg`).toBeLessThanOrEqual(5);
            expect(r.minutes).toBeGreaterThan(0);
        }

        // One drawn path per route.
        const drawn = await page.evaluate(() =>
            Array.from(document.querySelectorAll('.fan-path'))
                .filter((p) => p.getAttribute('d') && p.style.display !== 'none').length);
        expect(drawn, 'every route is on the map').toBe(fan.count);

        console.log(`FAN ${fan.count} routes, ${Math.round(fan.elapsedMs)}ms, ` +
            `${mins[0]}-${mins[mins.length - 1]}min, angles ${Math.min(...angles)}-${Math.max(...angles)}deg`);
        await g.shot('fan-plotted');
        g.assertNoPageErrors();
    });

    test('dragging across the fan highlights routes and labels the duration', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const mids = await g.fanMidpoints();
        test.skip(mids.length < 2, 'needs at least two routes to sweep between');

        // Sweep from one curve to another with a real finger.
        const a = mids[0];
        const b = mids[mids.length - 1];
        await g.dragReal({ x: a.x, y: a.y }, { x: b.x, y: b.y }, { steps: 16, stepMs: 30 });
        await page.waitForTimeout(200);

        const after = await g.fan();
        expect(after.highlight, 'the finger should have carried the highlight').toBe(b.i);

        // The label reports the highlighted route, and agrees with the panel.
        const label = await page.evaluate(() => {
            const gEl = document.querySelector('.fan-label');
            return { shown: gEl.style.display !== 'none', text: gEl.querySelector('text').textContent };
        });
        expect(label.shown, 'a duration label rides the highlighted route').toBe(true);
        const expected = await page.evaluate(() => formatTransferDuration(transferFan[fanHighlight].arrivalOffset));
        expect(label.text).toBe(expected);
        expect(await page.locator('#trajectory-info-bar').textContent()).toContain(expected);

        // Only one route is emphasised at a time.
        const highlighted = await page.evaluate(() =>
            document.querySelectorAll('.fan-path.highlighted').length);
        expect(highlighted).toBe(1);

        console.log(`SWEEP highlight ${a.i} -> ${after.highlight}, label "${label.text}"`);
        await g.shot('fan-swept');
        g.assertNoPageErrors();
    });

    test('sweeping the fan picks routes instead of panning the map', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const mids = await g.fanMidpoints();
        test.skip(mids.length < 2, 'needs at least two routes to sweep between');

        const before = await page.evaluate(() => ({ x: camera.x, y: camera.y, zoom: camera.zoom }));
        await g.dragReal(
            { x: mids[0].x, y: mids[0].y },
            { x: mids[mids.length - 1].x, y: mids[mids.length - 1].y },
            { steps: 16, stepMs: 30 }
        );
        const after = await page.evaluate(() => ({ x: camera.x, y: camera.y, zoom: camera.zoom }));

        // A drag that starts on a route is a choice, not a pan.
        expect(Math.abs(after.x - before.x), 'camera x moved during a fan sweep').toBeLessThan(1);
        expect(Math.abs(after.y - before.y), 'camera y moved during a fan sweep').toBeLessThan(1);
        expect(after.zoom).toBe(before.zoom);
        g.assertNoPageErrors();
    });

    test('a drag that starts away from the fan still pans', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        // Somewhere the fan is not: the map has to stay draggable everywhere, or the
        // player loses the ability to look around while choosing.
        const spot = await page.evaluate(() => {
            const r = document.getElementById('game-svg').getBoundingClientRect();
            for (let y = 130; y < r.height - 220; y += 12) {
                for (let x = 8; x < r.width - 8; x += 12) {
                    if (fanEntryAt(x, y) < 0 && !findBodyAtPosition(x, y)) {
                        return { x: x + r.left, y: y + r.top };
                    }
                }
            }
            return null;
        });
        test.skip(!spot, 'no clear patch of map to drag from');

        const before = await page.evaluate(() => ({ x: camera.x, y: camera.y }));
        await g.dragReal(spot, { x: spot.x + 70, y: spot.y }, { steps: 10, stepMs: 25 });
        const after = await page.evaluate(() => ({ x: camera.x, y: camera.y }));

        expect(Math.abs(after.x - before.x), 'empty map should still pan').toBeGreaterThan(1);
        g.assertNoPageErrors();
    });

    test('a body under the fan can still be tapped', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        // The routes loop around the whole system, so on a small screen one reliably
        // passes under some moon. The fan wins a DRAG there — otherwise a sweep turns
        // into a pan for no visible reason — but a plain tap must still reach the body,
        // or you could no longer re-aim the transfer at whatever the curves cover.
        const spot = await page.evaluate(() => {
            const svg = document.getElementById('game-svg');
            const r = svg.getBoundingClientRect();
            for (const e of transferFan) {
                for (const p of (e._screen || [])) {
                    const b = findBodyAtPosition(p.x, p.y);
                    if (!b || b === transferSourceBody) continue;
                    if (fanEntryAt(p.x, p.y) < 0) continue;
                    // Only somewhere a finger can actually land: a panel over this point
                    // would swallow the touch, and the test would be measuring the
                    // layout rather than the gesture.
                    if (document.elementFromPoint(p.x + r.left, p.y + r.top) !== svg) continue;
                    return { x: p.x + r.left, y: p.y + r.top, name: b.name };
                }
            }
            return null;
        });
        test.skip(!spot, 'no body sits under a reachable stretch of a route');

        await page.touchscreen.tap(spot.x, spot.y);
        await page.waitForTimeout(300);

        expect(await page.evaluate(() => (selectedBody ? selectedBody.name : null)),
            `tapping ${spot.name} through the fan should select it`).toBe(spot.name);
        console.log(`TAP-THROUGH selected ${spot.name} under a route`);
        g.assertNoPageErrors();
    });

    test('launching flies the route that was highlighted', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const chosen = await page.evaluate(() => ({
            releaseAngle: transferFan[fanHighlight].releaseAngle,
            arrivalOffset: transferFan[fanHighlight].arrivalOffset,
            launchFrame: fanLaunchFrame,
        }));

        await g.scheduleLaunch();
        await page.waitForTimeout(800);

        const s = await g.state();
        expect(s.squadrons.length, 'one squadron in flight').toBe(1);
        const sq = s.squadrons[0];
        expect(sq.source).toBe('Ember');
        expect(sq.dest).toBe('Terra');
        expect(s.bodyCounts.Ember, 'craft left the origin').toBe(0);
        expect(s.transferState).toBe('none');

        // The committed flight is the highlighted route re-integrated at full
        // resolution, so it must carry the same release angle and land at the same time.
        const flown = await page.evaluate(() => ({
            releaseAngle: squadrons[0].releaseAngle,
            frames: squadrons[0].trajectoryBuffer.length,
            launchFrame: squadrons[0].launchFrame,
        }));
        expect(flown.releaseAngle).toBeCloseTo(chosen.releaseAngle, 6);
        expect(flown.launchFrame).toBe(chosen.launchFrame);
        expect(flown.frames, 'flight length should match the route chosen')
            .toBe(chosen.arrivalOffset + 1);

        console.log(`LAUNCH release ${(chosen.releaseAngle * 180 / Math.PI).toFixed(0)}deg, ` +
            `${flown.frames} frames`);
        await g.shot('launched-from-fan');
        g.assertNoPageErrors();
    });

    test('arriving craft join the destination total and stop being a squadron', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(600);

        expect(await page.evaluate(() => squadrons.length)).toBe(1);

        // Run the flight out by draining its buffer the way advanceTimeline does.
        await page.evaluate(() => {
            const sq = squadrons[0];
            sq.launchFrame = 0;
            while (sq.trajectoryBuffer.length > 1) sq.trajectoryBuffer.shift();
        });
        await page.waitForFunction(() => squadrons.length === 0, null, { timeout: 30_000, polling: 100 });

        const s = await g.state();
        expect(s.bodyCounts.Terra, 'craft should have joined Terra').toBe(5);
        expect(s.bodyCounts.Ember).toBe(0);
        // Conservation: nothing minted, nothing lost.
        const total = Object.values(s.bodyCounts).reduce((a, b) => a + b, 0);
        expect(total).toBe(5);
        await g.shot('arrived-at-terra');
        g.assertNoPageErrors();
    });

    test('a body with no route says so rather than showing an empty map', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForScan();

        // Force the empty case rather than hunting for a moment that has none.
        await page.evaluate(() => { transferFan = []; fanHighlight = -1; updateTransferPanel(); });

        const bar = await page.locator('#trajectory-info-bar').textContent();
        expect(bar, `info bar was: ${bar}`).toMatch(/no route/i);
        expect(await page.locator('#schedule-launch-btn').isDisabled()).toBe(true);
        g.assertNoPageErrors();
    });
});
