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

        // No rocket: a parked fleet has no orbital phase and nowhere to be going, so there
        // is no position to draw it at and no direction to point it in.
        expect(await page.locator('.craft-rocket').count(), 'parked craft must not draw a rocket').toBe(0);
        expect(await page.evaluate(() => squadrons.length), 'a squadron only exists in flight').toBe(0);

        console.log(`COUNTS ${JSON.stringify(shown.map((s) => `${s.name}:${s.text}@${s.fontPx}px`))}`);
        await g.shot('craft-counts');
        g.assertNoPageErrors();
    });

    test('a body writes its total and its name as one stacked block', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();

        const laid = await page.evaluate(() => bodies.map((b) => {
            const centre = bodyScreenPos(b);
            const box = b.labelElement.getBBox();
            const cnt = b.craftCountElement;
            return {
                name: b.name,
                count: bodyDisplayCraftCount(b),
                labelSize: parseFloat(getComputedStyle(b.labelElement).fontSize),
                labelFill: getComputedStyle(b.labelElement).fill,
                countFill: getComputedStyle(cnt).fill,
                labelStroke: getComputedStyle(b.labelElement).stroke,
                countStroke: getComputedStyle(cnt).stroke,
                countSize: parseFloat(getComputedStyle(cnt).fontSize),
                labelX: +b.labelElement.getAttribute('x'),
                countX: cnt.style.display === 'none' ? null : +cnt.getAttribute('x'),
                // Where the name's box sits relative to the body's centre line.
                midVsCentre: box.y + box.height / 2 - centre.y,
                topVsCentre: box.y - centre.y,
                anchor: getComputedStyle(b.labelElement).textAnchor,
            };
        }));

        for (const b of laid) {
            // The name is the quieter half of the block: smaller than the number and
            // faded off the text colour, so the count is what the eye lands on.
            expect(b.labelSize, `${b.name} name`).toBe(12);
            expect(b.countSize, `${b.name} count`).toBe(22);
            expect(b.labelSize, `${b.name} name is smaller than its count`)
                .toBeLessThan(b.countSize);
            expect(b.labelFill, `${b.name} name should be faded off the count's colour`)
                .not.toBe(b.countFill);
            // Faded in the fill only — a faded outline would lose its footing over the grid.
            expect(b.labelStroke, `${b.name} name keeps a solid outline`).toBe(b.countStroke);
            expect(b.anchor, `${b.name} name is left-aligned with the number`).toBe('start');

            if (b.count > 0) {
                // Stacked: same left edge, name below the centre line the number rises from.
                expect(b.countX, `${b.name} count and name share a left edge`).toBeCloseTo(b.labelX, 3);
                expect(b.topVsCentre, `${b.name} name hangs below the centre line`)
                    .toBeGreaterThan(-6);
                expect(b.midVsCentre, `${b.name} name sits under the number`).toBeGreaterThan(4);
            } else {
                // Nothing to hang from, so the name centres on the body instead.
                expect(Math.abs(b.midVsCentre), `${b.name} name should centre on the body`)
                    .toBeLessThan(0.5);
            }
        }

        // Both pieces live in the top layer: a block whose number can never be covered but
        // whose name can would read as broken rather than as layered.
        const layers = await page.evaluate(() => {
            const layerOf = (n) => { while (n && !n.id) n = n.parentNode; return n ? n.id : null; };
            const b = bodies[0];
            return { label: layerOf(b.labelElement), count: layerOf(b.craftCountElement) };
        });
        expect(layers.label).toBe('ui-layer');
        expect(layers.count).toBe('ui-layer');

        console.log(`LABELS ${laid.map((b) => `${b.name}:${b.count}`).join(' ')}`);
        await g.shot('labels-stacked');
        g.assertNoPageErrors();
    });

    test('a fleet says how many it is at both ends of a trip, and only at one', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(600);

        // At rest a fleet is a number beside its body. Under way it is a number on its
        // rocket — smaller, because it is written on a 17px hull, and inverted, because it
        // has to read against that hull rather than against the map behind it.
        const written = await page.evaluate(() => {
            const label = getComputedStyle(squadrons[0].rocket.count);
            return {
                text: squadrons[0].rocket.count.textContent,
                fill: label.fill,
                fontPx: parseFloat(label.fontSize),
                hullFill: getComputedStyle(squadrons[0].rocket.hull).fill,
                length: ROCKET_LENGTH_PX,
                // How wide the digits actually draw, in the rocket's own frame — which is
                // the only way to ask whether they fit on it.
                inkWidth: squadrons[0].rocket.count.getBBox().width,
                parkedPx: parseFloat(getComputedStyle(bodies[0].craftCountElement).fontSize),
            };
        });

        expect(written.text, 'the whole fleet, on the one icon that is it').toBe('5');
        expect(written.fill, 'contrasting with the hull it is written on')
            .not.toBe(written.hullFill);
        // The barrel runs from the tail to the nose, 84% of the overall length — the rest
        // is fins standing off behind it. The number has to stay on the barrel.
        expect(written.inkWidth, 'and small enough to stay on it')
            .toBeLessThan(written.length * 0.84);

        // And written once. These five have left Ember's total — they are standing on the
        // rocket, not on the planet, and counting them in both places would show the same
        // fleet twice side by side.
        expect((await g.state()).displayedCounts.Ember, 'not also counted at the body').toBe(0);

        console.log(`WRITTEN "${written.text}" at ${written.fontPx}px drawing ` +
            `${written.inkWidth.toFixed(1)}px wide on a ${written.length.toFixed(1)}px hull; ` +
            `parked counts run ${written.parkedPx}px`);
        await g.shot('count-in-flight');
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

    test('each route gets its own colour, and only the chosen one is opaque', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const paint = await page.evaluate(() => {
            const paths = Array.from(document.querySelectorAll('.fan-path'))
                .filter((p) => p.getAttribute('d') && p.style.display !== 'none');
            return {
                strokes: paths.map((p) => getComputedStyle(p).stroke),
                opacities: paths.map((p) => +getComputedStyle(p).opacity),
                highlighted: paths.map((p) => p.classList.contains('highlighted')),
                labelStroke: getComputedStyle(document.querySelector('.fan-label rect')).stroke,
            };
        });

        // A colour each: with one accent for all of them, a crossing was unreadable.
        expect(new Set(paint.strokes).size, 'no two routes share a colour')
            .toBe(paint.strokes.length);
        // And a real colour, not a var() that failed to resolve to anything.
        for (const s of paint.strokes) expect(s).toMatch(/^rgba?\(/);

        // Exactly one at full strength, the rest translucent behind it.
        const opaque = paint.opacities.filter((o) => o === 1).length;
        expect(opaque, 'only the chosen route is fully opaque').toBe(1);
        for (let i = 0; i < paint.opacities.length; i++) {
            if (!paint.highlighted[i]) expect(paint.opacities[i]).toBeLessThan(1);
        }
        expect(paint.highlighted.indexOf(true), 'the opaque one is the highlighted one')
            .toBe(paint.opacities.indexOf(1));

        // The label borrows the highlighted route's colour, which is what says which
        // curve the number belongs to.
        expect(paint.labelStroke).toBe(paint.strokes[paint.opacities.indexOf(1)]);

        console.log(`COLOURS ${paint.strokes.length} routes: ${paint.strokes.join(' ')}`);
        await g.shot('fan-coloured');
        g.assertNoPageErrors();
    });

    test('a trajectory in flight is drawn translucent', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(800);

        const flights = await page.evaluate(() =>
            Array.from(document.querySelectorAll('.craft-trajectory'))
                .filter((p) => (p.getAttribute('d') || '').length > 0)
                .map((p) => ({
                    opacity: +getComputedStyle(p).opacity,
                    selected: p.classList.contains('selected'),
                })));

        expect(flights.length, 'a squadron is in the air').toBeGreaterThan(0);
        for (const f of flights) {
            // Translucent, but not so faint it drops below the grid lines it crosses.
            if (!f.selected) {
                expect(f.opacity).toBeLessThan(1);
                expect(f.opacity).toBeGreaterThanOrEqual(0.5);
            }
        }

        console.log(`IN FLIGHT ${flights.map((f) => f.opacity).join(', ')}`);
        await g.shot('in-flight-translucent');
        g.assertNoPageErrors();
    });

    test('scrubbing forward eats the path already flown', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        // The launch moment and the flight from it, separately: a craft has no path behind
        // it until it has left, and it does not leave until the launch (see
        // TRANSFER_LEAD_MINUTES), so everything below is measured from there.
        const { launch, flight } = await page.evaluate(() => ({
            launch: fanLaunchFrame * PREDICTION_DT,
            flight: transferFan[fanHighlight].arrivalOffset * PREDICTION_DT,
        }));
        await g.scheduleLaunch();
        await page.waitForTimeout(500);
        await g.viewMinute(Math.ceil(launch) + 1);
        await page.waitForTimeout(300);

        // Where the drawn path begins, and where the rocket is. The two have to be the
        // same point: a path that starts anywhere else leaves a straight run from the craft
        // back to wherever it does start.
        const sample = () => page.evaluate(() => {
            const path = document.querySelector('.craft-trajectory');
            const rocket = document.querySelector('.craft-rocket:not(.preview)');
            const d = path.getAttribute('d') || '';
            const m = d.match(/^M ([-\d.]+) ([-\d.]+)/);
            const t = rocket && /translate\(([-\d.e+]+) ([-\d.e+]+)\)/.exec(rocket.getAttribute('transform') || '');
            return {
                empty: d.length === 0,
                start: m ? { x: +m[1], y: +m[2] } : null,
                vertices: (d.match(/L /g) || []).length,
                dot: t ? { x: +t[1], y: +t[2] } : null,
                dotShown: rocket ? getComputedStyle(rocket).display !== 'none' : false,
            };
        });

        const early = await sample();
        expect(early.start, 'the path is drawn').not.toBeNull();
        expect(Math.hypot(early.start.x - early.dot.x, early.start.y - early.dot.y),
            'the path starts at the craft, not behind it').toBeLessThan(2);

        // Two thirds of the way there.
        await g.viewMinute(Math.round(launch + flight * 0.66));
        await page.waitForTimeout(300);
        const late = await sample();

        expect(late.start).not.toBeNull();
        expect(Math.hypot(late.start.x - late.dot.x, late.start.y - late.dot.y),
            'still starts at the craft after scrubbing').toBeLessThan(2);
        // The flown part is consumed, so there is materially less line left.
        expect(late.vertices, 'the path shortens as the craft advances')
            .toBeLessThan(early.vertices * 0.6);

        console.log(`CONSUME ${early.vertices} -> ${late.vertices} vertices ` +
            `over ${Math.round(flight * 0.66)}m of a ${flight.toFixed(0)}m flight ` +
            `launching at +${launch.toFixed(0)}m`);
        await g.shot('path-consumed');

        // Past arrival there is neither a path nor a rocket — those craft are part of the
        // destination's total by then, and drawing them too would show them twice.
        await g.viewMinute(Math.ceil(launch + flight) + 10);
        await page.waitForTimeout(300);
        const arrived = await sample();
        expect(arrived.empty, 'no path left after arrival').toBe(true);
        expect(arrived.dot === null || !arrived.dotShown, 'no rocket left after arrival').toBe(true);

        await g.shot('after-arrival');
        g.assertNoPageErrors();
    });

    test('craft that have landed can be sent straight on again', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        // When it lands, counted from the present: the launch moment plus the flight. A
        // transfer opens on a launch some minutes ahead (see TRANSFER_LEAD_MINUTES), so
        // the flight time alone would leave the clock short of the arrival.
        const minutes = await page.evaluate(
            () => (fanLaunchFrame + transferFan[fanHighlight].arrivalOffset) * PREDICTION_DT);
        await g.scheduleLaunch();
        await page.waitForTimeout(500);

        // Run the clock forward to watch them land. This is the only way anyone sees an
        // arrival — a flight is over an hour of game time — so it is the normal case, not
        // an edge one. The present has NOT caught up: Terra's own craftCount is still 0.
        await g.viewMinute(Math.ceil(minutes) + 5);
        await page.waitForTimeout(400);

        const landed = await page.evaluate(() => {
            const terra = bodies.find((b) => b.name === 'Terra');
            return {
                shown: terra.craftCountElement.textContent,
                raw: terra.craftCount,
                canSend: bodyCanSend(terra),
            };
        });
        expect(landed.shown, 'Terra shows the fleet that just arrived').toBe('5');
        expect(landed.raw, 'the present has not reached the arrival yet').toBe(0);
        // The gate has to agree with the number on the map, not with the present.
        expect(landed.canSend, 'a body showing craft must be draggable').toBe(true);

        // And the gesture itself works: drag Terra -> Gaia and get a fan, not a pan.
        await g.tapBody('Terra');
        await page.waitForTimeout(200);
        await g.beginTransfer('Terra', 'Gaia');
        await g.waitForScan();

        expect(await page.evaluate(() => transferSourceBody?.name)).toBe('Terra');
        expect(await page.evaluate(() => transferDestinationBody?.name)).toBe('Gaia');
        // The slider must offer the landed craft, drawn from the squadron still recorded
        // as in flight.
        expect(await page.evaluate(() => +transferQtySlider.max),
            'the landed fleet is what there is to send').toBe(5);

        console.log(`RESEND Terra shows ${landed.shown} (raw ${landed.raw}), ` +
            `onward slider max ${await page.evaluate(() => transferQtySlider.max)}`);
        await g.shot('resend-after-landing');
        g.assertNoPageErrors();
    });

    test('the burn arrow goes away with the craft that was burning', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        // Chain two legs, because the second one is short enough that its burn runs to the
        // very last frame of the flight — which is the case that stranded the arrow.
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        // The minute leg one lands on: its launch moment plus its flight, since a transfer
        // opens on a launch ahead of the present (see TRANSFER_LEAD_MINUTES). Leg two needs
        // no such allowance — the clock is already far past the lead by then, so that
        // search opens on the moment in view.
        const legOne = await page.evaluate(
            () => (fanLaunchFrame + transferFan[fanHighlight].arrivalOffset) * PREDICTION_DT);
        await g.scheduleLaunch();
        await page.waitForTimeout(400);

        await g.viewMinute(Math.ceil(legOne) + 5);
        await page.waitForTimeout(300);
        await g.tapBody('Terra');
        await g.beginTransfer('Terra', 'Luna');
        await g.waitForScan();
        const leg = await page.evaluate(() => {
            const e = transferFan[fanHighlight];
            return e ? { arrival: e.arrivalOffset, burnStart: e.burn.start, burnDur: e.burn.duration } : null;
        });
        test.skip(!leg, 'needs a route on the second leg');
        await g.scheduleLaunch();
        await page.waitForTimeout(400);

        // The burn as depicted must fit inside the flight. The optimizer may hand back one
        // that runs past the arrival — nothing after arrival is integrated, so the tail is
        // free to it — but a craft cannot be shown burning on frames it does not have.
        const shown = await page.evaluate(() => {
            const sq = squadrons.find((s) => s.destinationBody?.name === 'Luna');
            return sq.correctionParams
                ? { start: sq.correctionParams.startFrame, dur: sq.correctionParams.duration,
                    flight: sq.trajectoryBuffer.length }
                : null;
        });
        if (shown) {
            expect(shown.start + shown.dur, 'the drawn burn must fit inside the flight')
                .toBeLessThanOrEqual(shown.flight);
        }

        // Run the clock well past the arrival and check nothing is left pinned to the map.
        const end = Math.ceil(legOne) + 5 + leg.arrival * 0.1 + 40;
        await g.viewMinute(Math.round(end));
        await page.waitForTimeout(400);

        const leftovers = await page.evaluate(() => squadrons.map((sq) => ({
            dst: sq.destinationBody?.name,
            drawn: sq._displayCount,
            correcting: sq.isCorrecting,
            arrow: sq.correctionArrow ? sq.correctionArrow.style.display : 'gone',
            dot: sq.element ? sq.element.style.display : 'gone',
        })));

        for (const s of leftovers) {
            if (s.drawn > 0) continue;
            // A squadron with nothing drawn must leave nothing behind — the arrow is set
            // further down updateElements() than the dot, so it is the piece that gets
            // forgotten when the craft stops being drawn.
            expect(s.arrow, `${s.dst}: no arrow once the craft is gone`).toBe('none');
            expect(s.dot, `${s.dst}: no dot once the craft is gone`).toBe('none');
        }
        expect(await page.locator('line[marker-end]:visible').count(),
            'no burn arrow anywhere on the map').toBe(0);

        console.log(`ARROW leg2 arrival ${leg.arrival}f, burn ${leg.burnStart}+${leg.burnDur}f ` +
            `-> drawn ${shown ? shown.start + '+' + shown.dur : 'none'}`);
        await g.shot('no-stuck-arrow');
        g.assertNoPageErrors();
    });

    test('dragging across the fan highlights routes and labels the duration', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        // The view glides onto the chosen route as the fan lands, so the curves are still
        // moving; midpoints read now would be aimed at where they used to be.
        await g.waitForViewSettled();

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

        await g.waitForViewSettled();

        const mids = await g.fanMidpoints();
        test.skip(mids.length < 2, 'needs at least two routes to sweep between');

        // Sampled throughout rather than compared at the ends: the framing takes the
        // camera back the instant the finger lifts, so a reading taken after the gesture
        // says nothing about what happened during it.
        const before = await page.evaluate(() => {
            window.__panTrace = [];
            window.__panTimer = setInterval(
                () => window.__panTrace.push([camera.x, camera.y, camera.zoom]), 40);
            return { x: camera.x, y: camera.y, zoom: camera.zoom, paused: isAutoFitPaused };
        });
        await g.dragReal(
            { x: mids[0].x, y: mids[0].y },
            { x: mids[mids.length - 1].x, y: mids[mids.length - 1].y },
            { steps: 16, stepMs: 30 }
        );
        const after = await page.evaluate(() => {
            clearInterval(window.__panTimer);
            return { trace: window.__panTrace, paused: isAutoFitPaused, released: transferViewReleased };
        });

        // A drag that starts on a route is a choice, not a pan: it neither drags the view
        // along under the finger...
        expect(after.trace.length, 'the sweep should have been sampled').toBeGreaterThan(4);
        for (const [x, y, zoom] of after.trace) {
            expect(Math.abs(x - before.x), 'camera x moved during a fan sweep').toBeLessThan(1);
            expect(Math.abs(y - before.y), 'camera y moved during a fan sweep').toBeLessThan(1);
            // A bound rather than exact equality: the first sample can land a frame before
            // the finger does, while the framing is still settling by fractions of a pixel.
            expect(Math.abs(Math.log(zoom / before.zoom)), 'zoom moved during a fan sweep')
                .toBeLessThan(1e-3);
        }
        // ...nor hands the view over the way panning does.
        expect(after.paused, 'a fan sweep is not a manual pan').toBe(before.paused);
        expect(after.released, 'and does not release the transfer framing').toBe(false);
        g.assertNoPageErrors();
    });

    test('a drag that starts away from the fan still pans', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.waitForViewSettled();   // or the clear patch has moved by the time it is used

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
        await g.waitForViewSettled();   // or the body has slid out from under the point found

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

    test('planning drops the map to true scale, and gives it back', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();

        // Pan by hand first, as any real session does — that pauses auto-fit for good, so
        // nothing but the handback will put the view back afterwards.
        await page.evaluate(() => {
            isAutoFitPaused = true;
            camera.zoom = 0.13; camera.x = -280; camera.y = -150;
        });
        await page.waitForTimeout(400);
        const before = await page.evaluate(() => ({
            on: trueScaleOn, scale: trueScale, zoom: camera.zoom, x: camera.x, y: camera.y,
        }));
        expect(before.on, 'the schematic view is the starting point').toBe(false);

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await page.waitForTimeout(1800);   // the toggle eases over TRUE_SCALE_EASE_MS

        const during = await page.evaluate(() => ({
            on: trueScaleOn, scale: trueScale, zoom: camera.zoom,
            btnActive: document.getElementById('true-scale-btn').classList.contains('active'),
            remembered: scaleBeforeTransfer,
        }));
        expect(during.on, 'planning switches to true scale').toBe(true);
        expect(during.scale, 'and the ease should have finished').toBeCloseTo(1, 3);
        // The button has to agree, or the map is in a mode its own control denies.
        expect(during.btnActive).toBe(true);
        expect(during.remembered, 'the mode to put back is remembered').toBe(false);
        // Framing the route is a different view from the one the player had.
        expect(Math.abs(Math.log(during.zoom / before.zoom))).toBeGreaterThan(0.1);

        await g.cancelTransfer();
        await page.waitForTimeout(1200);       // the scale ease
        await g.waitForViewSettled();

        const after = await page.evaluate(() => ({
            on: trueScaleOn, scale: trueScale, zoom: camera.zoom, x: camera.x, y: camera.y,
            btnActive: document.getElementById('true-scale-btn').classList.contains('active'),
            remembered: scaleBeforeTransfer, restore: viewRestore,
        }));
        expect(after.on, 'the schematic view comes back').toBe(false);
        expect(after.scale).toBeCloseTo(0, 3);
        expect(after.btnActive).toBe(false);
        expect(after.remembered, 'nothing left to restore').toBe(null);
        expect(after.restore).toBe(null);
        // And so does the camera. Auto-fit is paused, so if the handback did not happen
        // the view would still be parked on a route that no longer exists.
        //
        // Judged in screen pixels: the ease stops once the remaining move is sub-pixel,
        // which at this zoom is several world units and would fail a world-unit tolerance
        // for no reason a player could ever see.
        const offBy = Math.hypot(after.x - before.x, after.y - before.y) * after.zoom;
        expect(after.zoom, 'zoom returned').toBeCloseTo(before.zoom, 3);
        expect(offBy, 'centre returned, to within a pixel').toBeLessThan(1);

        console.log(`SCALE MODE ${before.zoom.toFixed(3)} schematic -> ` +
            `${during.zoom.toFixed(3)} true -> ${after.zoom.toFixed(3)} schematic`);
        g.assertNoPageErrors();
    });

    test('the view frames the two bodies and the route being considered', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.beginTransfer('Ember', 'Terra');
        // Two routes at least: this asserts that picking a different one reframes, which
        // needs a different one to exist.
        await g.waitForTrajectories({ minRoutes: 2 });
        await page.waitForTimeout(1200);   // the scale ease, which the fit tracks across
        await g.waitForViewSettled();

        // Screen extent of everything that must be in frame, against the space actually
        // left over by the panels a transfer puts on top of the map.
        const framing = () => page.evaluate(() => {
            const view = transferFitViewport();
            const pts = highlightedFanEntry()._screen;
            let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
            const add = (x, y) => {
                minX = Math.min(minX, x); maxX = Math.max(maxX, x);
                minY = Math.min(minY, y); maxY = Math.max(maxY, y);
            };
            for (const p of pts) add(p.x, p.y);
            for (const b of [transferSourceBody, transferDestinationBody]) {
                const s = bodyScreenPos(b);
                add(s.x, s.y);
            }
            return {
                view, minX, maxX, minY, maxY,
                spanX: maxX - minX, spanY: maxY - minY,
                zoom: camera.zoom, highlight: fanHighlight,
                duration: transferFan[fanHighlight].arrivalOffset,
            };
        });

        const f = await framing();
        // Inside the visible band, top and bottom — a route that runs under the launch
        // panel is a route the player cannot see the shape of, which is the whole point.
        const SLOP = 8;   // stroke width and the fit's sampling stride
        expect(f.minY, 'route clears the readout').toBeGreaterThan(f.view.cy - f.view.height / 2 - SLOP);
        expect(f.maxY, 'route clears the launch panel').toBeLessThan(f.view.cy + f.view.height / 2 + SLOP);
        expect(f.minX).toBeGreaterThan(f.view.cx - f.view.width / 2 - SLOP);
        expect(f.maxX).toBeLessThan(f.view.cx + f.view.width / 2 + SLOP);

        // And it fills that space rather than sitting small in the middle of it: one of
        // the two axes has to be doing the constraining, or this is not a fit.
        const fill = Math.max(f.spanX / f.view.width, f.spanY / f.view.height);
        expect(fill, 'the framing should be tight').toBeGreaterThan(0.85);

        // Picking a different route re-frames for that route, and it too ends up in frame.
        await page.evaluate(() => {
            fanHighlight = transferFan.length - 1;   // the slowest, and the widest-ranging
            updateTransferPanel();
        });
        await g.waitForViewSettled();
        const g2 = await framing();

        expect(g2.highlight).not.toBe(f.highlight);
        expect(Math.abs(Math.log(g2.zoom / f.zoom)), 'a different route is a different view')
            .toBeGreaterThan(0.05);
        expect(g2.minY).toBeGreaterThan(g2.view.cy - g2.view.height / 2 - SLOP);
        expect(g2.maxY).toBeLessThan(g2.view.cy + g2.view.height / 2 + SLOP);
        expect(Math.max(g2.spanX / g2.view.width, g2.spanY / g2.view.height)).toBeGreaterThan(0.85);

        console.log(`FRAME route ${f.highlight} (${f.duration}f) fills ${(fill * 100).toFixed(0)}% ` +
            `at zoom ${f.zoom.toFixed(3)}; route ${g2.highlight} (${g2.duration}f) at ${g2.zoom.toFixed(3)}`);
        await g.shot('framed-route');
        g.assertNoPageErrors();
    });

    test('the opening of a transfer goes straight to the route, not via the pair', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForViewSettled();

        // Sample from before the drag right through the scan landing. Two bodies are not
        // the thing being framed — the route between them is, and it is bigger and lies
        // somewhere else — so a fit that took the pair at face value while the scan was out
        // would zoom onto them and slide to their midpoint, then undo both.
        await page.evaluate(() => {
            window.__camTrace = [];
            window.__camTimer = setInterval(
                () => window.__camTrace.push([camera.zoom, camera.x, camera.y, transferFan.length]), 40);
        });
        const start = await page.evaluate(() => ({ zoom: camera.zoom, x: camera.x, y: camera.y }));

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.waitForViewSettled();

        const got = await page.evaluate(() => {
            clearInterval(window.__camTimer);
            return { trace: window.__camTrace, zoom: camera.zoom, x: camera.x, y: camera.y };
        });

        const searching = got.trace.filter(([, , , n]) => n === 0);
        expect(searching.length, 'the scan should have been sampled').toBeGreaterThan(3);
        for (const [zoom, x, y] of searching) {
            // Widening is allowed, and needed: the switch to true scale pulls the bodies
            // apart to their real separation through this window, and the view has to keep
            // up or they leave the screen. Tightening is the half that is guessing.
            expect(zoom, 'the view must not tighten before there is a route to frame')
                .toBeLessThanOrEqual(start.zoom * 1.001);
            // And it may not go looking for a centre it has no way of knowing yet. Measured
            // in screen pixels, which is what a player would see move.
            expect(Math.hypot(x - start.x, y - start.y) * zoom,
                'the view must not slide before there is a route to frame').toBeLessThan(2);
        }

        // Across the whole opening the camera should travel in one straight line, arriving
        // rather than overshooting and recovering. A dogleg out to the pair and back would
        // put the path well above the straight-line distance.
        let path = 0;
        for (let i = 1; i < got.trace.length; i++) {
            const [z, x, y] = got.trace[i];
            const [, px, py] = got.trace[i - 1];
            path += Math.hypot(x - px, y - py) * z;
        }
        const straight = Math.hypot(got.x - start.x, got.y - start.y) * got.zoom;
        expect(path, 'the camera should travel in one straight line').toBeLessThan(straight * 1.3 + 8);

        const peak = Math.max(...got.trace.map(([z]) => z));
        expect(peak / got.zoom, 'the zoom should arrive, not overshoot and recover')
            .toBeLessThan(1.05);

        console.log(`OPENING ${start.zoom.toFixed(3)} -> ${got.zoom.toFixed(3)}, ` +
            `camera travelled ${path.toFixed(0)}px over a ${straight.toFixed(0)}px move, ` +
            `still through all ${searching.length} scan samples`);
        g.assertNoPageErrors();
    });

    test('the map holds still under a finger choosing a route', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.beginTransfer('Ember', 'Terra');
        // A sweep that has nothing to sweep between proves nothing about holding still.
        await g.waitForTrajectories({ minRoutes: 2 });
        await g.waitForViewSettled();

        // Sample the camera and the pick throughout a real sweep. Reframing mid-gesture
        // moves the curves out from under the finger comparing them, which changes which
        // one is nearest — a loop that flips the pick back and forth while the finger
        // travels steadily one way.
        await page.evaluate(() => {
            window.__trace = [];
            window.__timer = setInterval(() => {
                window.__trace.push([fanHighlight, camera.zoom, camera.x, camera.y]);
            }, 50);
        });
        await g.dragReal({ x: 40, y: 300 }, { x: 350, y: 300 }, { steps: 20, stepMs: 40 });
        const swept = await page.evaluate(() => {
            clearInterval(window.__timer);
            return { trace: window.__trace, highlight: fanHighlight, zoom: camera.zoom };
        });

        expect(swept.trace.length, 'the sweep should have been sampled').toBeGreaterThan(10);
        // Both bounds are in screen pixels, because that is where holding still is a claim
        // about anything: what must not move is the curves under the finger comparing them.
        // A tolerance in world units or in raw zoom says nothing on its own at a zoom of a
        // tenth — and reads as a decimal place the easing has to land on rather than as a
        // distance, which is a thing frame timing can decide.
        const [, zoom0, x0, y0] = swept.trace[0];
        const edge = 200; // px from centre; roughly the corner of either phone
        for (const [, zoom, x, y] of swept.trace) {
            expect(Math.abs(Math.log(zoom / zoom0)) * edge, 'zoom must not move under the finger')
                .toBeLessThan(0.05);
            expect(Math.hypot(x - x0, y - y0) * zoom, 'the map must not pan under the finger')
                .toBeLessThan(0.05);
        }
        // The sweep did choose something along the way, or this proves nothing.
        const picks = new Set(swept.trace.map((t) => t[0]));
        expect(picks.size, 'the sweep should have moved through routes').toBeGreaterThan(1);

        // Lifting is when the framing happens.
        await page.waitForTimeout(2000);
        const after = await page.evaluate(() => ({ zoom: camera.zoom, highlight: fanHighlight }));
        expect(after.highlight, 'the choice survives the release').toBe(swept.highlight);
        expect(Math.abs(Math.log(after.zoom / swept.zoom)), 'and is framed once the finger is off')
            .toBeGreaterThan(0.05);

        console.log(`SWEEP ${picks.size} routes touched, held at zoom ` +
            `${swept.zoom.toFixed(3)}, framed to ${after.zoom.toFixed(3)} on release`);
        g.assertNoPageErrors();
    });

    test('taking the view by hand stops the framing but keeps the scale', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.waitForViewSettled();

        const grabbed = await page.evaluate(() => {
            handleWheel({ preventDefault() {}, clientX: 195, clientY: 300, deltaY: -300 });
            return { zoom: camera.zoom, x: camera.x, y: camera.y, released: transferViewReleased };
        });
        expect(grabbed.released, 'a manual zoom hands the view back to the player').toBe(true);

        await page.waitForTimeout(1500);
        const held = await page.evaluate(() => ({
            zoom: camera.zoom, x: camera.x, y: camera.y, on: trueScaleOn,
        }));
        // The fit must not claw it back — a camera that argues with a pinch reads as a map
        // that refuses to be moved.
        expect(held.zoom).toBeCloseTo(grabbed.zoom, 6);
        expect(held.x).toBeCloseTo(grabbed.x, 3);
        // The scale mode is a separate promise and stays until the transfer ends.
        expect(held.on, 'true scale is not given up with the camera').toBe(true);

        // Re-aiming at a new destination is a new decision, so the framing comes back.
        await g.dragTouch(await g.bodyPoint('Ember'), await g.bodyPoint('Gaia'), { holdMs: 500 });
        await page.waitForTimeout(400);
        const reaimed = await page.evaluate(() => ({
            released: transferViewReleased, dest: transferDestinationBody?.name,
        }));
        expect(reaimed.dest).toBe('Gaia');
        expect(reaimed.released, 'a new pair gets the framing back').toBe(false);

        console.log(`RELEASE held at ${held.zoom.toFixed(3)} through the transfer, ` +
            `framing resumed on re-aim to ${reaimed.dest}`);
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
