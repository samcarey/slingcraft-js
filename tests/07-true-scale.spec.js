const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

/**
 * The to-scale toggle: the display's two exaggerations — bodies drawn far larger
 * than they are, and pulled far closer together than they are — switched off
 * together over one eased second.
 *
 * These assertions are all against the SIMULATION's own numbers rather than
 * against recorded pixel values, so they say "the picture is true", not "the
 * picture is what it was the day this was written".
 */

/** Every drawn quantity next to the true one it is supposed to match. */
const drawn = (page) =>
    page.evaluate(() => {
        const pairs = [];
        for (let i = 0; i < bodies.length; i++) {
            for (let j = i + 1; j < bodies.length; j++) {
                const a = bodies[i], b = bodies[j];
                const pa = bodyScreenPos(a), pb = bodyScreenPos(b);
                pairs.push({
                    pair: `${a.name}-${b.name}`,
                    // back out of screen px into world units, so the comparison
                    // does not depend on whatever zoom the fit happened to pick
                    drawn: Math.hypot(pb.x - pa.x, pb.y - pa.y) / camera.zoom,
                    truth: Math.hypot(b.x - a.x, b.y - a.y),
                });
            }
        }
        return {
            trueScale,
            radii: bodies.map((b) => ({
                name: b.name,
                drawn: bodyScreenRadius(b),
                truth: b.radius * camera.zoom,
            })),
            pairs,
        };
    });

/** How far the warp displaces the worst point in the viewport, in px. */
const maxWarp = (page) =>
    page.evaluate(() => {
        let worst = 0;
        for (let x = 0; x <= svgWidth; x += 20) {
            for (let y = 0; y <= svgHeight; y += 20) {
                const w = warpScreenPoint(x, y);
                worst = Math.max(worst, Math.hypot(w.x - x, w.y - y));
            }
        }
        return worst;
    });

test.describe('the to-scale view', () => {
    test('the toggle sits just left of the clock, on the same row', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();

        const [scale, clock] = await page.evaluate(() =>
            ['true-scale-btn', 'time-scrub-btn'].map((id) => {
                const r = document.getElementById(id).getBoundingClientRect();
                return { x: r.x, right: r.right, y: r.y, w: r.width, h: r.height };
            }));

        expect(scale.right, 'to-scale button is not left of the clock').toBeLessThanOrEqual(clock.x);
        expect(Math.abs(scale.y - clock.y), 'the two buttons are not on the same row').toBeLessThan(1);
        // Adjacent, not merely somewhere to the left
        expect(clock.x - scale.right).toBeLessThan(20);
        // Same 44px-minimum target the rest of the UI keeps
        expect(Math.min(scale.w, scale.h)).toBeGreaterThanOrEqual(44);
        await g.expectOnScreen('#true-scale-btn', 'to-scale button');
    });

    test('the schematic view is exaggerated, and says so in its numbers', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        const d = await drawn(page);
        expect(d.trueScale).toBe(0);
        // Every body drawn bigger than life, and the moons much bigger
        for (const r of d.radii) {
            expect(r.drawn, `${r.name} is not exaggerated`).toBeGreaterThan(r.truth * 1.5);
        }
        // A moon's separation from its planet is the most compressed thing on
        // screen — it has to be, or the moon would be swallowed by the disc.
        const luna = d.pairs.find((p) => p.pair === 'Terra-Luna');
        expect(luna.drawn).toBeGreaterThan(luna.truth * 5);
        expect(await maxWarp(page), 'the schematic view should be visibly warped').toBeGreaterThan(5);
    });

    test('to scale means to scale: true radii, true separations, no warp', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tap(page.locator('#true-scale-btn'));
        await expect.poll(() => page.evaluate(() => trueScale), { timeout: 4000 }).toBe(1);
        await g.shot('true-scale');

        const d = await drawn(page);
        for (const r of d.radii) {
            expect(Math.abs(r.drawn - r.truth), `${r.name} is drawn at ${r.drawn}, true is ${r.truth}`)
                .toBeLessThan(1e-6);
        }
        for (const p of d.pairs) {
            const err = Math.abs(p.drawn - p.truth);
            expect(err, `${p.pair} drawn ${p.drawn.toFixed(2)} world units apart, truly ${p.truth.toFixed(2)}`)
                .toBeLessThan(0.01);
        }
        // With display positions equal to true positions there is nothing left
        // for the warp to correct, so the grid must come back perfectly straight.
        expect(await maxWarp(page), 'space is still bent in the to-scale view').toBe(0);

        expect(await page.locator('#true-scale-btn').getAttribute('class')).toContain('active');
    });

    test('the transition is eased over about a second, and never runs backwards', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await page.evaluate(() => {
            window.__trace = [];
            window.__tracing = true;
            const tick = () => {
                window.__trace.push([performance.now(), trueScale]);
                if (window.__tracing) requestAnimationFrame(tick);
            };
            requestAnimationFrame(tick);
        });
        const t0 = await page.evaluate(() => performance.now());
        await g.tap(page.locator('#true-scale-btn'));
        await expect.poll(() => page.evaluate(() => trueScale), { timeout: 4000 }).toBe(1);
        await page.waitForTimeout(150);

        const trace = await page.evaluate((start) => {
            window.__tracing = false;
            const s = window.__trace.filter(([t]) => t >= start);
            const done = s.find(([, v]) => v >= 1);
            let backwards = 0;
            for (let i = 1; i < s.length; i++) if (s[i][1] < s[i - 1][1] - 1e-9) backwards++;
            // Value nearest the halfway point in time, to check it is eased and
            // not linear: a cubic ease-in-out passes 0.5 at the midpoint but
            // spends the first quarter well under a linear ramp.
            const quarter = s.reduce((best, cur) =>
                Math.abs(cur[0] - start - 250) < Math.abs(best[0] - start - 250) ? cur : best);
            return { settledMs: done ? done[0] - start : null, backwards, frames: s.length,
                     quarterValue: quarter[1] };
        }, t0);

        console.log(`TRUE-SCALE eased to 1 in ${Math.round(trace.settledMs)}ms over ${trace.frames} frames`);
        expect(trace.backwards, 'the value stepped backwards mid-transition').toBe(0);
        // A second, plus a frame's slack at each end for tap dispatch and rAF
        expect(trace.settledMs).toBeGreaterThan(900);
        expect(trace.settledMs).toBeLessThan(1250);
        // Eased in, so a quarter of the way through it has covered well under a
        // quarter of the distance. Linear would be ~0.25 here.
        expect(trace.quarterValue).toBeLessThan(0.18);
    });

    test('toggling back restores the schematic view', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        const before = await drawn(page);

        await g.tap(page.locator('#true-scale-btn'));
        await expect.poll(() => page.evaluate(() => trueScale), { timeout: 4000 }).toBe(1);
        await g.tap(page.locator('#true-scale-btn'));
        await expect.poll(() => page.evaluate(() => trueScale), { timeout: 4000 }).toBe(0);

        const after = await drawn(page);
        for (const r of after.radii) {
            const was = before.radii.find((x) => x.name === r.name);
            // Bodies keep orbiting while this runs, so compare the exaggeration
            // ratio rather than raw pixels
            expect(r.drawn / r.truth, `${r.name} did not go back to its exaggerated size`)
                .toBeCloseTo(was.drawn / was.truth, 1);
        }
        expect(await maxWarp(page), 'the warp did not come back').toBeGreaterThan(5);
        expect(await page.locator('#true-scale-btn').getAttribute('class') || '').not.toContain('active');
    });

    test('a reversal mid-transition turns round without snapping', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await page.evaluate(() => {
            window.__trace = []; window.__tracing = true;
            const tick = () => {
                window.__trace.push(trueScale);
                if (window.__tracing) requestAnimationFrame(tick);
            };
            requestAnimationFrame(tick);
        });
        await g.tap(page.locator('#true-scale-btn'));
        await page.waitForTimeout(300);
        await g.tap(page.locator('#true-scale-btn'));   // changed my mind, partway across
        await expect.poll(() => page.evaluate(() => trueScale), { timeout: 4000 }).toBe(0);
        await page.waitForTimeout(100);

        const t = await page.evaluate(() => {
            window.__tracing = false;
            const s = window.__trace;
            const peak = Math.max(...s);
            const peakAt = s.indexOf(peak);
            // Biggest single-frame drop after the turn: a snap back to 0 would
            // show up as one frame swallowing the whole remaining distance.
            let biggestDrop = 0;
            for (let i = peakAt + 1; i < s.length; i++) biggestDrop = Math.max(biggestDrop, s[i - 1] - s[i]);
            return { peak, biggestDrop, framesAfterPeak: s.length - peakAt };
        });

        console.log(`TRUE-SCALE reversed from ${t.peak.toFixed(3)}, largest frame step ${t.biggestDrop.toFixed(4)}`);
        expect(t.peak, 'never started moving before the second tap').toBeGreaterThan(0.02);
        expect(t.peak, 'ran all the way to 1 instead of turning round').toBeLessThan(0.95);
        expect(t.biggestDrop, 'snapped back in one frame instead of easing').toBeLessThan(t.peak * 0.6);
    });

    test('bodies stay selectable and transfers still work at true scale', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tap(page.locator('#true-scale-btn'));
        await expect.poll(() => page.evaluate(() => trueScale), { timeout: 4000 }).toBe(1);

        // At true scale a moon is under a pixel across, so the 44px tap floor is
        // the only thing keeping the map playable. It has to still apply.
        const tapRadii = await page.evaluate(() =>
            bodies.map((b) => ({ name: b.name, drawn: bodyScreenRadius(b), tap: bodyTapRadius(b) })));
        for (const r of tapRadii) {
            expect(r.tap, `${r.name} has no finger-sized target`).toBeGreaterThanOrEqual(22);
        }

        await g.beginTransfer('Ember', 'Terra');
        const s = await g.state();
        expect(s.transferState === 'searching' || s.transferState === 'ready').toBe(true);
        await g.shot('true-scale-transfer');
    });
});
