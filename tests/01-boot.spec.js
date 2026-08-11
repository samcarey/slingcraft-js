const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

test.describe('boot and initial layout', () => {
    test('loads with seven bodies and a seeded squadron at Ember', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.shot('initial');

        const s = await g.state();
        expect(Object.keys(s.bodyCounts).sort()).toEqual(
            ['Aria', 'Ember', 'Gaia', 'Luna', 'Nyx', 'Sol', 'Terra'].sort()
        );
        expect(s.bodyCounts.Ember).toBe(5);
        expect(s.transferState).toBe('none');
        g.assertNoPageErrors();
    });

    test('the map starts clear, with no panel over it', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.shot('clear-at-rest');

        // Nothing selected, so nothing to show — the map is the whole interface.
        await expect(page.locator('#selected-body-info')).toBeHidden();
        await expect(page.locator('#transfer-drag-line')).toBeHidden();
    });

    test('tapping a body opens its panel fully on screen', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.tapBody('Ember');
        await g.shot('body-panel-open');

        await expect(page.locator('#selected-body-info')).toBeVisible();
        await g.expectOnScreen('#selected-body-info', 'selected body panel');
        await expect(page.locator('#craft-count-display')).toHaveText('5');
    });

    test('the opening view is the settled one — no wander while the orbits fill in', async ({ page }, testInfo) => {
        // The view is fitted to the bounding box of the predicted orbits. Built a hundred
        // frames at a time, that box grows one arc at a time for three seconds, and a box
        // growing asymmetrically is a box whose centre swings — so the map wandered back and
        // forth over its own first three seconds. The buffer is built in one go instead.
        const g = new SlingCraft(page, testInfo);
        await page.goto('/', { waitUntil: 'domcontentloaded' });
        await page.waitForFunction(() => typeof camera !== 'undefined' && bodies.length >= 7,
            null, { timeout: 30_000 });

        const trace = await page.evaluate(async () => {
            const seen = [];
            await new Promise(done => {
                const t = setInterval(() => {
                    seen.push([camera.x, camera.y, camera.zoom, predictionBuffer.length]);
                    if (seen.length >= 50) { clearInterval(t); done(); }
                }, 30);
            });
            return { seen, full: PREDICTION_FRAMES };
        });

        // The buffer is already complete the first time anything is drawn with it, so there
        // is never a frame fitted to a partial set of orbits.
        expect(trace.seen[0][3], 'the buffer should be built before the first frame')
            .toBe(trace.full);

        // Total distance travelled, not start-versus-end: a wander returns to roughly where
        // it began, so only the path length can tell it from holding still.
        let path = 0;
        let minZ = Infinity, maxZ = 0;
        for (let i = 0; i < trace.seen.length; i++) {
            const [x, y, z] = trace.seen[i];
            minZ = Math.min(minZ, z); maxZ = Math.max(maxZ, z);
            if (i) {
                const [px, py] = trace.seen[i - 1];
                path += Math.hypot(x - px, y - py) * z;   // screen px, not world units
            }
        }
        console.log(`OPENING VIEW camera travelled ${path.toFixed(1)}px over `
            + `${trace.seen.length} samples, zoom ${minZ.toFixed(4)}-${maxZ.toFixed(4)}`);

        // The bodies do orbit while this runs, so the fit target drifts a little; what must
        // not happen is the several-hundred-pixel round trip of a growing bounding box.
        expect(path, 'the opening view should not wander').toBeLessThan(8);
        expect(Math.log(maxZ / minZ), 'the opening zoom should not hunt').toBeLessThan(0.02);
        g.assertNoPageErrors();
    });

    test('canvas renders and the time scrub button is reachable', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();

        await g.expectOnScreen('#time-scrub-btn', 'time scrub button');
        await expect(page.locator('#time-scrub-btn')).toBeVisible();
        await g.shot('controls-visible');
        g.assertNoPageErrors();
    });
});
