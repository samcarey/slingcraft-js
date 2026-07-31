const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

test.describe('multiple and chained transfers', () => {
    test('two concurrent transfers to different destinations coexist', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.tapSliderTo(2);
        await g.scheduleLaunch();
        await page.waitForTimeout(600);

        await g.beginTransfer('Ember', 'Gaia');
        await g.waitForTrajectories();
        await g.tapSliderTo(2);
        await g.scheduleLaunch();
        await page.waitForTimeout(600);

        const s = await g.state();
        const free = s.squadrons.filter((q) => q.state === 'free');
        expect(free.length).toBe(2);
        expect(free.map((q) => q.dest).sort()).toEqual(['Gaia', 'Terra']);
        expect(s.bodyCounts.Ember).toBe(1);
        await g.shot('two-in-flight');
        g.assertNoPageErrors();
    });

    test('every transit squadron carries a source and destination', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Luna');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(800);

        const s = await g.state();
        const free = s.squadrons.filter((q) => q.state === 'free');
        expect(free.length).toBe(1);
        // Regression guard: "From field showing Unknown" was a real past bug.
        expect(free[0].source).toBe('Ember');
        expect(free[0].dest).toBe('Luna');
        await g.shot('transit-endpoints');
    });

    test('transit squadrons render with a resolved colour, not undefined', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(1000);

        // Past bug: "invisible squadron trajectories caused by undefined color".
        // Squadron carries no `color` field — the path is styled by class, so
        // assert on what actually renders.
        const paths = await page.evaluate(() =>
            squadrons
                .filter((s) => s.state === 'free' && s.trajectoryPath)
                .map((s) => {
                    const cs = getComputedStyle(s.trajectoryPath);
                    return { stroke: cs.stroke, opacity: Number(cs.opacity), hasD: !!s.trajectoryPath.getAttribute('d') };
                })
        );
        expect(paths.length, 'in-flight squadron should have a trajectory path').toBeGreaterThan(0);
        for (const p of paths) {
            expect(p.stroke, `trajectory stroke unresolved: ${JSON.stringify(p)}`).not.toMatch(/undefined|none|^$/);
            expect(p.opacity, 'trajectory drawn fully transparent').toBeGreaterThan(0);
            expect(p.hasD, 'trajectory path has no geometry').toBe(true);
        }
        await g.shot('transit-colored');
        g.assertNoPageErrors();
    });

    test('craft are conserved across repeated partial sends', async ({ page }, testInfo) => {
        // Three sequential searches, each with its own propagation wait.
        test.setTimeout(300_000);
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        const total = () =>
            page.evaluate(() => squadrons.reduce((n, s) => n + s.count, 0));
        expect(await total()).toBe(5);

        // Scheduling a transfer must never mint craft, however many times the
        // same origin is drawn from.
        for (const dest of ['Terra', 'Gaia', 'Nyx']) {
            const before = await total();
            await g.beginTransfer('Ember', dest);
            await g.waitForTrajectories();
            const max = (await g.sliderInfo()).max;
            expect(max, `slider offered ${max} but only ${await g.craftAt('Ember')} orbit Ember`).toBeLessThanOrEqual(
                await g.craftAt('Ember')
            );
            await g.tapSliderTo(1);
            await g.scheduleLaunch();
            await page.waitForTimeout(700);
            expect(await total(), `fleet grew after sending to ${dest}`).toBe(before);
        }
        await g.shot('conservation');
        g.assertNoPageErrors();
    });

    test('origin drained to zero cannot start another transfer', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch(); // all five
        await page.waitForTimeout(800);
        expect(await g.craftAt('Ember')).toBe(0);

        await g.selectOrigin('Ember');
        // With nothing in orbit the craft step must say so rather than offering
        // a squadron that cannot be sent.
        await expect(page.locator('#accordion-dest-list .accordion-no-craft')).toBeVisible();
        await g.shot('drained-origin');
        g.assertNoPageErrors();
    });
});
