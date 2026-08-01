const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

/**
 * The reported regression: "I did work to allow sending only part of a
 * squadron. Now I can't." These tests pin the behaviour end to end.
 */
test.describe('partial squadron transfer', () => {
    test('quantity slider is visible and stays visible once trajectories exist', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        await expect(g.launchControls()).toBeVisible();
        await g.shot('slider-visible');

        // The complaint was that it appeared then vanished. Hold and re-check.
        for (let i = 0; i < 5; i++) {
            await page.waitForTimeout(1000);
            const info = await g.sliderInfo();
            expect(info.wrapVisible, `slider vanished at t+${i + 1}s: ${JSON.stringify(info)}`).toBe(true);
        }
        await g.shot('slider-still-visible-5s');
        expect(g.sliderHiddenLogs()).toEqual([]);
        g.assertNoPageErrors();
    });

    test('slider max equals available craft and defaults to sending all', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const info = await g.sliderInfo();
        expect(info.max).toBe(5);
        // Defaulting to max is why a player who never notices the slider
        // always sends the entire squadron.
        expect(info.value).toBe(5);
        expect(info.stayLabel).toBe('0');
        expect(info.launchLabel).toBe('5');
    });

    test('tapping the track to 2 sends 2 and leaves 3 behind', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        await g.tapSliderTo(2);
        const info = await g.sliderInfo();
        expect(info.value).toBe(2);
        expect(info.stayLabel).toBe('3');
        expect(info.launchLabel).toBe('2');
        await g.shot('slider-set-to-2');

        await g.scheduleLaunch();
        await page.waitForTimeout(800);

        const s = await g.state();
        expect(s.bodyCounts.Ember, `Ember should retain 3: ${JSON.stringify(s)}`).toBe(3);
        const transit = s.squadrons.filter((q) => q.count > 0);
        expect(transit.length).toBe(1);
        expect(transit[0].count).toBe(2);
        expect(transit[0].dest).toBe('Terra');
        await g.shot('after-partial-launch');
        g.assertNoPageErrors();
    });

    test('slider survives the candidate list momentarily emptying', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await expect(g.launchControls()).toBeVisible();

        // Force the condition that used to hide the panel mid-search: the fan is
        // emptied and rebuilt from scratch every time the viewed moment changes.
        await page.evaluate(() => {
            transferState = 'searching';
            transferFan = [];
            fanHighlight = -1;
            fanScanPending = 1;      // pretend a scan is in flight
        });
        await page.waitForTimeout(900);

        // The regression being guarded is the panel disappearing. Read both facts in
        // one go: a live re-scan can refill the fan on its own, so Launch may
        // legitimately have re-enabled by the time we look.
        const [info, stillEmpty] = await Promise.all([
            g.sliderInfo(),
            page.evaluate(() => transferFan.length === 0),
        ]);
        expect(info.wrapVisible, `panel vanished when candidates emptied: ${JSON.stringify(info)}`).toBe(true);
        if (stillEmpty) {
            expect(info.scheduleDisabled, 'Launch should be blocked while there is no candidate').toBe(true);
        }
        await g.shot('survives-empty-candidates');
        g.assertNoPageErrors();
    });

    test('quantity 0 disables Launch', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        await g.setSlider(0);
        await page.waitForTimeout(300);
        await expect(page.locator('#schedule-launch-btn')).toBeDisabled();
        await g.shot('zero-disables-launch');
    });

    test('sending every craft empties the origin', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        await g.scheduleLaunch(); // default is max
        await page.waitForTimeout(800);

        const s = await g.state();
        expect(s.bodyCounts.Ember).toBe(0);
        expect(s.squadrons.filter((q) => q.count > 0)[0].count).toBe(5);
        await g.shot('sent-all');
    });

    test('two successive partial sends split one squadron three ways', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.tapSliderTo(2);
        await g.scheduleLaunch();
        await page.waitForTimeout(800);
        expect(await g.craftAt('Ember')).toBe(3);
        await g.shot('first-partial');

        await g.beginTransfer('Ember', 'Gaia');
        await g.waitForTrajectories();
        const info = await g.sliderInfo();
        expect(info.max, `second send should cap at the 3 remaining: ${JSON.stringify(info)}`).toBe(3);
        await g.tapSliderTo(1);
        await g.scheduleLaunch();
        await page.waitForTimeout(800);

        const s = await g.state();
        expect(s.bodyCounts.Ember).toBe(2);
        const inFlight = s.squadrons.filter((q) => q.count > 0);
        expect(inFlight.map((q) => q.count).sort()).toEqual([1, 2]);
        await g.shot('two-partials-done');
        g.assertNoPageErrors();
    });
});
