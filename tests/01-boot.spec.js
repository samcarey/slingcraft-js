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

    test('canvas renders and the time scrub button is reachable', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();

        await g.expectOnScreen('#time-scrub-btn', 'time scrub button');
        await expect(page.locator('#time-scrub-btn')).toBeVisible();
        await g.shot('controls-visible');
        g.assertNoPageErrors();
    });
});
