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

    test('the panel rests collapsed behind the lower-left button', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.shot('collapsed-at-rest');

        await expect(page.locator('#accordion-toggle-btn')).toBeVisible();
        await g.expectOnScreen('#accordion-toggle-btn', 'accordion toggle button');
        await expect(page.locator('#accordion-menu')).toHaveClass(/collapsed/);
        expect(await g.isMenuExpanded()).toBe(false);
    });

    test('the button opens the panel fully on screen', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.openMenu();
        await g.shot('expanded-from-button');

        await expect(page.locator('#accordion-menu')).toBeVisible();
        await g.expectOnScreen('#accordion-menu', 'expanded accordion menu');
        await g.expectNoOverlap('#accordion-menu', '#accordion-toggle-btn', 'panel vs its own button');
    });

    test('origin list shows every body with a craft badge on Ember', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.openMenu();

        await expect(g.originItem('Ember')).toBeVisible();
        await expect(g.originItem('Ember').locator('.accordion-craft-badge')).toHaveText('5');
        // Bodies with no craft should carry no badge.
        await expect(g.originItem('Terra').locator('.accordion-craft-badge')).toHaveCount(0);
        await g.shot('origin-list');
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
