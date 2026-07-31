const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

test.describe('collapse and reopen', () => {
    test('tapping away collapses the panel', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.openMenu();
        await expect(page.locator('#accordion-menu')).not.toHaveClass(/collapsed/);

        await g.tapElsewhere();
        await expect(page.locator('#accordion-menu')).toHaveClass(/collapsed/);
        expect(await g.isMenuExpanded()).toBe(false);
        await g.shot('collapsed-by-outside-tap');
        g.assertNoPageErrors();
    });

    test('reopening restores the origin and craft that were selected', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.selectOrigin('Ember');
        await g.shot('before-collapse');

        await g.tapElsewhere();
        await expect(page.locator('#accordion-menu')).toHaveClass(/collapsed/);

        await g.openMenu();
        // The whole point: state survives the round trip.
        expect(await page.evaluate(() => (accordionOrigin ? accordionOrigin.name : null))).toBe('Ember');
        await expect(g.originItem('Ember')).toHaveClass(/selected-origin/);
        // The squadron rides along with the origin now that the craft step is gone.
        expect(await page.evaluate(() => accordionCraft !== null)).toBe(true);
        await g.shot('after-reopen');
        g.assertNoPageErrors();
    });

    test('the toggle button closes an open panel', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.openMenu();

        await g.tap(g.toggleBtn());
        await expect(page.locator('#accordion-menu')).toHaveClass(/collapsed/);
        expect(await g.isMenuExpanded()).toBe(false);
    });

    test('tapping inside the panel does not close it', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.openMenu();

        await g.tap(g.originItem('Ember'));
        await expect(page.locator('#accordion-menu')).not.toHaveClass(/collapsed/);
        expect(await g.isMenuExpanded()).toBe(true);
        await g.shot('still-open-after-inside-tap');
    });
});

test.describe('accordion selection flow', () => {
    test('selecting an origin auto-selects its squadron and collapses the list', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.selectOrigin('Ember');
        expect(await page.evaluate(() => (accordionCraft ? accordionCraft.count : null))).toBe(5);
        // List collapses to the chosen row only.
        await expect(page.locator('#accordion-origin-list .accordion-planet-item')).toHaveCount(1);
        await expect(g.originItem('Ember')).toBeVisible();
        await g.shot('origin-selected');
        g.assertNoPageErrors();
    });

    test('destination list excludes Sol and the origin body', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.selectOrigin('Ember');
        await g.selectCraft();
        await expect(g.destItem('Terra')).toBeVisible();
        await expect(g.destItem('Sol')).toHaveCount(0);
        await expect(g.destItem('Ember')).toHaveCount(0);
        await g.shot('dest-list');
    });

    test('a body with no craft reports none and offers no squadron', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.selectOrigin('Gaia');
        await expect(page.locator('#accordion-dest-list .accordion-no-craft')).toBeVisible();
        expect(await page.evaluate(() => accordionCraft)).toBeNull();
        await g.shot('gaia-no-craft');
    });

    test('re-tapping the chosen origin reopens the full list', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.selectOrigin('Ember');
        await expect(page.locator('#accordion-origin-list .accordion-planet-item')).toHaveCount(1);

        // Re-tapping the chosen origin reopens the full list, keeping the pick.
        await g.tap(g.originItem('Ember'));
        await expect(page.locator('#accordion-origin-list .accordion-planet-item')).toHaveCount(7);
        expect(await page.evaluate(() => (accordionOrigin ? accordionOrigin.name : null))).toBe('Ember');
        await g.shot('origin-list-reopened');
        g.assertNoPageErrors();
    });

    test('switching origin mid-flow retargets cleanly', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.selectOrigin('Ember');
        await g.selectCraft();
        await g.selectOrigin('Terra');
        // Terra has no craft, so the chain must not still be holding Ember's squadron.
        expect(await page.evaluate(() => (accordionCraft ? accordionCraft.parentBody.name : null))).toBeNull();
        await g.shot('switched-origin');
        g.assertNoPageErrors();
    });
});
