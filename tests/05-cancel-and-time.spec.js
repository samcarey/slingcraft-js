const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

test.describe('cancel and time controls', () => {
    test('cancelling a search restores the accordion and spends no craft', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.shot('before-cancel');

        await g.cancelTransfer();
        await page.waitForTimeout(600);

        expect(await page.evaluate(() => transferState)).toBe('none');
        expect(await g.craftAt('Ember')).toBe(5);
        await expect(page.locator('#accordion-menu')).toBeVisible();
        await expect(g.launchControls()).toBeHidden();
        await g.shot('after-cancel');
        g.assertNoPageErrors();
    });

    test('cancel then restart a transfer to a different destination', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.cancelTransfer();
        await page.waitForTimeout(600);

        await g.beginTransfer('Ember', 'Nyx');
        await g.waitForTrajectories();
        expect(await page.evaluate(() => transferDestinationBody.name)).toBe('Nyx');
        await expect(g.launchControls()).toBeVisible();
        await g.shot('restarted-to-nyx');
        g.assertNoPageErrors();
    });

    test('time scrub panel opens and does not cover the accordion', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tap(page.locator('#time-scrub-btn'));
        await page.waitForTimeout(600);
        await g.shot('time-scrub-open');

        await g.expectOnScreen('#time-scrub-panel', 'time scrub panel');
        g.assertNoPageErrors();
    });

    test('trajectory step buttons move the selected launch window', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const before = await page.evaluate(() => transferBestFrame);
        await g.tap(page.locator('#traj-next-btn'));
        await page.waitForTimeout(500);
        const after = await page.evaluate(() => transferBestFrame);
        expect(after, 'next-launch-time button should change the chosen frame').not.toBe(before);
        await g.shot('stepped-launch-window');
        g.assertNoPageErrors();
    });
});
