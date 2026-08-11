const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

test.describe('cancel and time controls', () => {
    test('cancelling a search clears the UI and spends no craft', async ({ page }, testInfo) => {
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

    test('time scrub panel opens fully on screen', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tap(page.locator('#time-scrub-btn'));
        await page.waitForTimeout(600);
        await g.shot('time-scrub-open');

        await g.expectOnScreen('#time-scrub-panel', 'time scrub panel');
        g.assertNoPageErrors();
    });

    test('moving the viewed moment re-scans from that moment', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');

        // Opening a transfer sets the clock a little ahead of the present, so the launch
        // being chosen is one there is still time to choose — see TRANSFER_LEAD_MINUTES.
        expect(await page.evaluate(() => timeViewOffset),
            'the clock opens on the launch lead, not the present')
            .toBe(await page.evaluate(() => TRANSFER_LEAD_FRAMES));

        await g.waitForTrajectories();

        // Whatever moment the hunt above settled on, that is what the fan describes.
        const before = await g.fan();
        expect(before.launchFrame, 'the first scan launches from the moment in view')
            .toBe(await page.evaluate(() => Math.round(timeViewOffset)));

        await g.scrubToMinute(120);
        const after = await g.fan();

        // The launch moment is whatever the clock says, so the fan must follow it.
        expect(after.launchFrame, 'the fan should launch from the moment now in view')
            .toBe(Math.round(120 / 0.1));
        expect(after.scanning).toBe(false);

        console.log(`SCRUB ${before.count} routes at ${(before.launchFrame * 0.1).toFixed(1)}m ` +
            `-> ${after.count} at 120m (${Math.round(after.elapsedMs)}ms)`);
        await g.shot('rescanned-at-120m');
        g.assertNoPageErrors();
    });

    test('time simply passing does not re-scan', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        // Look at a future moment, so both counters are off zero and a drift between
        // them would actually show.
        await g.scrubToMinute(120);

        // A buffer shift moves the viewed frame and the fan's launch frame together, so
        // the fan still describes the same physical moment and must be left alone. If
        // this ever regressed, the game would re-scan on a timer while nobody touched it.
        const gen = await page.evaluate(() => fanScanGeneration);
        await page.evaluate(() => {
            // Exactly what advanceTimeline does on each tick it pops a frame.
            for (let i = 0; i < 5; i++) {
                timeViewOffset = Math.max(0, timeViewOffset - 1);
                updateFanOnShift();
            }
        });
        await page.waitForTimeout(1200);

        expect(await page.evaluate(() => fanScanGeneration),
            'a buffer shift is not a scrub and must not start a scan').toBe(gen);
        g.assertNoPageErrors();
    });
});
