const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

/**
 * Planning a transfer is a map gesture, not a menu: drag from a body you have
 * craft on to the body you want them at. These scenarios pin down which presses
 * become a transfer, which stay a pan, and what the player is shown mid-drag.
 */

const dragState = (page) =>
    page.evaluate(() => ({
        armed: !!transferDrag,
        target: transferDrag && transferDrag.target ? transferDrag.target.name : null,
        lineVisible: getComputedStyle(document.getElementById('transfer-drag-line')).display !== 'none',
        lit: document.querySelectorAll('.body-circle.drag-target').length,
    }));

test.describe('arming the drag', () => {
    test('holding a body selects it before the finger lifts', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        const p = await g.bodyPoint('Ember');
        await page.evaluate(({ x, y }) => {
            const svg = document.getElementById('game-svg');
            const touch = new Touch({ identifier: 1, target: svg, clientX: x, clientY: y });
            svg.dispatchEvent(new TouchEvent('touchstart', {
                touches: [touch], targetTouches: [touch], changedTouches: [touch],
                bubbles: true, cancelable: true,
            }));
        }, p);

        // Nothing yet: this is still a candidate pan.
        expect(await page.evaluate(() => selectedBody)).toBeNull();
        expect((await dragState(page)).armed).toBe(false);

        // Selection has to land while the finger is still down — that is the cue
        // telling the player the transfer drag is now live.
        await expect
            .poll(() => page.evaluate(() => (selectedBody ? selectedBody.name : null)), { timeout: 3000 })
            .toBe('Ember');
        expect((await dragState(page)).armed, 'holding a body with craft also arms the drag').toBe(true);
        await g.shot('selected-while-held');
        g.assertNoPageErrors();
    });

    test('hold, drag and release is one uninterrupted press', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        expect(await page.evaluate(() => selectedBody)).toBeNull();
        // Watch the view for the duration of the gesture itself. It cannot be checked
        // afterwards any more: releasing plans the transfer, and planning deliberately
        // takes the camera over to frame the route — so a before/after comparison would be
        // measuring that, not whether the drag slid the map.
        const before = await page.evaluate(() => {
            window.__camTrace = [];
            window.__camTimer = setInterval(
                () => window.__camTrace.push([camera.x, camera.y, camera.zoom]), 40);
            return { x: camera.x, y: camera.y, z: camera.zoom, paused: isAutoFitPaused };
        });
        await g.dragTouch(await g.bodyPoint('Ember'), await g.bodyPoint('Terra'), { holdMs: 500 });
        const gesture = await page.evaluate(() => {
            clearInterval(window.__camTimer);
            return { trace: window.__camTrace, paused: isAutoFitPaused };
        });

        await expect.poll(() => page.evaluate(() => transferState)).toMatch(/searching|ready/);
        expect(await page.evaluate(() => transferSourceBody.name)).toBe('Ember');
        expect(await page.evaluate(() => transferDestinationBody.name)).toBe('Terra');
        // The whole fleet goes by default; the slider trims it afterwards.
        await g.waitForTrajectories();
        const slider = await g.sliderInfo();
        expect(slider.max, 'every craft at Ember is on offer').toBe(5);
        expect(slider.value, 'and all of them are selected to start with').toBe(5);
        // And it must not have slid the map on the way.
        expect(gesture.trace.length, 'the gesture should have been sampled').toBeGreaterThan(4);
        for (const [x, y, z] of gesture.trace) {
            const panned = Math.hypot(x - before.x, y - before.y) * z;
            expect(panned, 'a transfer drag must not pan the view').toBeLessThan(1);
        }
        // A pan hands the view to the player for good; a transfer drag never does.
        expect(gesture.paused, 'a transfer drag is not a pan').toBe(before.paused);
        await g.shot('transfer-planned-by-hold-drag');
        g.assertNoPageErrors();
    });

    test('once selected, a drag off it needs no second hold', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tapBody('Ember');
        await g.dragTouch(await g.bodyPoint('Ember'), await g.bodyPoint('Gaia'));

        await expect.poll(() => page.evaluate(() => transferState)).toMatch(/searching|ready/);
        expect(await page.evaluate(() => transferDestinationBody.name)).toBe('Gaia');
        g.assertNoPageErrors();
    });

    test('a quick drag off an unselected body pans', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        // Ember has craft, but it is not selected and the finger never waits, so
        // this is a pan like any other.
        expect(await page.evaluate(() => selectedBody)).toBeNull();
        const before = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const p = await g.bodyPoint('Ember');
        await g.dragTouch(p, { x: p.x + 110, y: p.y + 60 });

        const after = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const panned = Math.hypot(after.x - before.x, after.y - before.y) * after.z;
        expect(panned, 'an unselected body is not a transfer handle').toBeGreaterThan(40);
        expect(await page.evaluate(() => transferState)).toBe('none');
        await g.shot('quick-drag-off-body-pans');
        g.assertNoPageErrors();
    });

    test('a selected body with no craft pans instead of transferring', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        expect(await g.craftAt('Gaia')).toBe(0);
        await g.tapBody('Gaia');
        const before = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const p = await g.bodyPoint('Gaia');
        await g.dragTouch(p, { x: p.x + 110, y: p.y + 60 });

        const after = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const panned = Math.hypot(after.x - before.x, after.y - before.y) * after.z;
        expect(panned, 'nothing to send, so the drag is a pan').toBeGreaterThan(40);
        expect(await page.evaluate(() => transferState)).toBe('none');
        await g.shot('drag-off-empty-body-pans');
        g.assertNoPageErrors();
    });

    test('a hold that starts moving early stays a pan', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        const p = await g.bodyPoint('Ember');
        // Move off well before the hold could elapse, then keep the finger down
        // past it. The hold must have been cancelled, not merely deferred.
        const armed = await page.evaluate(async ({ x, y }) => {
            const svg = document.getElementById('game-svg');
            const mk = (type, cx, cy) => {
                const touch = new Touch({ identifier: 1, target: svg, clientX: cx, clientY: cy });
                const list = type === 'touchend' ? [] : [touch];
                return new TouchEvent(type, {
                    touches: list, targetTouches: list, changedTouches: [touch],
                    bubbles: true, cancelable: true,
                });
            };
            const wait = (ms) => new Promise((r) => setTimeout(r, ms));
            svg.dispatchEvent(mk('touchstart', x, y));
            for (let i = 1; i <= 5; i++) { svg.dispatchEvent(mk('touchmove', x + i * 12, y)); await wait(10); }
            await wait(700);
            const state = { armed: !!transferDrag, sel: selectedBody ? selectedBody.name : null };
            svg.dispatchEvent(mk('touchend', x + 60, y));
            await wait(200);
            return state;
        }, p);

        expect(armed.armed, 'a hold cancelled by movement must not fire later').toBe(false);
        expect(armed.sel).toBeNull();
        expect(await page.evaluate(() => transferState)).toBe('none');
        g.assertNoPageErrors();
    });

    test('a drag from open sky still pans', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        const before = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const vp = page.viewportSize();
        const from = { x: Math.round(vp.width * 0.5), y: Math.round(vp.height * 0.22) };
        // Confirm we really are starting on nothing.
        expect(await page.evaluate(({ x, y }) => {
            const r = document.getElementById('game-svg').getBoundingClientRect();
            return !!findBodyAtPosition(x - r.left, y - r.top);
        }, from)).toBe(false);

        await g.dragTouch(from, { x: from.x + 120, y: from.y + 70 });
        const after = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const panned = Math.hypot(after.x - before.x, after.y - before.y) * after.z;
        expect(panned, 'open sky is still how you move the view').toBeGreaterThan(40);
        expect(await page.evaluate(() => transferState)).toBe('none');
        g.assertNoPageErrors();
    });
});

test.describe('what the drag shows and where it may land', () => {
    test('the rubber band tracks the finger and lights up a valid destination', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tapBody('Ember');
        const from = await g.bodyPoint('Ember');
        const to = await g.bodyPoint('Terra');

        // Stop the drag on the destination without releasing, to inspect the
        // feedback the player is looking at while deciding.
        await page.evaluate(async ({ sx, sy, dx, dy }) => {
            const svg = document.getElementById('game-svg');
            const mk = (type, cx, cy) => {
                const touch = new Touch({ identifier: 1, target: svg, clientX: cx, clientY: cy });
                const list = type === 'touchend' ? [] : [touch];
                return new TouchEvent(type, {
                    touches: list, targetTouches: list, changedTouches: [touch],
                    bubbles: true, cancelable: true,
                });
            };
            svg.dispatchEvent(mk('touchstart', sx, sy));
            for (let i = 1; i <= 10; i++) {
                svg.dispatchEvent(mk('touchmove', sx + ((dx - sx) * i) / 10, sy + ((dy - sy) * i) / 10));
                await new Promise((r) => setTimeout(r, 16));
            }
        }, { sx: from.x, sy: from.y, dx: to.x, dy: to.y });

        const mid = await dragState(page);
        expect(mid.armed).toBe(true);
        expect(mid.lineVisible, 'rubber band should be drawn mid-drag').toBe(true);
        expect(mid.target).toBe('Terra');
        expect(mid.lit, 'exactly one body highlighted as the destination').toBe(1);
        await g.shot('mid-drag-over-destination');

        await expect(page.locator('#transfer-drag-line')).toHaveClass(/locked/);
        g.assertNoPageErrors();
    });

    test('releasing over empty space cancels without panning or deselecting', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tapBody('Ember');
        const before = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const vp = page.viewportSize();
        await g.dragTouch(await g.bodyPoint('Ember'), { x: 8, y: Math.round(vp.height * 0.5) });

        expect(await page.evaluate(() => transferState)).toBe('none');
        // Still selected, so the player can simply try again.
        expect(await page.evaluate(() => selectedBody.name)).toBe('Ember');
        const after = await page.evaluate(() => ({ x: camera.x, y: camera.y, z: camera.zoom }));
        const moved = Math.hypot(after.x - before.x, after.y - before.y) * after.z;
        expect(moved, 'a cancelled transfer drag must not have panned the view').toBeLessThan(1);
        await expect(page.locator('#transfer-drag-line')).toBeHidden();
        g.assertNoPageErrors();
    });

    test('the star is not a destination', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tapBody('Ember');
        await g.dragTouch(await g.bodyPoint('Ember'), await g.bodyPoint('Sol'));

        expect(await page.evaluate(() => transferState)).toBe('none');
        g.assertNoPageErrors();
    });

    test('a body cannot be its own destination', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.tapBody('Ember');
        const p = await g.bodyPoint('Ember');
        // A single gesture that swings well clear of Ember and comes back to it,
        // releasing on the source. Dropping a body on itself is not a transfer.
        const target = await page.evaluate(async ({ x, y }) => {
            const svg = document.getElementById('game-svg');
            const mk = (type, cx, cy) => {
                const touch = new Touch({ identifier: 1, target: svg, clientX: cx, clientY: cy });
                const list = type === 'touchend' ? [] : [touch];
                return new TouchEvent(type, {
                    touches: list, targetTouches: list, changedTouches: [touch],
                    bubbles: true, cancelable: true,
                });
            };
            const wait = (ms) => new Promise((r) => setTimeout(r, ms));
            svg.dispatchEvent(mk('touchstart', x, y));
            for (const dy of [-40, -90, -140, -90, -40, 0]) {
                svg.dispatchEvent(mk('touchmove', x, y + dy));
                await wait(16);
            }
            const back = transferDrag && transferDrag.target ? transferDrag.target.name : null;
            svg.dispatchEvent(mk('touchend', x, y));
            await wait(300);
            return back;
        }, p);

        expect(target, 'the source must never register as its own destination').toBeNull();
        expect(await page.evaluate(() => transferState)).toBe('none');
        g.assertNoPageErrors();
    });
});

test.describe('the selected-body panel', () => {
    test('selecting a body shows its panel and teaches the gesture', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await expect(page.locator('#selected-body-info')).toBeHidden();

        await g.tapBody('Ember');
        await expect(page.locator('#selected-body-info')).toBeVisible();
        await expect(page.locator('#transfer-hint')).toHaveText(/drag/i);
        await expect(page.locator('#build-craft-btn')).toBeVisible();
        await g.expectOnScreen('#selected-body-info', 'selected body panel');
        await g.shot('body-panel');

        await g.tapElsewhere();
        await expect(page.locator('#selected-body-info')).toBeHidden();
        g.assertNoPageErrors();
    });

    test('the old origin/destination menu is gone', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();

        await expect(page.locator('#accordion-menu')).toHaveCount(0);
        await expect(page.locator('#accordion-toggle-btn')).toHaveCount(0);
        // And no leftover destination picker on the body panel either.
        await g.tapBody('Ember');
        await expect(page.locator('#transfer-btn')).toHaveCount(0);
        g.assertNoPageErrors();
    });

    test('craft built from the panel can then be sent by dragging', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        expect(await g.craftAt('Terra')).toBe(0);
        await g.buildCraftAt('Terra');
        await expect.poll(() => g.craftAt('Terra')).toBeGreaterThan(0);

        await g.dragTouch(await g.bodyPoint('Terra'), await g.bodyPoint('Gaia'));
        await expect.poll(() => page.evaluate(() => transferState)).toMatch(/searching|ready/);
        expect(await page.evaluate(() => transferSourceBody.name)).toBe('Terra');
        g.assertNoPageErrors();
    });
});
