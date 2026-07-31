const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

/**
 * Layout audit: nothing overlapping, nothing off screen, nothing that is
 * present in the DOM but unreachable by a finger.
 */
test.describe('layout and reachability on a phone', () => {
    test('the two corner buttons do not overlap at rest', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.shot('rest-layout');
        await g.expectNoOverlap('#accordion-toggle-btn', '#time-scrub-btn', 'panel button vs time scrub button');
        await g.expectOnScreen('#accordion-toggle-btn', 'panel button');
    });

    test('the open panel clears both corner buttons', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.openMenu();
        await g.shot('open-panel-layout');
        await g.expectNoOverlap('#accordion-menu', '#accordion-toggle-btn', 'panel vs its button');
        await g.expectNoOverlap('#accordion-menu', '#time-scrub-btn', 'panel vs time scrub button');
    });

    test('open panel fits within the viewport with a squadron expanded', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.selectOrigin('Ember');
        await page.waitForTimeout(700);
        await g.shot('expanded-accordion');

        await g.expectOnScreen('#accordion-menu', 'expanded accordion');
    });

    test('transfer panel, plot and scrub button do not overlap during a transfer', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.shot('transfer-layout');

        await g.expectNoOverlap('#transfer-controls-panel', '#trajectory-plot-container', 'transfer panel vs plot');
        await g.expectNoOverlap('#transfer-controls-panel', '#time-scrub-btn', 'transfer panel vs scrub button');
        await g.expectOnScreen('#transfer-controls-panel', 'transfer controls panel');
        await g.expectOnScreen('#trajectory-plot-container', 'trajectory plot');
    });

    test('accordion is hidden while a transfer is in progress, not stacked underneath', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        // Both live at bottom:20px/left:20px, so the accordion must actually be
        // hidden rather than merely painted behind the transfer panel.
        const accordionHidden = await page.evaluate(() => {
            const m = document.getElementById('accordion-menu');
            const cs = getComputedStyle(m);
            return { opacity: Number(cs.opacity), pointerEvents: cs.pointerEvents, hasClass: m.classList.contains('hidden-menu') };
        });
        expect(accordionHidden.hasClass).toBe(true);
        expect(accordionHidden.opacity).toBeLessThan(0.05);
        expect(accordionHidden.pointerEvents).toBe('none');
        await g.shot('accordion-hidden-during-transfer');
    });

    test('the launch controls are tappable, not covered by another element', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        // Hit-test the real centres: whatever is on top must belong to the control.
        const hits = await page.evaluate(() => {
            const check = (sel) => {
                const el = document.querySelector(sel);
                const r = el.getBoundingClientRect();
                const top = document.elementFromPoint(r.x + r.width / 2, r.y + r.height / 2);
                return { sel, reachable: !!(top && (top === el || el.contains(top))), topTag: top ? `${top.tagName}#${top.id}` : null };
            };
            return [check('#transfer-qty-slider'), check('#schedule-launch-btn'), check('#cancel-transfer-btn')];
        });
        for (const h of hits) {
            expect(h.reachable, `${h.sel} is covered by ${h.topTag}`).toBe(true);
        }
        await g.shot('controls-hit-tested');
    });

    test('no panel content spills outside its own container', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.shot('overflow-check');

        // Overlap assertions compare sibling panels and cannot see a child
        // spilling past its parent's edges — which is how the trajectory
        // readout got clipped on a 320px screen.
        const spills = await page.evaluate(() => {
            const out = [];
            for (const sel of ['#trajectory-info-bar', '#transfer-launch-controls', '#trajectory-controls']) {
                const el = document.querySelector(sel);
                if (!el || el.offsetParent === null) continue;
                const overflowX = el.scrollWidth - el.clientWidth;
                const r = el.getBoundingClientRect();
                if (overflowX > 1 || r.left < -1 || r.right > window.innerWidth + 1) {
                    out.push({ sel, overflowX, left: Math.round(r.left), right: Math.round(r.right), vw: window.innerWidth });
                }
            }
            return out;
        });
        expect(spills, `content overflows its container: ${JSON.stringify(spills)}`).toEqual([]);
    });

    test('the quantity slider is wide enough to pick each value', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        const box = await page.locator('#transfer-qty-slider').boundingBox();
        const max = Number(await page.locator('#transfer-qty-slider').getAttribute('max'));
        const perStep = box.width / max;
        console.log(`LAYOUT slider width ${box.width}px, ${max} steps, ${perStep.toFixed(1)}px per step`);
        // Apple's minimum comfortable touch target is 44px; a slider step much
        // below that makes exact selection a coin flip.
        expect(perStep, `only ${perStep.toFixed(1)}px per step — too fine for a finger`).toBeGreaterThanOrEqual(28);
    });
});
