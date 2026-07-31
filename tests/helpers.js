const fs = require('fs');
const path = require('path');
const { expect } = require('@playwright/test');

const SHOT_DIR =
    process.env.SLINGCRAFT_SHOTS ||
    '/private/tmp/claude-501/-Users-sccarey-slingcraft-js/415a93ce-a64f-4307-9df4-df8194e15a4d/scratchpad/shots';

fs.mkdirSync(SHOT_DIR, { recursive: true });

/**
 * Page object for driving SlingCraft through its real UI.
 *
 * game.js is a classic script, so its top-level `let` bindings (bodies,
 * squadrons, transferState, ...) are global lexical bindings. They are NOT
 * properties of window, but bare references inside page.evaluate() resolve
 * against the global scope, which is how state is read here.
 */
class SlingCraft {
    constructor(page, testInfo) {
        this.page = page;
        this.testInfo = testInfo;
        this.consoleLines = [];
        this.pageErrors = [];
        this._shotSeq = 0;

        page.on('console', (msg) => {
            this.consoleLines.push(`[${msg.type()}] ${msg.text()}`);
        });
        page.on('pageerror', (err) => {
            this.pageErrors.push(String(err));
        });
    }

    slug() {
        return this.testInfo.title.replace(/[^a-z0-9]+/gi, '-').toLowerCase().slice(0, 60);
    }

    /** Save a debug screenshot; returns its absolute path. */
    async shot(label) {
        const seq = String(++this._shotSeq).padStart(2, '0');
        const project = this.testInfo.project.name;
        const file = path.join(SHOT_DIR, `${project}__${this.slug()}__${seq}-${label}.png`);
        await this.page.screenshot({ path: file, fullPage: false });
        return file;
    }

    async boot() {
        await this.page.goto('/', { waitUntil: 'domcontentloaded' });
        // Bodies exist once init() has run.
        await this.page.waitForFunction(() => typeof bodies !== 'undefined' && bodies.length >= 7, null, {
            timeout: 30_000,
        });
        return this;
    }

    /** Transfers require a fully propagated prediction buffer. */
    async waitForPropagation() {
        await this.page.waitForFunction(
            () => predictionBuffer.length >= PREDICTION_FRAMES,
            null,
            { timeout: 180_000, polling: 250 }
        );
    }

    async propagationPercent() {
        return this.page.evaluate(() =>
            Math.round((predictionBuffer.length / PREDICTION_FRAMES) * 100)
        );
    }

    // ---- state readers -------------------------------------------------

    async state() {
        return this.page.evaluate(() => ({
            transferState,
            timeViewOffset,
            squadrons: squadrons.map((s) => ({
                state: s.state,
                count: s.count,
                parent: s.parentBody ? s.parentBody.name : null,
                source: s.sourceBody ? s.sourceBody.name : null,
                dest: s.destinationBody ? s.destinationBody.name : null,
                launchFrame: s.launchFrame,
            })),
            bodyCounts: Object.fromEntries(
                bodies.map((b) => {
                    const sq = squadrons.find((s) => s.state === 'orbiting' && s.parentBody === b);
                    return [b.name, sq ? sq.count : 0];
                })
            ),
        }));
    }

    async craftAt(bodyName) {
        return (await this.state()).bodyCounts[bodyName] ?? 0;
    }

    // ---- accordion flow ------------------------------------------------

    originItem(name) {
        return this.page.locator(`#accordion-origin-list .accordion-planet-item[data-body-name="${name}"]`);
    }

    destItem(name) {
        return this.page.locator(`#accordion-dest-list .accordion-dest-item[data-body-name="${name}"]`);
    }

    craftItem() {
        return this.page.locator('#accordion-craft-list .accordion-craft-item');
    }

    /**
     * All interaction goes through touch, matching how the game is actually
     * played. tap() requires hasTouch, which every project sets.
     */
    async tap(locator) {
        await expect(locator).toBeVisible();
        await locator.tap();
    }

    toggleBtn() {
        return this.page.locator('#accordion-toggle-btn');
    }

    async isMenuExpanded() {
        return this.page.evaluate(() => accordionExpanded === true);
    }

    /** Idempotent: the panel rests collapsed behind the lower-left button. */
    async openMenu() {
        if (await this.isMenuExpanded()) return;
        await this.tap(this.toggleBtn());
        await expect(this.page.locator('#accordion-menu')).not.toHaveClass(/collapsed/);
    }

    /**
     * Tap the star field. The panel occupies left:20 to right:80 and most of the
     * height when the body list is open, so the only reliably-outside area is
     * the strip down the right edge — kept clear of the scrub button at the
     * bottom and the controls popover at the top.
     */
    async tapElsewhere() {
        const vp = this.page.viewportSize();
        const x = vp.width - 24;
        const y = Math.round(vp.height * 0.5);
        await this.page.touchscreen.tap(x, y);
        // Verify we actually missed the panel, rather than silently selecting in it.
        const hit = await this.page.evaluate(([px, py]) => {
            const el = document.elementFromPoint(px, py);
            return !!(el && el.closest('#accordion-menu'));
        }, [x, y]);
        expect(hit, `tapElsewhere(${x},${y}) landed inside the panel`).toBe(false);
    }

    async selectOrigin(name) {
        await this.openMenu();
        // Picking an origin collapses the list to that one row, so reaching a
        // different body means reopening the list first.
        if ((await this.originItem(name).count()) === 0) {
            const current = await this.page.evaluate(() =>
                accordionOrigin ? accordionOrigin.name : null
            );
            if (current) await this.tap(this.originItem(current));
        }
        await this.tap(this.originItem(name));
        await expect(this.originItem(name)).toHaveClass(/selected-origin/);
    }

    /**
     * There is no craft step any more — one squadron per body means selecting
     * an origin auto-selects it. Kept as a no-op assertion so the scenarios
     * still state the expectation explicitly.
     */
    async selectCraft() {
        await this.page.waitForFunction(() => accordionCraft !== null, null, { timeout: 10_000 });
    }

    /** Selecting a destination auto-starts the transfer search. */
    async selectDest(name) {
        await this.tap(this.destItem(name));
    }

    /** Full origin -> craft -> dest chain, leaving the sim searching. */
    async beginTransfer(origin, dest) {
        await this.selectOrigin(origin);
        await this.selectCraft();
        await this.selectDest(dest);
        await this.page.waitForFunction(
            () => transferState === 'searching' || transferState === 'ready',
            null,
            { timeout: 20_000 }
        );
    }

    /** Wait until the search has produced at least one usable trajectory. */
    async waitForTrajectories() {
        await this.page.waitForFunction(
            () => acceptableTrajectories.length > 0 && initialSearchComplete,
            null,
            { timeout: 180_000, polling: 250 }
        );
    }

    // ---- quantity slider -----------------------------------------------

    slider() {
        return this.page.locator('#transfer-qty-slider');
    }

    launchControls() {
        return this.page.locator('#transfer-launch-controls');
    }

    async sliderInfo() {
        return this.page.evaluate(() => {
            const el = document.getElementById('transfer-qty-slider');
            const wrap = document.getElementById('transfer-launch-controls');
            const panel = document.getElementById('transfer-controls-panel');
            const cs = wrap ? getComputedStyle(wrap) : null;
            return {
                exists: !!el,
                value: el ? Number(el.value) : null,
                max: el ? Number(el.max) : null,
                wrapDisplay: cs ? cs.display : null,
                wrapVisible: !!(wrap && wrap.offsetParent !== null),
                panelDisplay: panel ? getComputedStyle(panel).display : null,
                stayLabel: document.getElementById('transfer-stay-label')?.textContent,
                launchLabel: document.getElementById('transfer-launch-label')?.textContent,
                scheduleDisabled: document.getElementById('schedule-launch-btn')?.disabled,
            };
        });
    }

    /**
     * Set the quantity with a real finger tap on the track — the gesture a
     * player actually uses. Falls back to nudging if the tap lands off by one,
     * because the track is narrow enough that a step is only ~25px.
     */
    async tapSliderTo(target) {
        const box = await this.slider().boundingBox();
        const max = Number(await this.slider().getAttribute('max'));
        for (let attempt = 0; attempt < 4; attempt++) {
            const current = Number(await this.slider().inputValue());
            if (current === target) return current;
            const frac = Math.min(1, Math.max(0, target / max));
            const x = box.x + Math.min(box.width - 1, Math.max(1, box.width * frac));
            await this.page.touchscreen.tap(x, box.y + box.height / 2);
            await this.page.waitForTimeout(120);
        }
        const final = Number(await this.slider().inputValue());
        expect(final, `could not tap slider to ${target} (max ${max}, width ${box.width}px)`).toBe(target);
        return final;
    }

    /** Programmatic setter for cases where the exact value matters more than the gesture. */
    async setSlider(value) {
        await this.slider().evaluate((el, v) => {
            el.value = String(v);
            el.dispatchEvent(new Event('input', { bubbles: true }));
            el.dispatchEvent(new Event('change', { bubbles: true }));
        }, value);
    }

    async scheduleLaunch() {
        const btn = this.page.locator('#schedule-launch-btn');
        await expect(btn).toBeEnabled();
        await this.tap(btn);
    }

    async cancelTransfer() {
        await this.tap(this.page.locator('#cancel-transfer-btn'));
    }

    // ---- misc UI -------------------------------------------------------

    async buildCraftAt(bodyName) {
        // Build lives in the selected-body info panel, reached by clicking the
        // body in the accordion origin list.
        await this.selectOrigin(bodyName);
        const before = await this.craftAt(bodyName);
        await this.page.evaluate((n) => {
            selectedBody = bodies.find((b) => b.name === n);
        }, bodyName);
        return before;
    }

    /**
     * Assert two elements do not overlap. Both must be visible; a hidden
     * element trivially "doesn't overlap" and would mask a real regression.
     */
    async expectNoOverlap(selA, selB, label) {
        const boxes = await this.page.evaluate(
            ([a, b]) => {
                const rect = (sel) => {
                    const el = document.querySelector(sel);
                    if (!el) return null;
                    const cs = getComputedStyle(el);
                    const visible =
                        cs.display !== 'none' &&
                        cs.visibility !== 'hidden' &&
                        Number(cs.opacity) > 0.01 &&
                        el.offsetParent !== null;
                    const r = el.getBoundingClientRect();
                    return { visible, x: r.x, y: r.y, w: r.width, h: r.height };
                };
                return [rect(a), rect(b)];
            },
            [selA, selB]
        );
        const [ra, rb] = boxes;
        if (!ra || !rb || !ra.visible || !rb.visible) return { skipped: true, ra, rb };

        const overlapW = Math.max(0, Math.min(ra.x + ra.w, rb.x + rb.w) - Math.max(ra.x, rb.x));
        const overlapH = Math.max(0, Math.min(ra.y + ra.h, rb.y + rb.h) - Math.max(ra.y, rb.y));
        const area = overlapW * overlapH;
        expect(area, `${label || `${selA} overlaps ${selB}`} — overlap ${overlapW}x${overlapH}px`).toBe(0);
        return { skipped: false, area };
    }

    /** Every visible interactive control must sit inside the viewport. */
    async expectOnScreen(selector, label) {
        const info = await this.page.evaluate((sel) => {
            const el = document.querySelector(sel);
            if (!el) return { missing: true };
            const cs = getComputedStyle(el);
            if (cs.display === 'none' || el.offsetParent === null) return { hidden: true };
            const r = el.getBoundingClientRect();
            return {
                x: r.x, y: r.y, w: r.width, h: r.height,
                vw: window.innerWidth, vh: window.innerHeight,
            };
        }, selector);
        if (info.missing || info.hidden) return info;
        expect(info.x, `${label || selector} off left edge`).toBeGreaterThanOrEqual(-1);
        expect(info.y, `${label || selector} off top edge`).toBeGreaterThanOrEqual(-1);
        expect(info.x + info.w, `${label || selector} off right edge (vw=${info.vw})`).toBeLessThanOrEqual(info.vw + 1);
        expect(info.y + info.h, `${label || selector} off bottom edge (vh=${info.vh})`).toBeLessThanOrEqual(info.vh + 1);
        return info;
    }

    /** Fail the test on uncaught page errors — catches silent JS breakage. */
    assertNoPageErrors() {
        expect(this.pageErrors, `page errors:\n${this.pageErrors.join('\n')}`).toEqual([]);
    }

    sliderHiddenLogs() {
        return this.consoleLines.filter((l) => l.includes('[Slider] Hidden'));
    }
}

module.exports = { SlingCraft, SHOT_DIR };
