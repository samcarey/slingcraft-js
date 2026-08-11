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
            // Every squadron is in flight; craft at rest are a count on their body.
            squadrons: squadrons.map((s) => ({
                count: s.count,
                source: s.sourceBody ? s.sourceBody.name : null,
                dest: s.destinationBody ? s.destinationBody.name : null,
                launchFrame: s.launchFrame,
            })),
            bodyCounts: Object.fromEntries(bodies.map((b) => [b.name, b.craftCount])),
            // What the map actually shows at the moment being viewed, which differs from
            // the plain total while scrubbing across a departure or an arrival.
            displayedCounts: Object.fromEntries(
                bodies.map((b) => [b.name, bodyDisplayCraftCount(b)])
            ),
        }));
    }

    /** The fan of candidate release angles currently on the map. */
    async fan() {
        return this.page.evaluate(() => ({
            count: transferFan.length,
            highlight: fanHighlight,
            launchFrame: fanLaunchFrame,
            scanning: fanScanPending > 0,
            elapsedMs: fanScanElapsedMs,
            routes: transferFan.map((e) => ({
                releaseDeg: +(e.releaseAngle * 180 / Math.PI).toFixed(1),
                minutes: +(e.arrivalOffset * PREDICTION_DT).toFixed(1),
                error: +e.error.toFixed(2),
                points: (e._screen || []).length,
            })),
        }));
    }

    /**
     * Every rocket currently on the map: one per squadron, plus the preview standing on
     * the origin while a transfer is being chosen.
     *
     * Read off the SVG transform, because that is the only place a rocket's position and
     * heading exist — it is drawn from a pose worked out per frame, not stored. `deg` is
     * the direction it points, screen-space, 0 = right and growing clockwise.
     */
    async rockets() {
        return this.page.evaluate(() => {
            const re = /translate\(([-\d.e+]+) ([-\d.e+]+)\) rotate\(([-\d.e+]+)\)/;
            return [...document.querySelectorAll('.craft-rocket')]
                .filter((g) => g.style.display !== 'none')
                .map((g) => {
                    const m = re.exec(g.getAttribute('transform') || '');
                    return {
                        preview: g.classList.contains('preview'),
                        count: g.querySelector('.rocket-count').textContent,
                        x: m ? +m[1] : null,
                        y: m ? +m[2] : null,
                        deg: m ? +m[3] : null,
                    };
                });
        });
    }

    /** Where a squadron's rocket was last drawn, in viewport coordinates. */
    async rocketPoint(index = 0) {
        return this.page.evaluate((i) => {
            const r = document.getElementById('game-svg').getBoundingClientRect();
            const p = squadrons[i]._rocketScreen;
            return p ? { x: p.x + r.left, y: p.y + r.top } : null;
        }, index);
    }

    /** Midpoint of each drawn fan curve, in viewport coordinates. */
    async fanMidpoints() {
        return this.page.evaluate(() => {
            const r = document.getElementById('game-svg').getBoundingClientRect();
            return transferFan.map((e, i) => {
                const pts = e._screen || [];
                if (pts.length < 2) return null;
                const m = pts[Math.floor(pts.length / 2)];
                return { i, x: m.x + r.left, y: m.y + r.top };
            }).filter(Boolean);
        });
    }

    /**
     * Every craft in the game. A fleet lives in two places now — parked craft are a
     * count on their body, craft in flight are a squadron — so conservation checks
     * have to add both or they will read a launch as craft vanishing.
     */
    async totalCraft() {
        return this.page.evaluate(() =>
            bodies.reduce((n, b) => n + b.craftCount, 0) +
            squadrons.reduce((n, s) => n + s.count, 0));
    }

    async craftAt(bodyName) {
        return (await this.state()).bodyCounts[bodyName] ?? 0;
    }

    // ---- map gestures --------------------------------------------------

    /**
     * All interaction goes through touch, matching how the game is actually
     * played. tap() requires hasTouch, which every project sets.
     */
    async tap(locator) {
        await expect(locator).toBeVisible();
        await locator.tap();
    }

    /**
     * Viewport coordinates of a body as it is DRAWN, which is not where it is in
     * world space — the display exaggerates sizes and compresses the gaps. Every
     * gesture below aims at the drawn position, same as a player's finger.
     */
    async bodyPoint(name) {
        return this.page.evaluate((n) => {
            const b = bodies.find((x) => x.name === n);
            if (!b) throw new Error(`no body named ${n}`);
            const p = bodyScreenPos(b);
            const r = document.getElementById('game-svg').getBoundingClientRect();
            return { x: p.x + r.left, y: p.y + r.top };
        }, name);
    }

    /** Tap a body on the map. A clean tap is the only thing that selects. */
    async tapBody(name) {
        const p = await this.bodyPoint(name);
        await this.page.touchscreen.tap(p.x, p.y);
        await expect
            .poll(() => this.page.evaluate(() => (selectedBody ? selectedBody.name : null)))
            .toBe(name);
    }

    /** Tap empty sky. Deselects, and lets auto-fit resume. */
    async tapElsewhere() {
        const vp = this.page.viewportSize();
        const x = 10;
        const y = Math.round(vp.height * 0.5);
        await this.page.touchscreen.tap(x, y);
        // Verify we actually missed every body, rather than silently selecting one.
        const hit = await this.page.evaluate(
            ([px, py]) => {
                const r = document.getElementById('game-svg').getBoundingClientRect();
                return !!findBodyAtPosition(px - r.left, py - r.top);
            },
            [x, y]
        );
        expect(hit, `tapElsewhere(${x},${y}) landed on a body`).toBe(false);
    }

    /**
     * Drag between two points with raw touch events.
     *
     * Playwright's touchscreen only taps, and the whole gesture under test lives
     * between touchstart and touchend: the hold that arms the drag, the moves
     * that hunt for a destination, and the release that commits.
     */
    async dragTouch(from, to, { holdMs = 0, steps = 14 } = {}) {
        await this.page.evaluate(
            async ({ sx, sy, dx, dy, hold, steps }) => {
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

                svg.dispatchEvent(mk('touchstart', sx, sy));
                if (hold) await wait(hold);
                for (let i = 1; i <= steps; i++) {
                    svg.dispatchEvent(mk('touchmove', sx + ((dx - sx) * i) / steps, sy + ((dy - sy) * i) / steps));
                    await wait(16);
                }
                svg.dispatchEvent(mk('touchend', dx, dy));
            },
            { sx: from.x, sy: from.y, dx: to.x, dy: to.y, hold: holdMs, steps }
        );
    }

    /**
     * Drag with REAL touch events, delivered through the browser's own input
     * pipeline rather than dispatched at the SVG.
     *
     * dragTouch() above aims its synthetic events straight at the SVG element, which
     * skips hit-testing entirely — so it happily "touches" a point covered by a panel.
     * That is fine for the body-to-body gestures, whose targets are known to be clear,
     * but it cannot be trusted for anything that has to land where the player can
     * actually reach. The fan is drawn across the whole map, including the parts the
     * transfer panel sits on top of, so its tests use this.
     */
    async dragReal(from, to, { holdMs = 0, steps = 14, stepMs = 25 } = {}) {
        const cdp = this._cdp || (this._cdp = await this.page.context().newCDPSession(this.page));
        const send = (type, x, y) => cdp.send('Input.dispatchTouchEvent', {
            type,
            touchPoints: type === 'touchEnd'
                ? []
                : [{ x, y, radiusX: 12, radiusY: 12, force: 1 }],
        });

        await send('touchStart', from.x, from.y);
        if (holdMs) await this.page.waitForTimeout(holdMs);
        for (let i = 1; i <= steps; i++) {
            await send('touchMove', from.x + ((to.x - from.x) * i) / steps, from.y + ((to.y - from.y) * i) / steps);
            await this.page.waitForTimeout(stepMs);
        }
        await send('touchEnd', to.x, to.y);
    }

    /**
     * Plan a transfer the way a player does, in one uninterrupted press: hold the
     * origin until it selects under the finger, then drag onto the destination and
     * release. Leaves the sim searching for launch windows.
     *
     * The hold is harmless when the origin is already selected — that arms the
     * drag at once — so this one helper covers both routes in.
     */
    async beginTransfer(origin, dest) {
        await this.dragTouch(await this.bodyPoint(origin), await this.bodyPoint(dest), { holdMs: 500 });
        await this.page.waitForFunction(
            () => transferState === 'searching' || transferState === 'ready',
            null,
            { timeout: 20_000 }
        );
    }

    /**
     * Wait until a scan has finished and left at least one viable route on the map,
     * moving the clock forward if the moment in view has no window.
     *
     * A scan that comes back empty is not a failure and not something to wait longer for
     * — it is a finished answer, and the readout says what to do about it: try the clock.
     * So that is what this does, which is also exactly the gesture a player makes. Waiting
     * instead would hang until the timeout on a state that had already settled.
     *
     * Hunting rather than trusting the opening moment is what keeps these tests off an
     * accident. A test that only ever worked because its setup happened to burn a few
     * seconds of sim time is pinned to that phase, and any change in startup timing
     * strands it on a dead moment — which is precisely what happened when the prediction
     * buffer stopped taking three seconds to build.
     *
     * minRoutes is the same argument one step further: a test that sweeps between routes,
     * or that expects picking a different one to look different, needs a moment offering
     * more than one, and how many any given moment offers is not something to assume.
     */
    async waitForTrajectories({ stepMinutes = 10, maxMinutes = 300, minRoutes = 1 } = {}) {
        await this.waitForScan();
        let minutes = await this.page.evaluate(() => timeViewOffset * PREDICTION_DT);
        for (let searched = 0; searched <= maxMinutes; searched += stepMinutes) {
            if (await this.page.evaluate((n) => transferFan.length >= n, minRoutes)) return;
            minutes += stepMinutes;
            await this.scrubToMinute(minutes);
        }
        throw new Error(
            `no moment offering ${minRoutes} route(s) within ${maxMinutes} minutes of the ` +
            `moment in view`);
    }

    /** Wait for any in-flight scan to settle, however it turns out. */
    async waitForScan() {
        await this.page.waitForFunction(
            () => fanScanPending === 0 && fanHasScanned,
            null,
            { timeout: 180_000, polling: 100 }
        );
    }

    /**
     * Wait until the camera has stopped moving.
     *
     * Anything that aims a finger at a drawn thing has to wait for this first. The view
     * eases rather than snaps — auto-fit does, and planning a transfer takes the camera
     * over and glides it onto the route being considered — so coordinates read the moment
     * a fan lands are stale by the time a touch is delivered to them, and the finger
     * arrives on empty sky (which pans, and so reads as the gesture being ignored).
     *
     * "Stopped" is judged in screen pixels between polls, not world units: the sim keeps
     * running underneath, so bodies drift and the fit's target drifts with them, and no
     * exact fixed point is ever reached.
     */
    async waitForViewSettled({ timeout = 30_000 } = {}) {
        // Start from no history, so this always takes two polls to answer. Left over from a
        // previous call, the stored sample would still match a camera that has been asked
        // to move but has not had a frame to start moving in — and the wait would return at
        // once, on the old view, which is the exact thing it exists to prevent.
        await this.page.evaluate(() => { window.__viewSettle = null; });
        await this.page.waitForFunction(
            () => {
                const now = { x: camera.x, y: camera.y, z: camera.zoom };
                const last = window.__viewSettle;
                window.__viewSettle = now;
                if (!last) return false;
                return Math.hypot(now.x - last.x, now.y - last.y) * now.z < 0.5
                    && Math.abs(Math.log(now.z / last.z)) < 1e-4;
            },
            null,
            { timeout, polling: 100 }
        );
    }

    /**
     * Point the view at a future moment, as the time wheel does, without waiting on
     * anything. Use when no transfer is being planned — there is no fan to re-scan then,
     * so scrubToMinute() would wait for a scan that never comes.
     */
    async viewMinute(minutes) {
        await this.page.evaluate((m) => { timeViewOffset = m / PREDICTION_DT; }, minutes);
    }

    /**
     * Point the view at a future moment, as the time wheel does, and wait for the
     * re-scan it provokes to land.
     */
    async scrubToMinute(minutes) {
        const before = await this.page.evaluate(() => fanScanGeneration);
        await this.page.evaluate((m) => { timeViewOffset = m / PREDICTION_DT; }, minutes);
        await this.page.waitForFunction(
            (g) => fanScanGeneration > g && fanScanPending === 0,
            before,
            { timeout: 60_000, polling: 50 }
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

    /** Build lives in the selected-body panel, which opens by tapping the body. */
    async buildCraftAt(bodyName) {
        await this.tapBody(bodyName);
        const before = await this.craftAt(bodyName);
        await this.tap(this.page.locator('#build-craft-btn'));
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
