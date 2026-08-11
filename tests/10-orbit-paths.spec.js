const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

// A body's future path answers one question — where will this planet be when the craft
// get there — so it is drawn exactly that far: out to the arrival of the last thing still
// on its way, or of the route currently being chosen. With nothing in the air and nothing
// being planned there is no question, and no lines.

/** The `d` of every body's orbit path. */
const orbitPaths = (page) => page.evaluate(() =>
    bodies.map((b) => ({ name: b.name, d: b.trajectoryPath.getAttribute('d') || '' }))
);

test.describe('orbit paths', () => {
    test('an idle map draws no orbit paths at all', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        for (const p of await orbitPaths(page)) {
            expect(p.d, `${p.name} drew an orbit with nothing in flight`).toBe('');
        }
        // The centre-of-mass dot went with them: a point no gesture ever addressed and no
        // decision ever turned on.
        await expect(page.locator('.center-of-mass')).toHaveCount(0);
        await g.shot('no-orbits-at-rest');
        g.assertNoPageErrors();
    });

    test('choosing a route runs the orbits out to its arrival', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await page.waitForTimeout(400);

        // Drawn, expected and compared inside one frame. The camera is still easing into
        // the to-scale framing here, so a path drawn on one frame and read on the next
        // would differ by the camera's own motion rather than by anything claimed.
        const check = await page.evaluate(() => {
            updateTrajectories();
            const arrival = fanLaunchFrame + transferFan[fanHighlight].arrivalOffset;
            return {
                frame: bodyTrajectoryHorizon(Math.round(timeViewOffset)),
                arrival,
                bodies: bodies.map((b, i) => {
                    const d = b.trajectoryPath.getAttribute('d') || '';
                    const nums = (s) => s.trim().split(/\s+/).map(Number);
                    // The path runs backwards, so it opens on the arrival and closes on
                    // the body — which is what phases the dashes to the far end.
                    const opens = nums(d.split('L')[0].replace('M', ''));
                    const closes = nums(d.split('L').pop());
                    const at = predictionBuffer[arrival][i];
                    const want = displayTransform(at.x, at.y);
                    const here = displayTransform(b.x, b.y);
                    return {
                        name: b.name,
                        empty: d === '',
                        dashed: getComputedStyle(b.trajectoryPath).strokeDasharray,
                        offArrival: Math.hypot(opens[0] - want.x, opens[1] - want.y),
                        offBody: Math.hypot(closes[0] - here.x, closes[1] - here.y),
                    };
                }),
            };
        });
        expect(check.frame, 'the horizon is the chosen route arriving').toBe(check.arrival);
        for (const b of check.bodies) {
            expect(b.empty, `${b.name} drew nothing while a route was being chosen`).toBe(false);
            // Reaches where that body will be when the craft would land, and no further
            // into the prediction buffer — and starts there, so the dashes are counted
            // from the arrival rather than from the body.
            expect(b.offArrival, `${b.name}'s orbit does not start at the arrival moment`).toBeLessThan(0.01);
            expect(b.offBody, `${b.name}'s orbit does not end at the body itself`).toBeLessThan(0.01);
            expect(b.dashed, `${b.name}'s orbit is not dashed`).toMatch(/^[\d.]+px,? [\d.]+px$/);
        }
        await g.shot('orbits-to-the-chosen-route');
        g.assertNoPageErrors();
    });

    test('a launch in the air holds them open, and its arrival closes them', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(800);

        // The controls are gone; what keeps the orbits drawn now is the flight itself.
        await expect(page.locator('#transfer-launch-controls')).toBeHidden();
        const flight = await page.evaluate(() => ({
            horizon: bodyTrajectoryHorizon(Math.round(timeViewOffset)),
            arrival: squadrons[0].launchFrame + squadrons[0].trajectoryBuffer.length - 1,
        }));
        expect(flight.horizon).toBe(flight.arrival);
        for (const p of await orbitPaths(page)) {
            expect(p.d, `${p.name} lost its orbit while craft were in flight`).not.toBe('');
        }

        // Past the landing there is nothing left to be early for.
        await page.evaluate(() => {
            const sq = squadrons[0];
            setTimeViewOffset(sq.launchFrame + sq.trajectoryBuffer.length + 20);
        });
        await page.waitForTimeout(300);
        for (const p of await orbitPaths(page)) {
            expect(p.d, `${p.name} kept its orbit after everything had landed`).toBe('');
        }
        await g.shot('orbits-after-arrival');
        g.assertNoPageErrors();
    });
});
