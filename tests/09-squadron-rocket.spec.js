const { test, expect } = require('@playwright/test');
const { SlingCraft } = require('./helpers');

// A squadron is drawn as a rocket: one icon carrying the whole fleet's number and pointing
// where that fleet is going. It stands on its origin bobbing while it waits for its launch
// moment, and stops bobbing when it starts moving. Before it goes, it is also the way back
// into the decision — tapping it or its path reopens the launch controls.

/** Screen distance between two things with x/y. */
const gap = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);

/** Difference between two headings in degrees, wrapped into [0, 180]. */
function headingGap(a, b) {
    let d = Math.abs(a - b) % 360;
    return d > 180 ? 360 - d : d;
}

test.describe('the squadron rocket', () => {
    test('a transfer being chosen stands a rocket on the origin, aimed down the route', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await page.waitForTimeout(300);

        const rockets = await g.rockets();
        expect(rockets.length, 'one rocket while choosing, and it is the preview').toBe(1);
        expect(rockets[0].preview).toBe(true);

        // The pose it is drawn from, taken the way the game takes it: off the highlighted
        // route's own screen polyline. Measured here rather than off the drawn transform,
        // because the drawn one carries the bob and the bob is a separate claim.
        const geometry = await page.evaluate(() => {
            const c = bodyScreenPos(transferSourceBody);
            const pts = transferFan[fanHighlight]._screen;
            const { p0, p1 } = pathStartHeading(pts.length, (i) => pts[i]);
            const pose = parkedRocketPose(transferSourceBody, p0, p1);
            return {
                centre: { x: c.x, y: c.y },
                radius: bodyScreenRadius(transferSourceBody),
                pose: { x: pose.x, y: pose.y, deg: pose.heading * 180 / Math.PI },
                launchPoint: { x: p0.x, y: p0.y },
                // Where the route has got to once it has gone far enough to have a heading.
                onward: { x: p1.x, y: p1.y },
            };
        });

        const rocket = rockets[0];
        expect(gap(geometry.pose, geometry.centre), 'it stands on the drawn rim')
            .toBeCloseTo(geometry.radius, 2);

        const outDeg = Math.atan2(
            geometry.pose.y - geometry.centre.y,
            geometry.pose.x - geometry.centre.x) * 180 / Math.PI;
        const towardLaunch = Math.atan2(
            geometry.launchPoint.y - geometry.centre.y,
            geometry.launchPoint.x - geometry.centre.x) * 180 / Math.PI;
        expect(headingGap(outDeg, towardLaunch), 'on the side of the body the route leaves from')
            .toBeLessThan(0.5);

        const routeDeg = Math.atan2(
            geometry.onward.y - geometry.launchPoint.y,
            geometry.onward.x - geometry.launchPoint.x) * 180 / Math.PI;
        expect(headingGap(rocket.deg, routeDeg), 'pointing the way the route sets off')
            .toBeLessThan(1);

        // Drawn on that pose, off it only by the bob, and only along its own nose.
        const bob = await page.evaluate(() => ROCKET_BOB_FRACTION * ROCKET_LENGTH_PX / 2);
        expect(gap(rocket, geometry.pose), 'and drawn there, give or take the bob')
            .toBeLessThan(bob + 0.01);

        console.log(`AIM rocket at ${rocket.deg.toFixed(0)}deg, route leaves at ${routeDeg.toFixed(0)}deg, ` +
            `${gap(rocket, geometry.pose).toFixed(2)}px off its pose`);
        await g.shot('rocket-while-choosing');
        g.assertNoPageErrors();
    });

    test('the number on the rocket is the number leaving, so the body shows what stays', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();

        // The same five craft must not appear in two places. Whatever is on the slider is
        // on the rocket; the rest is still the body's, which is what "N stay" says in words.
        await g.tapSliderTo(3);
        await page.waitForTimeout(250);
        expect((await g.rockets())[0].count).toBe('3');
        expect((await g.state()).displayedCounts.Ember, 'two stay behind').toBe(2);
        await expect(page.locator('#transfer-stay-label')).toHaveText('2');

        await g.tapSliderTo(5);
        await page.waitForTimeout(250);
        expect((await g.rockets())[0].count).toBe('5');
        expect((await g.state()).displayedCounts.Ember, 'none stay behind').toBe(0);

        await g.shot('rocket-count-splits-the-fleet');
        g.assertNoPageErrors();
    });

    test('it bobs while it waits and holds still once it is under way', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(600);

        // Measured against the pose it would have if it were not bobbing, read at the same
        // instant. Sampling the drawn position alone would be measuring the map as much as
        // the rocket: over the two seconds this takes, the body it stands on has moved.
        const offset = () => page.evaluate(() => {
            const sq = squadrons[0];
            const pose = sq._displayPhase === 'pending' ? sq.waitingPose() : sq.flyingPose();
            // Not the preview — it is still in the DOM, hidden, holding the pose it had
            // when the launch was committed.
            const m = /translate\(([-\d.e+]+) ([-\d.e+]+)\)/.exec(
                document.querySelector('.craft-rocket:not(.preview)').getAttribute('transform'));
            // Split into travel along the nose and travel across it.
            const dx = +m[1] - pose.x, dy = +m[2] - pose.y;
            return {
                along: dx * Math.cos(pose.heading) + dy * Math.sin(pose.heading),
                across: -dx * Math.sin(pose.heading) + dy * Math.cos(pose.heading),
            };
        });

        // Waiting: sampled across a quarter of the period, which is where the movement is
        // fastest, so a still rocket cannot pass by luck.
        const waiting = [];
        for (let i = 0; i < 5; i++) {
            waiting.push(await offset());
            await page.waitForTimeout(425);
        }
        const swing = Math.max(...waiting.map((s) => s.along)) - Math.min(...waiting.map((s) => s.along));
        const wander = Math.max(...waiting.map((s) => Math.abs(s.across)));
        expect(swing, 'a waiting rocket moves').toBeGreaterThan(0.5);
        // 10% of its length end to end. A wait, not a dance — and along the nose, not
        // across it, so what it says is "about to set off that way".
        const bob = await page.evaluate(() => ROCKET_BOB_FRACTION * ROCKET_LENGTH_PX);
        expect(swing, 'and no further than the tenth of its length it is given')
            .toBeLessThan(bob + 0.01);
        expect(wander, 'strictly along its own axis').toBeLessThan(0.001);
        console.log(`BOB ${swing.toFixed(2)}px along the axis of a ${bob.toFixed(2)}px allowance`);

        // Under way: the only movement it has now is the trajectory's, so with the clock
        // parked the rocket is parked exactly on its pose.
        const launch = await page.evaluate(() => squadrons[0].launchFrame * PREDICTION_DT);
        await g.viewMinute(Math.ceil(launch) + 20);
        await page.waitForTimeout(400);
        for (let i = 0; i < 4; i++) {
            const o = await offset();
            expect(Math.hypot(o.along, o.across), 'a flying rocket has stopped bobbing')
                .toBeLessThan(0.001);
            await page.waitForTimeout(425);
        }

        await g.shot('rocket-in-flight');
        g.assertNoPageErrors();
    });

    test('launching moves nothing: the rocket stays where the preview stood', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.tapSliderTo(2);
        await page.waitForTimeout(250);

        const before = (await g.rockets())[0];
        await g.scheduleLaunch();
        await page.waitForTimeout(700);

        const after = await g.rockets();
        expect(after.length, 'the preview goes and the committed one takes its place').toBe(1);
        expect(after[0].preview).toBe(false);
        expect(after[0].count, 'carrying the number that was chosen').toBe('2');

        // Not identical — the clock goes back to the present at Launch, and the bodies have
        // moved between then and the launch moment — but the rocket is still on Ember's rim
        // pointing down the same route, not somewhere else on the map.
        const onRim = await page.evaluate(() => {
            const sq = squadrons[0];
            const c = bodyScreenPos(sq.sourceBody);
            return { d: Math.hypot(sq._rocketScreen.x - c.x, sq._rocketScreen.y - c.y),
                     r: bodyScreenRadius(sq.sourceBody) };
        });
        expect(onRim.d, 'still standing on its origin').toBeCloseTo(onRim.r, 1);
        console.log(`HANDOVER preview ${before.deg.toFixed(0)}deg -> committed ${after[0].deg.toFixed(0)}deg`);

        await g.shot('rocket-after-launch');
        g.assertNoPageErrors();
    });

    test('a launch that has not gone yet reopens from its rocket', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.tapSliderTo(3);
        await g.scheduleLaunch();
        await page.waitForTimeout(700);

        const launchFrame = await page.evaluate(() => squadrons[0].launchFrame);
        expect(launchFrame, 'it is still waiting to go').toBeGreaterThan(0);

        const at = await g.rocketPoint();
        await page.touchscreen.tap(at.x, at.y);
        await page.waitForTimeout(800);

        // The launch is unmade to reopen it: the craft are home, nothing is scheduled, and
        // what is on screen is the plan that made it — same pair, same moment, same number.
        const s = await g.state();
        expect(s.transferState, 'the launch controls are back').toMatch(/searching|ready/);
        expect(s.squadrons.length, 'the committed launch is undone while it is edited').toBe(0);
        expect(s.bodyCounts.Ember, 'and its craft are back at the body').toBe(5);
        expect(await page.evaluate(() => transferSourceBody.name)).toBe('Ember');
        expect(await page.evaluate(() => transferDestinationBody.name)).toBe('Terra');
        expect(await page.evaluate(() => transferQtySlider.value), 'the number already chosen')
            .toBe('3');
        expect(Math.round(s.timeViewOffset), 'and the moment already chosen').toBe(launchFrame);

        await g.shot('rocket-reopened');
        g.assertNoPageErrors();
    });

    test('or from the path it is going to fly', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.scheduleLaunch();
        await page.waitForTimeout(700);

        // Somewhere out along the drawn path, well clear of both bodies.
        const on = await page.evaluate(() => {
            const d = document.querySelector('.craft-trajectory').getAttribute('d') || '';
            const pts = [...d.matchAll(/([-\d.]+) ([-\d.]+)/g)].map((m) => ({ x: +m[1], y: +m[2] }));
            const r = document.getElementById('game-svg').getBoundingClientRect();
            const p = pts[Math.floor(pts.length / 2)];
            return { x: p.x + r.left, y: p.y + r.top };
        });
        await page.touchscreen.tap(on.x, on.y);
        await page.waitForTimeout(800);

        expect(await page.evaluate(() => transferState), 'the path is the launch too')
            .toMatch(/searching|ready/);
        expect((await g.state()).squadrons.length).toBe(0);
        await g.shot('reopened-from-path');
        g.assertNoPageErrors();
    });

    test('reopening and cancelling calls the launch off', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        expect(await g.totalCraft()).toBe(5);

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.tapSliderTo(4);
        await g.scheduleLaunch();
        await page.waitForTimeout(700);

        const at = await g.rocketPoint();
        await page.touchscreen.tap(at.x, at.y);
        await page.waitForTimeout(800);
        await g.cancelTransfer();
        await page.waitForTimeout(500);

        const s = await g.state();
        expect(s.transferState).toBe('none');
        expect(s.squadrons.length, 'nothing is going anywhere').toBe(0);
        expect(s.bodyCounts.Ember, 'every craft is back where it started').toBe(5);
        expect(await g.totalCraft(), 'and none were minted or lost on the way').toBe(5);
        expect(await g.rockets(), 'no rocket left on the map').toEqual([]);

        await g.shot('launch-called-off');
        g.assertNoPageErrors();
    });

    test('reopening and sending fewer leaves the rest behind', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();

        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.tapSliderTo(5);
        await g.scheduleLaunch();
        await page.waitForTimeout(700);

        const at = await g.rocketPoint();
        await page.touchscreen.tap(at.x, at.y);
        await page.waitForTimeout(800);
        await g.tapSliderTo(2);
        await g.scheduleLaunch();
        await page.waitForTimeout(700);

        const s = await g.state();
        expect(s.squadrons.length, 'one launch, not two').toBe(1);
        expect(s.squadrons[0].count, 'sending the smaller number now').toBe(2);
        expect(s.bodyCounts.Ember, 'and the other three never left').toBe(3);
        expect(await g.totalCraft()).toBe(5);
        expect((await g.rockets())[0].count).toBe('2');

        await g.shot('launch-adjusted');
        g.assertNoPageErrors();
    });

    test('tapping the body a launch waits on still selects the body', async ({ page }, testInfo) => {
        const g = new SlingCraft(page, testInfo);
        await g.boot();
        await g.waitForPropagation();
        await g.beginTransfer('Ember', 'Terra');
        await g.waitForTrajectories();
        await g.tapSliderTo(1);
        await g.scheduleLaunch();
        await page.waitForTimeout(700);

        // The rocket stands on one point of the rim and wins only there. The rest of the
        // disc is still the body's, or a pending launch would lock its own origin.
        await g.tapBody('Ember');
        await page.waitForTimeout(400);
        expect(await page.evaluate(() => selectedBody && selectedBody.name),
            'the centre of the body is still the body').toBe('Ember');
        expect(await page.evaluate(() => transferState), 'and no launch was reopened').toBe('none');
        await expect(page.locator('#craft-count-display')).toHaveText('4');

        await g.shot('body-still-tappable');
        g.assertNoPageErrors();
    });
});
