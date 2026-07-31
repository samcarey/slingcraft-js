const { defineConfig, devices } = require('@playwright/test');

// 8099 is taken by another project (and Funnel-exposed), 8080/8081 by the dev
// server and an ssh forward. Use a port nothing else claims.
const PORT = process.env.TEST_PORT || 8177;

// Debug screenshots and traces land outside the repo so they never get committed.
// Override with SLINGCRAFT_SHOTS to keep them somewhere you can browse.
const SHOT_DIR =
    process.env.SLINGCRAFT_SHOTS ||
    require('path').join(require('os').tmpdir(), 'slingcraft-shots');

module.exports = defineConfig({
    testDir: './tests',
    // Every spec file and every test inside it runs concurrently.
    fullyParallel: true,
    // Each page runs an 18k-frame propagation plus a trajectory search, so the
    // suite is CPU-bound. Oversubscribing starves workers into false timeouts.
    workers: process.env.CI ? 2 : 2,
    // The sim propagates 18000 prediction frames before transfers are possible,
    // so per-test budgets are generous by necessity.
    timeout: 300_000,
    expect: { timeout: 20_000 },
    reporter: [['list'], ['json', { outputFile: `${SHOT_DIR}/results.json` }]],
    outputDir: `${SHOT_DIR}/artifacts`,
    use: {
        baseURL: `http://127.0.0.1:${PORT}`,
        screenshot: 'only-on-failure',
        video: 'off',
        trace: 'retain-on-failure',
    },
    // Mobile only, touch only — this game is played on a phone.
    //
    // These profiles ran on WebKit (the real iOS Safari engine) until WebKit
    // started hanging at launch on this machine — `webkit.launch()` times out
    // even standalone, and a --force reinstall did not clear it, so it is an OS
    // level wedge rather than a project problem. Chromium mobile emulation keeps
    // the viewport, device pixel ratio and touch input identical; only the
    // engine differs. Flip browserName back to 'webkit' once a reboot clears it.
    projects: [
        {
            name: 'iphone13',
            use: { ...devices['iPhone 13'], browserName: 'chromium', isMobile: true, hasTouch: true },
        },
        {
            // Smallest common screen: catches overlap the roomier phone hides.
            name: 'iphone-se',
            use: { ...devices['iPhone SE'], browserName: 'chromium', isMobile: true, hasTouch: true },
        },
    ],
    webServer: {
        command: `DEV_RELOAD=0 node dev-server.js ${PORT}`,
        url: `http://127.0.0.1:${PORT}/`,
        // Never adopt a stranger's server on this port — a stale listener from
        // another project silently tested the wrong app once already.
        reuseExistingServer: false,
        timeout: 20_000,
    },
});

module.exports.SHOT_DIR = SHOT_DIR;
