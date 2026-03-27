/* ═══════════════════════════════════════════════════════════════
   Constants
═══════════════════════════════════════════════════════════════ */
const COLS            = 20;
const ROWS            = 20;
const CELL            = 20;
const TOTAL_CELLS     = COLS * ROWS;
const MIN_INTERVAL    = 55;      // ms — speed floor
const SPECIAL_TTL     = 70;      // ticks until special food disappears
const COMBO_WINDOW    = 8;       // max ticks between eats for a combo streak
const INPUT_QUEUE_MAX = 2;       // direction changes buffered ahead of steps
const SPECIAL_EVERY   = 5;       // spawn special food every N regular foods eaten

/* ═══════════════════════════════════════════════════════════════
   Shared, frozen direction vectors
   Both DIR_MAP and DPAD_MAP reference the same four objects so
   identity checks (d === ref) work alongside value checks.
═══════════════════════════════════════════════════════════════ */
const D_UP    = Object.freeze({ x:  0, y: -1 });
const D_DOWN  = Object.freeze({ x:  0, y:  1 });
const D_LEFT  = Object.freeze({ x: -1, y:  0 });
const D_RIGHT = Object.freeze({ x:  1, y:  0 });

const DIR_MAP = {
  ArrowUp: D_UP,    w: D_UP,
  ArrowDown: D_DOWN, s: D_DOWN,
  ArrowLeft: D_LEFT, a: D_LEFT,
  ArrowRight: D_RIGHT, d: D_RIGHT,
};

const DPAD_MAP = { UP: D_UP, DOWN: D_DOWN, LEFT: D_LEFT, RIGHT: D_RIGHT };

/* ═══════════════════════════════════════════════════════════════
   Integer coordinate encoding  ─  zero-allocation O(1) Set keys.
═══════════════════════════════════════════════════════════════ */
const pos2key = (x, y) => y * COLS + x;

/* ═══════════════════════════════════════════════════════════════
   Body colour lookup table
   Pre-compute all 31 possible body-segment colour strings once.
   Eliminates template-string allocation in the hot draw loop.
   The green channel ranges from 168 (near head) to 198 (tail).
═══════════════════════════════════════════════════════════════ */
const BODY_COLORS = Array.from({ length: 31 }, (_, i) => `rgb(70,${168 + i},83)`);

/* ═══════════════════════════════════════════════════════════════
   Ring Deque  ─  O(1) push_front / push_back / pop_back.
   Backed by typed arrays for cache-friendly access.
   Capacity = TOTAL_CELLS + 1 handles a fully-grown snake.
═══════════════════════════════════════════════════════════════ */
class RingDeque {
  constructor(capacity) {
    this._cap  = capacity;
    this._xs   = new Int16Array(capacity);
    this._ys   = new Int16Array(capacity);
    this._head = 0;
    this._size = 0;
  }

  get length() { return this._size; }

  pushFront(x, y) {
    this._head = (this._head - 1 + this._cap) % this._cap;
    this._xs[this._head] = x;
    this._ys[this._head] = y;
    this._size++;
  }

  // Append to the logical back (used to build the initial snake without reversal tricks)
  pushBack(x, y) {
    const idx = (this._head + this._size) % this._cap;
    this._xs[idx] = x;
    this._ys[idx] = y;
    this._size++;
  }

  popBack() {
    if (this._size > 0) this._size--;
  }

  // Direct index access — caller computes (head+i)%cap once and reuses for X and Y
  headX()  { return this._xs[this._head]; }
  headY()  { return this._ys[this._head]; }
  tailX()  { return this._xs[(this._head + this._size - 1) % this._cap]; }
  tailY()  { return this._ys[(this._head + this._size - 1) % this._cap]; }
  getX(i)  { return this._xs[(this._head + i) % this._cap]; }
  getY(i)  { return this._ys[(this._head + i) % this._cap]; }
}

/* ═══════════════════════════════════════════════════════════════
   State
═══════════════════════════════════════════════════════════════ */
let snake;        // RingDeque
let bodySet;      // Set<number> — integer-encoded occupied cells
let direction;    // one of D_UP / D_DOWN / D_LEFT / D_RIGHT
let inputQueue;   // Array<direction>

let food;         // { x, y }
let specialFood;  // { x, y, ttl } | null
let foodsEaten;   // count of regular foods eaten this game

let score, highScore, level;
let combo, lastEatTick, tickCount;

let stepInterval; // current ms per logic tick
let baseSpeed;    // player-chosen difficulty baseline

let rafId;        // main rAF loop handle
let lastTimestamp, accumulator;

let gameState;    // 'idle' | 'running' | 'paused' | 'over' | 'dying'
let eatAnimTick;  // tick of the most recent eat (head-bounce animation)
let deathRafId;   // rAF handle for death-flash sequence

// Dirty flags — prevent writing DOM text nodes when values haven't changed
let _domScore = -1, _domBest = -1, _domLevel = -1;

/* ═══════════════════════════════════════════════════════════════
   Canvas
═══════════════════════════════════════════════════════════════ */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');

/* ═══════════════════════════════════════════════════════════════
   Offscreen grid cache
   Renders the 20×20 grid lines once into an offscreen canvas.
   Each frame uses a single drawImage instead of 82 canvas calls.
═══════════════════════════════════════════════════════════════ */
const gridCanvas  = document.createElement('canvas');
gridCanvas.width  = canvas.width;
gridCanvas.height = canvas.height;
const gridCtx     = gridCanvas.getContext('2d');
(function buildGrid() {
  gridCtx.strokeStyle = 'rgba(0,0,0,0.04)';
  gridCtx.lineWidth   = 0.5;
  for (let c = 0; c <= COLS; c++) {
    gridCtx.beginPath();
    gridCtx.moveTo(c * CELL, 0);
    gridCtx.lineTo(c * CELL, canvas.height);
    gridCtx.stroke();
  }
  for (let r = 0; r <= ROWS; r++) {
    gridCtx.beginPath();
    gridCtx.moveTo(0, r * CELL);
    gridCtx.lineTo(canvas.width, r * CELL);
    gridCtx.stroke();
  }
})();

/* ═══════════════════════════════════════════════════════════════
   roundRect shim
   Uses the native API (Chrome 99+, Firefox 112+, Safari 15.4+)
   and falls back to quadraticCurveTo on older browsers.
═══════════════════════════════════════════════════════════════ */
const _hasNativeRR = typeof ctx.roundRect === 'function';

function fillRoundRect(x, y, w, h, r) {
  ctx.beginPath();
  if (_hasNativeRR) {
    ctx.roundRect(x, y, w, h, r);
  } else {
    ctx.moveTo(x + r, y);
    ctx.lineTo(x + w - r, y);
    ctx.quadraticCurveTo(x + w, y, x + w, y + r);
    ctx.lineTo(x + w, y + h - r);
    ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
    ctx.lineTo(x + r, y + h);
    ctx.quadraticCurveTo(x, y + h, x, y + h - r);
    ctx.lineTo(x, y + r);
    ctx.quadraticCurveTo(x, y, x + r, y);
    ctx.closePath();
  }
  ctx.fill();
}

/* ═══════════════════════════════════════════════════════════════
   Cached canvas bounding rect
   Invalidated by ResizeObserver so particles stay correctly placed.
═══════════════════════════════════════════════════════════════ */
let _canvasRect = canvas.getBoundingClientRect();
new ResizeObserver(() => { _canvasRect = canvas.getBoundingClientRect(); }).observe(canvas);

/* ═══════════════════════════════════════════════════════════════
   DOM references
═══════════════════════════════════════════════════════════════ */
const overlay        = document.getElementById('overlay');
const startScreen    = document.getElementById('startScreen');
const pauseScreen    = document.getElementById('pauseScreen');
const gameOverScreen = document.getElementById('gameOverScreen');
const scoreEl        = document.getElementById('score');
const highScoreEl    = document.getElementById('highScore');
const levelEl        = document.getElementById('level');
const headerScoreEl  = document.getElementById('headerScore');
const finalScoreText = document.getElementById('finalScoreText');
const newBestText    = document.getElementById('newBestText');

/* Screen panel map — frozen so it's never re-created */
const SCREEN_PANELS = Object.freeze({
  start: startScreen, pause: pauseScreen, gameover: gameOverScreen,
});
// Tracks which panel is currently shown so showScreen only touches changing elements
let _visibleScreen = 'start';

/* ═══════════════════════════════════════════════════════════════
   Difficulty selector
═══════════════════════════════════════════════════════════════ */
baseSpeed = 150;
document.querySelectorAll('.diff-btn').forEach(btn => {
  btn.addEventListener('click', () => {
    document.querySelectorAll('.diff-btn').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    baseSpeed = parseInt(btn.dataset.speed, 10);
  });
});

/* ═══════════════════════════════════════════════════════════════
   Persistent high score
═══════════════════════════════════════════════════════════════ */
highScore = parseInt(localStorage.getItem('snakeHighScore') || '0', 10);
highScoreEl.textContent = highScore;

/* ═══════════════════════════════════════════════════════════════
   State machine
═══════════════════════════════════════════════════════════════ */
function setState(next) {
  gameState = next;
  switch (next) {
    case 'idle':
      showScreen('start');
      break;

    case 'running':
      showScreen(null);
      lastTimestamp = performance.now();
      accumulator   = 0;
      if (!rafId) rafId = requestAnimationFrame(rafLoop);
      break;

    case 'paused':
      showScreen('pause');
      break;

    case 'dying':
      runDeathAnimation();
      break;

    case 'over': {
      const isNewBest = score > highScore; // capture before saveHighScore mutates highScore
      saveHighScore();
      finalScoreText.textContent = `Score: ${score}`;
      newBestText.classList.toggle('hidden', !isNewBest);
      showScreen('gameover');
      break;
    }
  }
}

/* ═══════════════════════════════════════════════════════════════
   Initialize / reset
═══════════════════════════════════════════════════════════════ */
function initGame() {
  const midX = Math.floor(COLS / 2);
  const midY = Math.floor(ROWS / 2);

  // pushBack preserves insertion order without needing to reverse
  snake = new RingDeque(TOTAL_CELLS + 1);
  snake.pushBack(midX,     midY); // index 0 — head
  snake.pushBack(midX - 1, midY); // index 1 — first body segment

  bodySet = new Set([pos2key(midX, midY), pos2key(midX - 1, midY)]);

  direction  = D_RIGHT;
  inputQueue = [];

  score        = 0;
  level        = 1;
  combo        = 0;
  lastEatTick  = -99;
  tickCount    = 0;
  eatAnimTick  = -99;
  foodsEaten   = 0;
  specialFood  = null;
  stepInterval = baseSpeed;

  _domScore = _domBest = _domLevel = -1; // force full UI refresh on first tick

  spawnFood();
  updateScoreUI();
}

/* ═══════════════════════════════════════════════════════════════
   Food spawning
   isFree() avoids creating a new Set — it checks bodySet plus the
   two food positions inline.

   Dense boards (>60% full) use reservoir sampling (algorithm R)
   for O(n) guaranteed single-pass selection.
   Sparse boards use O(1) expected rejection sampling.
═══════════════════════════════════════════════════════════════ */
function spawnFood(isSpecial = false) {
  // Determine which cells are off-limits without allocating a new Set
  const foodKey    = food        ? pos2key(food.x,        food.y)        : -1;
  const sfoodKey   = specialFood ? pos2key(specialFood.x, specialFood.y) : -1;
  const isFree     = (x, y) => {
    const k = pos2key(x, y);
    return !bodySet.has(k) && k !== foodKey && k !== sfoodKey;
  };

  const freeCount = TOTAL_CELLS - bodySet.size
    - (food        ? 1 : 0)
    - (specialFood ? 1 : 0);

  if (freeCount <= 0) return;

  let rx, ry;

  if (freeCount < TOTAL_CELLS * 0.4) {
    // Algorithm R: scan once, each free cell replaces chosen with probability 1/count
    let count = 0, chosen = -1;
    for (let k = 0; k < TOTAL_CELLS; k++) {
      if (isFree(k % COLS, Math.floor(k / COLS))) {
        count++;
        if (Math.random() * count < 1) chosen = k; // P = 1/count for each cell
      }
    }
    if (chosen === -1) return;
    rx = chosen % COLS;
    ry = Math.floor(chosen / COLS);
  } else {
    do {
      rx = Math.floor(Math.random() * COLS);
      ry = Math.floor(Math.random() * ROWS);
    } while (!isFree(rx, ry));
  }

  if (isSpecial) specialFood = { x: rx, y: ry, ttl: SPECIAL_TTL };
  else           food        = { x: rx, y: ry };
}

/* ═══════════════════════════════════════════════════════════════
   Input queue
   Validates against the tail of the queue (or current direction)
   to block 180° reversals. Uses identity equality on frozen objects.
═══════════════════════════════════════════════════════════════ */
function enqueueDirection(d) {
  if (inputQueue.length >= INPUT_QUEUE_MAX) return;
  const ref = inputQueue.length ? inputQueue[inputQueue.length - 1] : direction;
  if (d === ref) return;                             // duplicate
  if (d.x === -ref.x && d.y === -ref.y) return;     // 180° reversal
  inputQueue.push(d);
}

/* ═══════════════════════════════════════════════════════════════
   Game step
═══════════════════════════════════════════════════════════════ */
function step() {
  tickCount++;
  if (inputQueue.length) direction = inputQueue.shift();

  const hx = snake.headX() + direction.x;
  const hy = snake.headY() + direction.y;

  // Wall collision
  if (hx < 0 || hx >= COLS || hy < 0 || hy >= ROWS) {
    setState('dying'); return;
  }

  // Remove the tail from bodySet before self-collision check.
  // The tail vacates its cell this tick; without this, a "wrap-around"
  // move where the new head enters the old tail cell would be a false kill.
  const tailKey = pos2key(snake.tailX(), snake.tailY());
  bodySet.delete(tailKey);

  const headKey = pos2key(hx, hy);
  if (bodySet.has(headKey)) {
    bodySet.add(tailKey); // restore tail so the death-flash renders correctly
    setState('dying'); return;
  }

  // Commit the new head
  snake.pushFront(hx, hy);
  bodySet.add(headKey);

  let ate = false;

  // Regular food
  if (food && hx === food.x && hy === food.y) {
    ate         = true;
    eatAnimTick = tickCount;
    combo       = (tickCount - lastEatTick <= COMBO_WINDOW) ? combo + 1 : 1;
    lastEatTick = tickCount;
    foodsEaten++;

    const points = 10 * combo;
    score += points;
    showParticle(hx, hy, `+${points}`, combo > 1);
    spawnFood();

    // Trigger special food every SPECIAL_EVERY regular foods eaten.
    // Using a counter avoids the score-skip bug that broke the score % 50 approach.
    if (!specialFood && foodsEaten % SPECIAL_EVERY === 0) spawnFood(true);
  }

  // Special food
  if (specialFood && hx === specialFood.x && hy === specialFood.y) {
    ate         = true;
    const points = 30 * Math.max(combo, 1);
    score       += points;
    combo++;
    lastEatTick = tickCount;
    showParticle(hx, hy, `+${points}`, true);
    specialFood = null;
  }

  if (!ate) {
    // Tail's cell was already removed from bodySet above; discard from the deque too
    snake.popBack();
  } else {
    // Snake grew: the tail cell stays in the deque, so restore it in bodySet
    bodySet.add(tailKey);
  }

  if (specialFood && --specialFood.ttl <= 0) specialFood = null;

  const newLevel = Math.floor(score / 50) + 1;
  if (newLevel !== level) {
    level        = newLevel;
    stepInterval = Math.max(MIN_INTERVAL, baseSpeed - (level - 1) * 8);
  }

  updateScoreUI();
}

/* ═══════════════════════════════════════════════════════════════
   RAF loop
   Fixed timestep: the accumulator drains in stepInterval-sized
   chunks so game speed is independent of display refresh rate.

   Canvas drawing is skipped during 'idle' — the overlay covers it
   entirely, so there is nothing to animate (saves ~60 draws/sec).
   During 'paused', drawing continues only when special food is
   present (its star pulses on timestamp).
═══════════════════════════════════════════════════════════════ */
function rafLoop(timestamp) {
  rafId = requestAnimationFrame(rafLoop);

  if (gameState === 'running') {
    const delta   = Math.min(timestamp - lastTimestamp, 200); // cap tab-restore spike
    lastTimestamp = timestamp;
    accumulator  += delta;

    while (accumulator >= stepInterval) {
      step();
      accumulator -= stepInterval;
      if (gameState !== 'running') break;
    }

    draw(timestamp);
  } else {
    lastTimestamp = timestamp; // keep fresh so resume starts with correct delta

    // Redraw only when there is something animating under the pause overlay
    if (gameState === 'paused' && specialFood) draw(timestamp);
    // 'idle' and 'over': canvas is fully covered by overlay — skip draw entirely
  }
}

/* ═══════════════════════════════════════════════════════════════
   Death flash
   Alternates red / normal over ~600 ms then transitions to 'over'.
═══════════════════════════════════════════════════════════════ */
function runDeathAnimation() {
  let   flashes = 0;
  const TOTAL   = 10;
  const STEP_MS = 60;
  let   prev    = performance.now();

  function frame(ts) {
    if (ts - prev >= STEP_MS) {
      prev = ts;
      draw(ts, ++flashes % 2 === 1); // odd frames → red
    }
    deathRafId = flashes < TOTAL
      ? requestAnimationFrame(frame)
      : (setState('over'), undefined);
  }

  deathRafId = requestAnimationFrame(frame);
}

/* ═══════════════════════════════════════════════════════════════
   Rendering
═══════════════════════════════════════════════════════════════ */
function draw(timestamp = 0, deathFlash = false) {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.fillStyle = '#fff';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  ctx.drawImage(gridCanvas, 0, 0); // blit pre-rendered grid

  if (food)        drawFoodCircle(food.x, food.y);
  if (specialFood) drawSpecialFood(specialFood.x, specialFood.y, timestamp, specialFood.ttl / SPECIAL_TTL);

  drawSnake(deathFlash);
}

function drawFoodCircle(col, row) {
  const cx = col * CELL + CELL / 2;
  const cy = row * CELL + CELL / 2;
  const r  = CELL / 2 - 2;

  ctx.fillStyle = '#EA4335';
  ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();

  ctx.fillStyle = '#f28b82'; // specular highlight
  ctx.beginPath(); ctx.arc(cx - r * .28, cy - r * .28, r * .32, 0, Math.PI * 2); ctx.fill();
}

function drawSpecialFood(col, row, timestamp, urgency) {
  const cx    = col * CELL + CELL / 2;
  const cy    = row * CELL + CELL / 2;
  const pulse = 0.85 + Math.sin(timestamp / 180) * 0.15;
  const outer = (CELL / 2 - 1) * pulse;
  const inner = outer * 0.42;

  ctx.save();
  ctx.globalAlpha = 0.35 + urgency * 0.65; // fade as TTL approaches zero
  ctx.fillStyle   = '#FBBC05';
  ctx.shadowColor = 'rgba(251,188,5,.8)';
  ctx.shadowBlur  = 8;

  ctx.beginPath();
  for (let i = 0; i < 10; i++) {
    const angle = (Math.PI / 5) * i - Math.PI / 2;
    const r     = i % 2 === 0 ? outer : inner;
    i === 0
      ? ctx.moveTo(cx + Math.cos(angle) * r, cy + Math.sin(angle) * r)
      : ctx.lineTo(cx + Math.cos(angle) * r, cy + Math.sin(angle) * r);
  }
  ctx.closePath();
  ctx.fill();
  ctx.shadowBlur = 0;
  ctx.restore();
}

function drawSnake(deathFlash) {
  const headScale = computeHeadScale();
  const len       = snake.length;

  // Cache internal deque fields to avoid repeated property lookups
  // and to compute (head + i) % cap only once per segment instead of twice.
  const cap  = snake._cap;
  const head = snake._head;
  const xs   = snake._xs;
  const ys   = snake._ys;

  for (let i = 0; i < len; i++) {
    const idx = (head + i) % cap; // single modulo reused for both x and y
    const x   = xs[idx];
    const y   = ys[idx];

    if (deathFlash) {
      ctx.fillStyle = i === 0 ? '#EA4335' : '#f28b82';
    } else if (i === 0) {
      ctx.fillStyle = '#34A853';
    } else {
      // BODY_COLORS[0..30] — no string allocation, index clamped to [0,30]
      ctx.fillStyle = BODY_COLORS[Math.min(30, Math.round((i / len) * 30))];
    }

    const px = x * CELL + 1;
    const py = y * CELL + 1;
    const sz = CELL - 2;

    if (i === 0 && headScale !== 1) {
      ctx.save();
      ctx.translate(px + sz / 2, py + sz / 2);
      ctx.scale(headScale, headScale);
      ctx.translate(-(px + sz / 2), -(py + sz / 2));
      fillRoundRect(px, py, sz, sz, 6);
      ctx.restore();
    } else {
      fillRoundRect(px, py, sz, sz, i === 0 ? 6 : 4);
    }
  }

  if (!deathFlash) drawEyes(xs[head], ys[head]);
}

// Head-bounce: brief scale-up right after eating, interpolated within the step
function computeHeadScale() {
  const elapsed = tickCount - eatAnimTick;
  if (elapsed > 2) return 1;
  const t = Math.min(1, (accumulator / stepInterval + elapsed) / 3);
  return 1 + 0.28 * Math.sin(t * Math.PI);
}

function drawEyes(hx, hy) {
  const cx = hx * CELL + CELL / 2;
  const cy = hy * CELL + CELL / 2;
  const d  = direction;

  // Eye pair positions keyed by direction — no array allocation per frame
  let e1x, e1y, e2x, e2y;
  if      (d === D_RIGHT) { e1x = cx+4; e1y = cy-3; e2x = cx+4; e2y = cy+3; }
  else if (d === D_LEFT)  { e1x = cx-4; e1y = cy-3; e2x = cx-4; e2y = cy+3; }
  else if (d === D_UP)    { e1x = cx-3; e1y = cy-4; e2x = cx+3; e2y = cy-4; }
  else                    { e1x = cx-3; e1y = cy+4; e2x = cx+3; e2y = cy+4; }

  ctx.fillStyle = '#fff';
  ctx.beginPath(); ctx.arc(e1x, e1y, 2.5, 0, Math.PI * 2); ctx.fill();
  ctx.beginPath(); ctx.arc(e2x, e2y, 2.5, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = '#202124';
  ctx.beginPath(); ctx.arc(e1x, e1y, 1.2, 0, Math.PI * 2); ctx.fill();
  ctx.beginPath(); ctx.arc(e2x, e2y, 1.2, 0, Math.PI * 2); ctx.fill();
}

/* ═══════════════════════════════════════════════════════════════
   UI helpers
═══════════════════════════════════════════════════════════════ */
function updateScoreUI() {
  const best = Math.max(score, highScore);
  // Only write a text node when its value has actually changed
  if (score !== _domScore) {
    const s = String(score);
    scoreEl.textContent = s;
    headerScoreEl.textContent = s;
    _domScore = score;
  }
  if (best  !== _domBest)  { highScoreEl.textContent = String(best);  _domBest  = best;  }
  if (level !== _domLevel) { levelEl.textContent      = String(level); _domLevel = level; }
}

function saveHighScore() {
  if (score > highScore) {
    highScore = score;
    localStorage.setItem('snakeHighScore', highScore);
    highScoreEl.textContent = String(highScore);
    _domBest = highScore;
  }
}

// Touches only the panel that's actually changing — no bulk add/remove on all three
function showScreen(which) {
  if (_visibleScreen !== null) {
    SCREEN_PANELS[_visibleScreen].classList.add('hidden');
  }

  if (which === null) {
    overlay.classList.add('hidden');
    _visibleScreen = null;
    return;
  }

  overlay.classList.remove('hidden');
  SCREEN_PANELS[which].classList.remove('hidden');
  _visibleScreen = which;
}

// Floating +N particle using cached canvas rect; no layout reflow
function showParticle(col, row, text, isCombo = false) {
  const el = document.createElement('div');
  el.className   = 'particle';
  el.textContent = text;
  el.style.left  = `${_canvasRect.left + col * CELL + CELL / 2}px`;
  el.style.top   = `${_canvasRect.top  + row * CELL}px`;
  if (isCombo) el.style.color = '#FBBC05';
  document.body.appendChild(el);

  // Double-rAF restarts the pop animation without a forced synchronous layout
  scoreEl.classList.remove('pop');
  requestAnimationFrame(() => scoreEl.classList.add('pop'));

  el.addEventListener('animationend', () => el.remove(), { once: true });
}

/* ═══════════════════════════════════════════════════════════════
   Game flow
═══════════════════════════════════════════════════════════════ */
function startGame() {
  cancelAnimationFrame(deathRafId);
  deathRafId    = null;
  initGame();
  lastTimestamp = performance.now();
  accumulator   = 0;
  if (!rafId) rafId = requestAnimationFrame(rafLoop);
  setState('running');
}

function togglePause() {
  if      (gameState === 'running') setState('paused');
  else if (gameState === 'paused')  setState('running');
}

/* ═══════════════════════════════════════════════════════════════
   Auto-pause on tab switch / window blur
═══════════════════════════════════════════════════════════════ */
document.addEventListener('visibilitychange', () => {
  if (document.hidden && gameState === 'running') setState('paused');
});
window.addEventListener('blur', () => {
  if (gameState === 'running') setState('paused');
});

/* ═══════════════════════════════════════════════════════════════
   Keyboard input
═══════════════════════════════════════════════════════════════ */
const SCROLL_KEYS = new Set(['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', ' ']);

document.addEventListener('keydown', e => {
  if (SCROLL_KEYS.has(e.key)) e.preventDefault();

  const d = DIR_MAP[e.key];
  if (d) {
    if (gameState === 'idle')   { startGame(); return; }
    if (gameState === 'paused') setState('running');
    enqueueDirection(d);
    return;
  }

  if (e.key === 'p' || e.key === 'P') { togglePause(); return; }

  if (e.key === ' ') {
    if (gameState === 'idle')   startGame();
    if (gameState === 'paused') setState('running');
  }
});

/* ═══════════════════════════════════════════════════════════════
   Buttons
═══════════════════════════════════════════════════════════════ */
document.getElementById('startBtn').addEventListener('click', startGame);
document.getElementById('resumeBtn').addEventListener('click', () => setState('running'));
document.getElementById('retryBtn').addEventListener('click', startGame);
document.getElementById('restartFromPauseBtn').addEventListener('click', startGame);

/* ═══════════════════════════════════════════════════════════════
   Mobile: D-pad
═══════════════════════════════════════════════════════════════ */
document.querySelectorAll('.dpad-btn[data-dir]').forEach(btn => {
  btn.addEventListener('pointerdown', e => {
    e.preventDefault();
    const d = DPAD_MAP[btn.dataset.dir];
    if (!d) return;
    if (gameState === 'idle')   { startGame(); return; }
    if (gameState === 'paused') setState('running');
    enqueueDirection(d);
  });
});

/* ═══════════════════════════════════════════════════════════════
   Mobile: canvas swipe
   Two scalar variables instead of allocating { x, y } per touch.
═══════════════════════════════════════════════════════════════ */
let _touchX = 0, _touchY = 0, _touching = false;

canvas.addEventListener('touchstart', e => {
  _touchX   = e.touches[0].clientX;
  _touchY   = e.touches[0].clientY;
  _touching = true;
}, { passive: true });

canvas.addEventListener('touchend', e => {
  if (!_touching) return;
  _touching = false;

  const dx = e.changedTouches[0].clientX - _touchX;
  const dy = e.changedTouches[0].clientY - _touchY;

  if (Math.abs(dx) < 12 && Math.abs(dy) < 12) return; // ignore taps

  const d = Math.abs(dx) > Math.abs(dy)
    ? (dx > 0 ? D_RIGHT : D_LEFT)
    : (dy > 0 ? D_DOWN  : D_UP);

  if (gameState === 'idle')   { startGame(); return; }
  if (gameState === 'paused') setState('running');
  enqueueDirection(d);
}, { passive: true });

/* ═══════════════════════════════════════════════════════════════
   Boot
═══════════════════════════════════════════════════════════════ */
gameState = 'idle';
initGame();
draw(0); // render the initial board once before the overlay appears
showScreen('start');
rafId = requestAnimationFrame(rafLoop);
