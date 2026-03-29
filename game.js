/* ═══════════════════════════════════════════════════════════════
   Constants
═══════════════════════════════════════════════════════════════ */
const COLS            = 20;
const ROWS            = 20;
const CELL            = 20;
const CELL_HALF       = CELL >> 1;         // 10
const CELL_INNER      = CELL - 2;          // 18 — segment draw size
const CELL_INNER_HALF = CELL_INNER * 0.5;  // 9  — used in head-scale transform
const TOTAL_CELLS     = COLS * ROWS;       // 400

// Power-of-2 capacity enables bitwise AND in place of modulo inside RingDeque
const RING_CAP  = 512;
const RING_MASK = RING_CAP - 1;

const MIN_INTERVAL    = 55;  // ms — speed floor
const SPECIAL_TTL     = 70;  // ticks before special food vanishes
const COMBO_WINDOW    = 8;   // max tick gap between eats to continue a combo
const INPUT_QUEUE_MAX = 2;   // direction changes buffered ahead of steps
const SPECIAL_EVERY   = 5;   // spawn special food every N regular foods eaten

// Food circle geometry — r = CELL_HALF - 2 = 8 is a compile-time constant.
// Precomputing the sub-highlight values avoids 3 multiplications per frame.
const FOOD_R            = CELL_HALF - 2;        //  8
const FOOD_SHINE_OFFSET = FOOD_R * 0.28;        //  2.24
const FOOD_SHINE_R      = FOOD_R * 0.32;        //  2.56

/* ═══════════════════════════════════════════════════════════════
   Shared, frozen direction vectors
   All direction references throughout the file point to these four
   objects, enabling O(1) identity checks (d === ref) in enqueueDirection.
═══════════════════════════════════════════════════════════════ */
const D_UP    = Object.freeze({ x:  0, y: -1 });
const D_DOWN  = Object.freeze({ x:  0, y:  1 });
const D_LEFT  = Object.freeze({ x: -1, y:  0 });
const D_RIGHT = Object.freeze({ x:  1, y:  0 });

const DIR_MAP = {
  ArrowUp: D_UP,   w: D_UP,
  ArrowDown: D_DOWN, s: D_DOWN,
  ArrowLeft: D_LEFT, a: D_LEFT,
  ArrowRight: D_RIGHT, d: D_RIGHT,
};

const DPAD_MAP = { UP: D_UP, DOWN: D_DOWN, LEFT: D_LEFT, RIGHT: D_RIGHT };

// Integer cell key — |0 encourages V8 to represent the result as a Smi
const pos2key = (x, y) => (y * COLS + x) | 0;

/* ═══════════════════════════════════════════════════════════════
   Body colour lookup table
   31 strings built once at startup. The draw loop indexes directly —
   zero string allocation per frame.
   Gradient: near-head rgb(70,168,83) → tail rgb(70,198,83).
═══════════════════════════════════════════════════════════════ */
const BODY_COLORS = Object.freeze(
  Array.from({ length: 31 }, (_, i) => 'rgb(70,' + (168 + i) + ',83)')
);

/* ═══════════════════════════════════════════════════════════════
   Star trig look-up tables — precomputed once at startup.
   Replaces 10 × Math.cos + 10 × Math.sin per animated frame
   with 20 typed-array lookups.
═══════════════════════════════════════════════════════════════ */
const STAR_COS = new Float64Array(10);
const STAR_SIN = new Float64Array(10);
for (let i = 0; i < 10; i++) {
  const a    = (Math.PI / 5) * i - Math.PI * 0.5;
  STAR_COS[i] = Math.cos(a);
  STAR_SIN[i] = Math.sin(a);
}

/* ═══════════════════════════════════════════════════════════════
   RingDeque — O(1) pushFront / popBack on typed arrays.
   Power-of-2 capacity → bitwise AND instead of modulo.
   reset() reuses TypedArrays — zero allocation per game.

   The overflow guard `if (size < RING_CAP)` has been removed:
   TOTAL_CELLS(400) < RING_CAP(512) is a static guarantee, so the
   guard was an unreachable dead branch that fired on every push.
═══════════════════════════════════════════════════════════════ */
class RingDeque {
  constructor() {
    this._xs   = new Int16Array(RING_CAP);
    this._ys   = new Int16Array(RING_CAP);
    this._head = 0;
    this._size = 0;
  }

  reset()      { this._head = 0; this._size = 0; }
  get length() { return this._size; }

  pushFront(x, y) {
    this._head           = (this._head - 1) & RING_MASK;
    this._xs[this._head] = x;
    this._ys[this._head] = y;
    this._size++;                  // no overflow guard needed: 400 < 512
  }

  popBack() { if (this._size > 0) this._size--; }

  headX() { return this._xs[this._head]; }
  headY() { return this._ys[this._head]; }

  tailKey() {
    const i = (this._head + this._size - 1) & RING_MASK;
    return pos2key(this._xs[i], this._ys[i]);
  }
}

/* ═══════════════════════════════════════════════════════════════
   2-slot input ring
   Replaces the `inputQueue` JS array (with its `shift()` O(n)
   mutation and heap pressure) with three scalar variables.
   Maximum buffered inputs is INPUT_QUEUE_MAX = 2.
     _iqLen = 0  → empty
     _iqLen = 1  → one entry at _iq0
     _iqLen = 2  → _iq0 is next to consume, _iq1 is last queued
═══════════════════════════════════════════════════════════════ */
let _iq0, _iq1, _iqLen = 0;

function enqueueDirection(d) {
  if (_iqLen >= INPUT_QUEUE_MAX) return;
  // Compare against the last queued entry (or current direction if queue is empty)
  const ref = _iqLen === 0 ? direction : (_iqLen === 1 ? _iq0 : _iq1);
  if (d === ref) return;                         // identical direction — no-op
  if (d.x === -ref.x && d.y === -ref.y) return; // 180° reversal — illegal
  if (_iqLen === 0) _iq0 = d; else _iq1 = d;
  _iqLen++;
}

/* ═══════════════════════════════════════════════════════════════
   State
═══════════════════════════════════════════════════════════════ */
const snake   = new RingDeque();
const bodySet = new Set();

let direction;

// Food objects reused every game — zero heap allocation per eat
const _foodObj        = { x: 0, y: 0 };
const _specialFoodObj = { x: 0, y: 0, ttl: 0 };
let food;        // → _foodObj | null
let specialFood; // → _specialFoodObj | null
let foodsEaten;

let score, highScore, level;
let combo, lastEatTick, tickCount;
let stepInterval, baseSpeed;

let rafId = 0, lastTimestamp, accumulator;
let gameState;   // 'idle' | 'running' | 'paused' | 'over' | 'dying'
let eatAnimTick;
let deathRafId = 0;

// Dirty flags — suppress textContent writes when values are unchanged
let _domScore = -1, _domBest = -1, _domLevel = -1;

/* ═══════════════════════════════════════════════════════════════
   Canvas setup — CW/CH cached once; canvas dimensions never change.
═══════════════════════════════════════════════════════════════ */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');
const CW     = canvas.width;
const CH     = canvas.height;

/* ═══════════════════════════════════════════════════════════════
   Offscreen grid cache — 82 lines rendered once, blitted each frame.
═══════════════════════════════════════════════════════════════ */
const gridCanvas  = document.createElement('canvas');
gridCanvas.width  = CW;
gridCanvas.height = CH;
(function buildGrid() {
  const gx = gridCanvas.getContext('2d');
  gx.strokeStyle = 'rgba(0,0,0,0.04)';
  gx.lineWidth   = 0.5;
  for (let c = 0; c <= COLS; c++) {
    gx.beginPath(); gx.moveTo(c * CELL, 0); gx.lineTo(c * CELL, CH); gx.stroke();
  }
  for (let r = 0; r <= ROWS; r++) {
    gx.beginPath(); gx.moveTo(0, r * CELL); gx.lineTo(CW, r * CELL); gx.stroke();
  }
})();

/* ═══════════════════════════════════════════════════════════════
   roundRect shim — native Chrome 99+/Firefox 112+/Safari 15.4+,
   fallback via quadraticCurveTo on older engines.
═══════════════════════════════════════════════════════════════ */
const _hasNativeRR = typeof ctx.roundRect === 'function';

function fillRoundRect(x, y, w, h, r) {
  ctx.beginPath();
  if (_hasNativeRR) {
    ctx.roundRect(x, y, w, h, r);
  } else {
    ctx.moveTo(x + r, y);
    ctx.lineTo(x + w - r, y);
    ctx.quadraticCurveTo(x + w, y,     x + w, y + r);
    ctx.lineTo(x + w, y + h - r);
    ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
    ctx.lineTo(x + r, y + h);
    ctx.quadraticCurveTo(x,     y + h, x,     y + h - r);
    ctx.lineTo(x, y + r);
    ctx.quadraticCurveTo(x,     y,     x + r, y);
    ctx.closePath();
  }
  ctx.fill();
}

/* ═══════════════════════════════════════════════════════════════
   Cached canvas bounding rect
   Invalidated by ResizeObserver; particle positioning uses this
   instead of calling getBoundingClientRect() per eat (forces layout).
═══════════════════════════════════════════════════════════════ */
let _canvasRect = canvas.getBoundingClientRect();
new ResizeObserver(function() { _canvasRect = canvas.getBoundingClientRect(); }).observe(canvas);

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

const SCREEN_PANELS = { start: startScreen, pause: pauseScreen, gameover: gameOverScreen };
let _visiblePanel = null;

/* ═══════════════════════════════════════════════════════════════
   Difficulty selector — diffBtns cached to avoid repeated DOM queries
═══════════════════════════════════════════════════════════════ */
baseSpeed = 150;
const diffBtns = document.querySelectorAll('.diff-btn');
diffBtns.forEach(function(btn) {
  btn.addEventListener('click', function() {
    diffBtns.forEach(function(b) { b.classList.remove('active'); });
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
    case 'idle':   showScreen('start'); break;
    case 'paused': showScreen('pause'); break;

    case 'dying':
      // Stop the main loop for the ~600 ms death animation.
      // runDeathAnimation() drives its own rAF; startGame() restarts rafLoop.
      cancelAnimationFrame(rafId);
      rafId = 0;
      runDeathAnimation();
      break;

    case 'running':
      showScreen(null);
      lastTimestamp = performance.now();
      accumulator   = 0;
      if (!rafId) rafId = requestAnimationFrame(rafLoop);
      break;

    case 'over': {
      const isNewBest = score > highScore; // capture before saveHighScore mutates it
      saveHighScore();
      finalScoreText.textContent = 'Score: ' + score;
      newBestText.classList.toggle('hidden', !isNewBest);
      showScreen('gameover');
      // rafId was already cancelled in 'dying'; nothing to cancel here
      break;
    }
  }
}

/* ═══════════════════════════════════════════════════════════════
   Initialize / reset — zero heap activity per game restart.
═══════════════════════════════════════════════════════════════ */
function initGame() {
  const midX = COLS >> 1;
  const midY = ROWS >> 1;

  snake.reset();
  snake.pushFront(midX - 1, midY); // body at index 1
  snake.pushFront(midX,     midY); // head at index 0

  bodySet.clear();
  bodySet.add(pos2key(midX,     midY));
  bodySet.add(pos2key(midX - 1, midY));

  direction = D_RIGHT;
  _iqLen    = 0; // flush 2-slot ring

  score        = 0;
  level        = 1;
  combo        = 0;
  lastEatTick  = -99;
  tickCount    = 0;
  eatAnimTick  = -99;
  foodsEaten   = 0;
  food         = null;
  specialFood  = null;
  stepInterval = baseSpeed;

  _domScore = _domBest = _domLevel = -1;

  spawnFood();
  updateScoreUI();
}

/* ═══════════════════════════════════════════════════════════════
   Food spawning
   Dense board (>60% full): reservoir sampling (Algorithm R) —
     O(n), provably uniform, no bodySet copy.
   Sparse board: rejection sampling — O(1) expected.
   Reuses _foodObj / _specialFoodObj — zero heap allocation per eat.
═══════════════════════════════════════════════════════════════ */
function spawnFood(isSpecial) {
  const otherFood = isSpecial ? food : specialFood;
  const otherKey  = otherFood ? pos2key(otherFood.x, otherFood.y) : -1;
  const freeCount = TOTAL_CELLS - bodySet.size - (otherKey >= 0 ? 1 : 0);
  if (freeCount <= 0) return;

  let x, y;

  if (freeCount < TOTAL_CELLS * 0.4) {
    // Algorithm R (k=1): each free cell gets probability exactly 1/seen
    let seen = 0, chosen = -1;
    for (let k = 0; k < TOTAL_CELLS; k++) {
      if (!bodySet.has(k) && k !== otherKey) {
        if ((Math.random() * ++seen | 0) === 0) chosen = k;
      }
    }
    if (chosen < 0) return;
    x = chosen % COLS;
    y = chosen / COLS | 0;
  } else {
    let k;
    do {
      x = Math.random() * COLS | 0;
      y = Math.random() * ROWS | 0;
      k = pos2key(x, y);
    } while (bodySet.has(k) || k === otherKey);
  }

  if (isSpecial) {
    _specialFoodObj.x = x; _specialFoodObj.y = y; _specialFoodObj.ttl = SPECIAL_TTL;
    specialFood = _specialFoodObj;
  } else {
    _foodObj.x = x; _foodObj.y = y;
    food = _foodObj;
  }
}

/* ═══════════════════════════════════════════════════════════════
   Game step — one fixed-timestep logic tick
═══════════════════════════════════════════════════════════════ */
function step() {
  tickCount++;

  // Consume the oldest buffered direction from the 2-slot ring
  if (_iqLen) {
    direction = _iq0;
    if (_iqLen === 2) _iq0 = _iq1;
    _iqLen--;
  }

  const hx = snake.headX() + direction.x;
  const hy = snake.headY() + direction.y;

  // Wall collision
  if (hx < 0 || hx >= COLS || hy < 0 || hy >= ROWS) { setState('dying'); return; }

  // Remove the tail before self-collision check: tail vacates its cell this tick,
  // so the head may legally advance into that cell.
  const tailKey = snake.tailKey();
  bodySet.delete(tailKey);

  const headKey = pos2key(hx, hy);
  if (bodySet.has(headKey)) {
    bodySet.add(tailKey); // restore so death-flash renders the complete body
    setState('dying'); return;
  }

  snake.pushFront(hx, hy);
  bodySet.add(headKey);

  let ate = false;

  // Regular food — null guard covers the pathological board-full edge case
  if (food && hx === food.x && hy === food.y) {
    ate         = true;
    eatAnimTick = tickCount;
    combo       = tickCount - lastEatTick <= COMBO_WINDOW ? combo + 1 : 1;
    lastEatTick = tickCount;
    foodsEaten++;

    const pts = 10 * combo;
    score    += pts;
    showParticle(hx, hy, '+' + pts, combo > 1);
    spawnFood();

    // Counter-based trigger avoids the score % 50 skip-over bug that arises when
    // combo multipliers cause score to jump past a multiple of 50 in one step.
    if (!specialFood && foodsEaten % SPECIAL_EVERY === 0) spawnFood(true);
  }

  // Special food
  if (specialFood && hx === specialFood.x && hy === specialFood.y) {
    ate         = true;
    const pts   = 30 * Math.max(combo, 1);
    score      += pts;
    combo++;
    lastEatTick = tickCount;
    showParticle(hx, hy, '+' + pts, true);
    specialFood = null;
  }

  if (!ate) {
    snake.popBack(); // tail cell already removed from bodySet above
  } else {
    // Snake grew: tail stays in deque → its cell must stay in bodySet.
    // Without this restore the tail cell is absent for one tick, creating a
    // phantom passable gap at the tip of the body.
    bodySet.add(tailKey);
  }

  if (specialFood && --specialFood.ttl <= 0) specialFood = null;

  const newLevel = (score / 50 | 0) + 1;
  if (newLevel !== level) {
    level        = newLevel;
    stepInterval = Math.max(MIN_INTERVAL, baseSpeed - (level - 1) * 8);
  }

  updateScoreUI();
}

/* ═══════════════════════════════════════════════════════════════
   RAF loop — fixed timestep; renders only when there is something
   visible to paint.
     'running' → always draw
     'paused'  → draw only when specialFood is pulsing
     'dying'   → rafId is cancelled; this loop never fires
     'over'    → rafId was cancelled in 'dying'; never fires
     'idle'    → rafId never started; never fires
═══════════════════════════════════════════════════════════════ */
function rafLoop(timestamp) {
  rafId = requestAnimationFrame(rafLoop);

  if (gameState === 'running') {
    const delta   = Math.min(timestamp - lastTimestamp, 200); // cap tab-restore surge
    lastTimestamp = timestamp;
    accumulator  += delta;
    while (accumulator >= stepInterval) {
      step();
      accumulator -= stepInterval;
      if (gameState !== 'running') break;
    }
    // step() may have transitioned to 'dying' (which cancelled rafId and started
    // deathRafId). Guard so we do not render a normal frame after that transition.
    if (gameState === 'running') draw(timestamp);
  } else {
    lastTimestamp = timestamp;
    if (gameState === 'paused' && specialFood) draw(timestamp);
  }
}

/* ═══════════════════════════════════════════════════════════════
   Death flash animation
   Alternates red/normal at 60 ms intervals for ~600 ms total.
═══════════════════════════════════════════════════════════════ */
function runDeathAnimation() {
  let flashes = 0;
  const TOTAL = 10;
  const STEP  = 60;
  let   prev  = performance.now();

  function frame(ts) {
    if (ts - prev >= STEP) {
      prev = ts;
      flashes++;
      draw(ts, flashes % 2 === 1); // odd frames → red
    }
    deathRafId = flashes < TOTAL
      ? requestAnimationFrame(frame)
      : (setState('over'), 0);
  }
  deathRafId = requestAnimationFrame(frame);
}

/* ═══════════════════════════════════════════════════════════════
   Rendering
═══════════════════════════════════════════════════════════════ */
function draw(timestamp = 0, deathFlash = false) {
  ctx.fillStyle = '#fff';
  ctx.fillRect(0, 0, CW, CH);
  ctx.drawImage(gridCanvas, 0, 0);

  if (food)        drawFoodCircle(food.x, food.y);
  if (specialFood) drawSpecialFood(specialFood.x, specialFood.y, timestamp, specialFood.ttl / SPECIAL_TTL);
  drawSnake(deathFlash);
}

function drawFoodCircle(col, row) {
  const cx = col * CELL + CELL_HALF;
  const cy = row * CELL + CELL_HALF;

  ctx.fillStyle = '#EA4335';
  ctx.beginPath(); ctx.arc(cx, cy, FOOD_R, 0, Math.PI * 2); ctx.fill();

  // Sub-highlight uses precomputed constants — no per-frame multiplication
  ctx.fillStyle = '#f28b82';
  ctx.beginPath();
  ctx.arc(cx - FOOD_SHINE_OFFSET, cy - FOOD_SHINE_OFFSET, FOOD_SHINE_R, 0, Math.PI * 2);
  ctx.fill();
}

function drawSpecialFood(col, row, timestamp, urgency) {
  const cx    = col * CELL + CELL_HALF;
  const cy    = row * CELL + CELL_HALF;
  const pulse = 0.85 + Math.sin(timestamp / 180) * 0.15;
  const outer = (CELL_HALF - 1) * pulse;
  const inner = outer * 0.42;

  // Manually save/restore only globalAlpha instead of ctx.save/restore,
  // which pushes the entire state record (transform, clip, compositing, etc.).
  const prevAlpha      = ctx.globalAlpha;
  ctx.globalAlpha      = 0.35 + urgency * 0.65;
  ctx.fillStyle        = '#FBBC05';
  ctx.shadowColor      = 'rgba(251,188,5,.8)';
  ctx.shadowBlur       = 8;

  ctx.beginPath();
  for (let i = 0; i < 10; i++) {
    const r = i & 1 ? inner : outer;
    i ? ctx.lineTo(cx + STAR_COS[i] * r, cy + STAR_SIN[i] * r)
      : ctx.moveTo(cx + STAR_COS[i] * r, cy + STAR_SIN[i] * r);
  }
  ctx.closePath();
  ctx.fill();

  // Restore exactly what we changed; shadowColor must be reset so it doesn't
  // linger in context state and affect subsequent semi-transparent draws.
  ctx.shadowBlur  = 0;
  ctx.shadowColor = 'transparent';
  ctx.globalAlpha = prevAlpha;
}

function drawSnake(deathFlash) {
  const headScale = computeHeadScale();
  const len       = snake.length;

  // Cache internal deque fields for direct typed-array access — avoids
  // property-chain lookups and the double (head+i) & RING_MASK that
  // getX() + getY() would each compute separately.
  const head = snake._head;
  const xs   = snake._xs;
  const ys   = snake._ys;

  if (deathFlash) {
    // In death-flash mode all body segments share one colour. Set it once
    // outside the loop; the head colour is the only per-iteration exception.
    ctx.fillStyle = '#f28b82';
  }

  for (let i = 0; i < len; i++) {
    const idx = (head + i) & RING_MASK;
    const px  = xs[idx] * CELL + 1;
    const py  = ys[idx] * CELL + 1;

    if (deathFlash) {
      // Only override fillStyle for the head; body was set before the loop
      if (i === 0) ctx.fillStyle = '#EA4335';
      else if (i === 1) ctx.fillStyle = '#f28b82'; // restore after head override
    } else if (i === 0) {
      ctx.fillStyle = '#34A853';
    } else {
      // i/len is in [1/len, (len-1)/len) — always < 1, so the result of
      // (i/len * 30 + 0.5)|0 is at most 30. Math.min(30, ...) is redundant.
      ctx.fillStyle = BODY_COLORS[(i / len * 30 + 0.5) | 0];
    }

    if (i === 0 && headScale !== 1) {
      ctx.save();
      ctx.translate(px + CELL_INNER_HALF, py + CELL_INNER_HALF);
      ctx.scale(headScale, headScale);
      ctx.translate(-(px + CELL_INNER_HALF), -(py + CELL_INNER_HALF));
      fillRoundRect(px, py, CELL_INNER, CELL_INNER, 6);
      ctx.restore();
    } else {
      fillRoundRect(px, py, CELL_INNER, CELL_INNER, i === 0 ? 6 : 4);
    }
  }

  if (!deathFlash) drawEyes();
}

function computeHeadScale() {
  const elapsed = tickCount - eatAnimTick;
  if (elapsed > 2) return 1;
  const t = Math.min(1, (accumulator / stepInterval + elapsed) / 3);
  return 1 + 0.28 * Math.sin(t * Math.PI);
}

function drawEyes() {
  const cx = snake.headX() * CELL + CELL_HALF;
  const cy = snake.headY() * CELL + CELL_HALF;
  const dx = direction.x;
  const dy = direction.y;

  let e1x, e1y, e2x, e2y;
  if      (dx ===  1) { e1x = cx + 4; e1y = cy - 3; e2x = cx + 4; e2y = cy + 3; }
  else if (dx === -1) { e1x = cx - 4; e1y = cy - 3; e2x = cx - 4; e2y = cy + 3; }
  else if (dy === -1) { e1x = cx - 3; e1y = cy - 4; e2x = cx + 3; e2y = cy - 4; }
  else                { e1x = cx - 3; e1y = cy + 4; e2x = cx + 3; e2y = cy + 4; }

  // Batch by colour: 2 fillStyle switches instead of 4
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

// Skips textContent writes when numeric values haven't changed.
// Assigning a number to textContent coerces it to string internally —
// explicit String() conversion is unnecessary overhead.
function updateScoreUI() {
  const best = score > highScore ? score : highScore;
  if (score !== _domScore) { scoreEl.textContent = headerScoreEl.textContent = (_domScore = score); }
  if (best  !== _domBest)  { highScoreEl.textContent = (_domBest  = best);  }
  if (level !== _domLevel) { levelEl.textContent     = (_domLevel = level); }
}

function saveHighScore() {
  if (score > highScore) {
    highScore = score;
    localStorage.setItem('snakeHighScore', highScore);
    highScoreEl.textContent = highScore;
    _domBest = highScore;
  }
}

// Touches only the two panels that change (outgoing + incoming) per call
function showScreen(which) {
  if (_visiblePanel !== null) {
    SCREEN_PANELS[_visiblePanel].classList.add('hidden');
    _visiblePanel = null;
  }
  if (which === null) { overlay.classList.add('hidden'); return; }
  overlay.classList.remove('hidden');
  SCREEN_PANELS[which].classList.remove('hidden');
  _visiblePanel = which;
}

function showParticle(col, row, text, isCombo) {
  const el = document.createElement('div');
  el.className   = 'particle';
  el.textContent = text;
  el.style.left  = (_canvasRect.left + col * CELL + CELL_HALF) + 'px';
  el.style.top   = (_canvasRect.top  + row * CELL) + 'px';
  if (isCombo) el.style.color = '#FBBC05';
  document.body.appendChild(el);

  // Two-frame rAF: remove in frame N, add in frame N+1 — restarts the CSS
  // animation without a forced synchronous layout (`void el.offsetWidth`).
  scoreEl.classList.remove('pop');
  requestAnimationFrame(function() { scoreEl.classList.add('pop'); });

  el.addEventListener('animationend', function() { el.remove(); }, { once: true });
}

/* ═══════════════════════════════════════════════════════════════
   Game flow
═══════════════════════════════════════════════════════════════ */
function startGame() {
  cancelAnimationFrame(deathRafId);
  deathRafId = 0;
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
   Auto-pause on tab switch or window blur
═══════════════════════════════════════════════════════════════ */
document.addEventListener('visibilitychange', function() {
  if (document.hidden && gameState === 'running') setState('paused');
});
window.addEventListener('blur', function() {
  if (gameState === 'running') setState('paused');
});

/* ═══════════════════════════════════════════════════════════════
   Keyboard input
═══════════════════════════════════════════════════════════════ */
const SCROLL_KEYS = new Set(['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', ' ']);

document.addEventListener('keydown', function(e) {
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
document.getElementById('resumeBtn').addEventListener('click', function() { setState('running'); });
document.getElementById('retryBtn').addEventListener('click', startGame);
document.getElementById('restartFromPauseBtn').addEventListener('click', startGame);

/* ═══════════════════════════════════════════════════════════════
   Mobile: D-pad
═══════════════════════════════════════════════════════════════ */
document.querySelectorAll('.dpad-btn[data-dir]').forEach(function(btn) {
  btn.addEventListener('pointerdown', function(e) {
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
   Two scalars avoid a {x,y} allocation on every touchstart.
   touchcancel clears the flag so interrupted gestures never fire.
═══════════════════════════════════════════════════════════════ */
let _txStart = 0, _tyStart = 0, _touching = false;

canvas.addEventListener('touchstart', function(e) {
  _txStart  = e.touches[0].clientX;
  _tyStart  = e.touches[0].clientY;
  _touching = true;
}, { passive: true });

canvas.addEventListener('touchcancel', function() { _touching = false; }, { passive: true });

canvas.addEventListener('touchend', function(e) {
  if (!_touching) return;
  _touching = false;
  const dx = e.changedTouches[0].clientX - _txStart;
  const dy = e.changedTouches[0].clientY - _tyStart;
  if (Math.abs(dx) < 12 && Math.abs(dy) < 12) return;

  const d = Math.abs(dx) > Math.abs(dy)
    ? (dx > 0 ? D_RIGHT : D_LEFT)
    : (dy > 0 ? D_DOWN  : D_UP);

  if (gameState === 'idle')   { startGame(); return; }
  if (gameState === 'paused') setState('running');
  enqueueDirection(d);
}, { passive: true });

/* ═══════════════════════════════════════════════════════════════
   Boot
   The RAF loop is NOT started here. The idle state has nothing to
   animate (specialFood is null, canvas is covered by the overlay).
   startGame() owns the first requestAnimationFrame call via `if (!rafId)`.
═══════════════════════════════════════════════════════════════ */
gameState = 'idle';
initGame();
draw(0);         // render the initial board once before the overlay appears
showScreen('start');
