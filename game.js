/* ═══════════════════════════════════════════════════════════════
   Constants
═══════════════════════════════════════════════════════════════ */
const COLS           = 20;
const ROWS           = 20;
const CELL           = 20;
const CELL_HALF      = CELL >> 1;          // 10
const CELL_INNER     = CELL - 2;           // 18 — segment draw size
const CELL_INNER_HALF = CELL_INNER * 0.5;  // 9  — eliminates per-call multiply in drawSnake
const TOTAL_CELLS    = COLS * ROWS;        // 400

// Power-of-2 capacity → bitwise AND replaces modulo in RingDeque
const RING_CAP  = 512;
const RING_MASK = RING_CAP - 1;

const MIN_INTERVAL    = 55;  // ms — speed floor
const SPECIAL_TTL     = 70;  // ticks before special food vanishes
const COMBO_WINDOW    = 8;   // max tick gap between eats to continue a combo
const INPUT_QUEUE_MAX = 2;   // direction changes buffered ahead of steps
const SPECIAL_EVERY   = 5;   // spawn special food every N regular foods eaten

/* ═══════════════════════════════════════════════════════════════
   Shared, frozen direction vectors
   DIR_MAP, DPAD_MAP, and the `direction` variable all reference the
   same four objects, so enqueueDirection() can use identity equality
   (d === ref) to detect duplicates in O(1) without value comparison.
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

// Integer cell key — |0 encourages V8 to keep the value as a Smi
const pos2key = (x, y) => (y * COLS + x) | 0;

/* ═══════════════════════════════════════════════════════════════
   Body colour lookup table
   31 strings built once at startup; the draw loop indexes directly
   into this array — zero string allocation per frame.
   Gradient: near-head rgb(70,168,83) → tail rgb(70,198,83).
═══════════════════════════════════════════════════════════════ */
const BODY_COLORS = Object.freeze(
  Array.from({ length: 31 }, (_, i) => 'rgb(70,' + (168 + i) + ',83)')
);

/* ═══════════════════════════════════════════════════════════════
   Star trig look-up tables
   Replaces 10 × Math.cos + 10 × Math.sin per frame with 20 lookups.
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
    if (this._size < RING_CAP) this._size++;
  }

  popBack() { if (this._size > 0) this._size--; }

  getX(i) { return this._xs[(this._head + i) & RING_MASK]; }
  getY(i) { return this._ys[(this._head + i) & RING_MASK]; }
  headX() { return this._xs[this._head]; }
  headY() { return this._ys[this._head]; }

  tailKey() {
    const i = (this._head + this._size - 1) & RING_MASK;
    return pos2key(this._xs[i], this._ys[i]);
  }
}

/* ═══════════════════════════════════════════════════════════════
   State
═══════════════════════════════════════════════════════════════ */
const snake      = new RingDeque(); // allocated once — reset() per game
const bodySet    = new Set();       // allocated once — clear() per game
const inputQueue = [];              // allocated once — .length=0 per game

let direction;   // one of D_UP / D_DOWN / D_LEFT / D_RIGHT

// Food objects reused across games — no heap allocation per eat
const _foodObj        = { x: 0, y: 0 };
const _specialFoodObj = { x: 0, y: 0, ttl: 0 };
let food;        // → _foodObj | null
let specialFood; // → _specialFoodObj | null
let foodsEaten;  // regular-food counter driving special-food cadence

let score, highScore, level;
let combo, lastEatTick, tickCount;
let stepInterval, baseSpeed;

let rafId, lastTimestamp, accumulator;
let gameState;   // 'idle' | 'running' | 'paused' | 'over' | 'dying'
let eatAnimTick;
let deathRafId;

// Dirty flags — suppress textContent writes when values are unchanged
let _domScore = -1, _domBest = -1, _domLevel = -1;

/* ═══════════════════════════════════════════════════════════════
   Canvas setup
   CW / CH cached once — canvas dimensions never change at runtime.
═══════════════════════════════════════════════════════════════ */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');
const CW     = canvas.width;   // 400 — avoid repeated property reads
const CH     = canvas.height;  // 400

/* ═══════════════════════════════════════════════════════════════
   Offscreen grid cache
   Renders all 82 grid lines once; each frame blits them in a single
   drawImage call instead of 82 stroke calls.
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
   roundRect shim
   ctx.roundRect() is native in Chrome 99+, Firefox 112+, Safari 15.4+.
   Falls back to quadraticCurveTo on older engines.
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
   Cached canvas bounding rect — invalidated by ResizeObserver.
   Particle positioning uses this instead of calling getBoundingClientRect()
   on every eat event, which forces a synchronous layout.
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
   Difficulty selector
   diffBtns cached at module level — avoids re-querying the DOM
   on every button click.
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
    case 'dying':  runDeathAnimation(); break;

    case 'running':
      showScreen(null);
      // Clear time debt so a long pause doesn't trigger a burst of steps on resume
      lastTimestamp = performance.now();
      accumulator   = 0;
      if (!rafId) rafId = requestAnimationFrame(rafLoop);
      break;

    case 'over': {
      // Capture new-best flag before saveHighScore() mutates `highScore`
      const isNewBest = score > highScore;
      saveHighScore();
      finalScoreText.textContent = 'Score: ' + score;
      newBestText.classList.toggle('hidden', !isNewBest);
      showScreen('gameover');
      // Cancel the main loop — nothing to animate when the game-over overlay is up.
      // startGame() restarts it via `if (!rafId)`.
      cancelAnimationFrame(rafId);
      rafId = 0;
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
  snake.pushFront(midX - 1, midY); // body segment at index 1
  snake.pushFront(midX,     midY); // head at index 0

  bodySet.clear();
  bodySet.add(pos2key(midX,     midY));
  bodySet.add(pos2key(midX - 1, midY));

  direction         = D_RIGHT;
  inputQueue.length = 0; // truncate in place — reuses the array allocation

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

  _domScore = _domBest = _domLevel = -1; // force full UI refresh

  spawnFood();
  updateScoreUI();
}

/* ═══════════════════════════════════════════════════════════════
   Food spawning
   Dense board (>60% full): reservoir sampling (Algorithm R) —
     O(n) single pass, provably uniform, no bodySet copy.
   Sparse board: rejection sampling — O(1) expected.
   Neither path allocates: _foodObj / _specialFoodObj are reused.
═══════════════════════════════════════════════════════════════ */
function spawnFood(isSpecial) {
  const otherFood = isSpecial ? food : specialFood;
  const otherKey  = otherFood ? pos2key(otherFood.x, otherFood.y) : -1;
  const freeCount = TOTAL_CELLS - bodySet.size - (otherKey >= 0 ? 1 : 0);
  if (freeCount <= 0) return;

  let x, y;

  if (freeCount < TOTAL_CELLS * 0.4) {
    // Algorithm R: visit every cell, replace chosen with probability 1/seen
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
   Input queue
   Identity comparison (d === ref) works because all direction values
   are the same frozen D_* singletons throughout the codebase.
═══════════════════════════════════════════════════════════════ */
function enqueueDirection(d) {
  if (inputQueue.length >= INPUT_QUEUE_MAX) return;
  const ref = inputQueue.length ? inputQueue[inputQueue.length - 1] : direction;
  if (d === ref) return;                         // same direction — no-op
  if (d.x === -ref.x && d.y === -ref.y) return; // 180° reversal — illegal
  inputQueue.push(d);
}

/* ═══════════════════════════════════════════════════════════════
   Game step — one fixed-timestep logic tick
═══════════════════════════════════════════════════════════════ */
function step() {
  tickCount++;
  if (inputQueue.length) direction = inputQueue.shift();

  const hx = snake.headX() + direction.x;
  const hy = snake.headY() + direction.y;

  // Wall collision
  if (hx < 0 || hx >= COLS || hy < 0 || hy >= ROWS) { setState('dying'); return; }

  // The tail vacates its cell this tick. Remove it from bodySet before checking
  // the new head so the snake can legally advance into its own departing tail.
  const tailKey = snake.tailKey();
  bodySet.delete(tailKey);

  const headKey = pos2key(hx, hy);
  if (bodySet.has(headKey)) {
    bodySet.add(tailKey); // restore tail so death-flash renders the full body
    setState('dying'); return;
  }

  snake.pushFront(hx, hy);
  bodySet.add(headKey);

  let ate = false;

  // Regular food — guard against null in the pathological board-full edge case
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

    // Counter-based trigger prevents the score % 50 skip-over bug that arises
    // when combo multipliers push score past a multiple of 50 in a single step.
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
    snake.popBack(); // tail already removed from bodySet above
  } else {
    // Snake grew: the tail stays in the deque, so its cell must remain in bodySet.
    // Without this restore, the tail cell is absent for one tick — a phantom gap
    // that lets the snake head pass through the tip of its own body.
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
   RAF loop — fixed timestep, render every display frame.
   draw() is guarded so it only fires when there is something
   to paint:
     'running' → always draw
     'paused'  → only when specialFood is animating (star pulse)
     'dying'   → death animation owns its own draw() calls
     'over'    → rafId cancelled in setState; loop never reaches here
     'idle'    → loop runs but overlay fully covers the canvas; draw skipped
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
    // Guard: step() may have called setState('dying'), changing gameState.
    // Drawing in that case would render one extra normal frame before the
    // death flash begins, creating a visible glitch.
    if (gameState === 'running') draw(timestamp);
  } else {
    lastTimestamp = timestamp;
    if (gameState === 'paused' && specialFood) draw(timestamp);
  }
}

/* ═══════════════════════════════════════════════════════════════
   Death flash animation
   Alternates red / normal over ~600 ms before transitioning to 'over'.
═══════════════════════════════════════════════════════════════ */
function runDeathAnimation() {
  let flashes = 0;
  const TOTAL = 10;
  const STEP  = 60; // ms per flash frame
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

// Default parameters replace the `param = param || false` body assignments.
function draw(timestamp = 0, deathFlash = false) {
  // fillRect alone is sufficient — clearRect (transparent) before an opaque
  // fillRect is redundant and wastes one canvas API call per frame.
  ctx.fillStyle = '#fff';
  ctx.fillRect(0, 0, CW, CH);
  ctx.drawImage(gridCanvas, 0, 0); // blit pre-rendered grid

  if (food)        drawFoodCircle(food.x, food.y);
  if (specialFood) drawSpecialFood(specialFood.x, specialFood.y, timestamp, specialFood.ttl / SPECIAL_TTL);
  drawSnake(deathFlash);
}

function drawFoodCircle(col, row) {
  const cx = col * CELL + CELL_HALF;
  const cy = row * CELL + CELL_HALF;
  const r  = CELL_HALF - 2;

  ctx.fillStyle = '#EA4335';
  ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = '#f28b82';
  ctx.beginPath(); ctx.arc(cx - r * .28, cy - r * .28, r * .32, 0, Math.PI * 2); ctx.fill();
}

function drawSpecialFood(col, row, timestamp, urgency) {
  const cx    = col * CELL + CELL_HALF;
  const cy    = row * CELL + CELL_HALF;
  const pulse = 0.85 + Math.sin(timestamp / 180) * 0.15;
  const outer = (CELL_HALF - 1) * pulse;
  const inner = outer * 0.42;

  // Save only globalAlpha instead of pushing the full canvas state with ctx.save().
  // ctx.save/restore stores the entire state record (transform, clip, line settings,
  // compositing, etc.) — far more than we need here.
  const prevAlpha = ctx.globalAlpha;
  ctx.globalAlpha = 0.35 + urgency * 0.65;
  ctx.fillStyle   = '#FBBC05';
  ctx.shadowColor = 'rgba(251,188,5,.8)';
  ctx.shadowBlur  = 8;

  ctx.beginPath();
  for (let i = 0; i < 10; i++) {
    const r = i & 1 ? inner : outer;
    i ? ctx.lineTo(cx + STAR_COS[i] * r, cy + STAR_SIN[i] * r)
      : ctx.moveTo(cx + STAR_COS[i] * r, cy + STAR_SIN[i] * r);
  }
  ctx.closePath();
  ctx.fill();

  ctx.shadowBlur  = 0;
  ctx.globalAlpha = prevAlpha; // restore only what we changed
}

function drawSnake(deathFlash) {
  const headScale = computeHeadScale();
  const len       = snake.length;

  // Cache internal deque fields to avoid repeated property chain lookups per segment
  const head = snake._head;
  const xs   = snake._xs;
  const ys   = snake._ys;

  for (let i = 0; i < len; i++) {
    const idx = (head + i) & RING_MASK; // single bitwise op; avoids getX + getY duplication
    const px  = xs[idx] * CELL + 1;
    const py  = ys[idx] * CELL + 1;

    if (deathFlash) {
      ctx.fillStyle = i === 0 ? '#EA4335' : '#f28b82';
    } else if (i === 0) {
      ctx.fillStyle = '#34A853';
    } else {
      ctx.fillStyle = BODY_COLORS[Math.min(30, (i / len * 30 + 0.5) | 0)];
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

// Interpolates a brief scale-up immediately after eating for tactile feedback
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

  // Batch same-colour draws: 2 fillStyle switches instead of 4
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

// Writes to DOM only when a value has actually changed
function updateScoreUI() {
  const best = score > highScore ? score : highScore;
  if (score !== _domScore) { scoreEl.textContent = headerScoreEl.textContent = String(_domScore = score); }
  if (best  !== _domBest)  { highScoreEl.textContent = String(_domBest = best); }
  if (level !== _domLevel) { levelEl.textContent     = String(_domLevel = level); }
}

function saveHighScore() {
  if (score > highScore) {
    highScore = score;
    localStorage.setItem('snakeHighScore', highScore);
    highScoreEl.textContent = String(highScore);
    _domBest = highScore;
  }
}

// Updates only the two elements that actually change (outgoing + incoming panel)
// instead of bulk-toggling all three on every call.
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

  // Two-frame rAF: remove class in frame N, add in frame N+1.
  // Allows the browser to process the style change between frames without
  // a forced synchronous layout (which `void el.offsetWidth` would cause).
  scoreEl.classList.remove('pop');
  requestAnimationFrame(function() { scoreEl.classList.add('pop'); });

  el.addEventListener('animationend', function() { el.remove(); }, { once: true });
}

/* ═══════════════════════════════════════════════════════════════
   Game flow
═══════════════════════════════════════════════════════════════ */
function startGame() {
  cancelAnimationFrame(deathRafId);
  deathRafId    = 0;
  initGame();
  lastTimestamp = performance.now();
  accumulator   = 0;
  // rafId is 0 after 'over' state cancels it, so this always starts a fresh loop
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
   Mobile: D-pad (pointerdown for zero-latency response)
═══════════════════════════════════════════════════════════════ */
document.querySelectorAll('.dpad-btn[data-dir]').forEach(function(btn) {
  btn.addEventListener('pointerdown', function(e) {
    e.preventDefault(); // blocks ghost click on touch devices
    const d = DPAD_MAP[btn.dataset.dir];
    if (!d) return;
    if (gameState === 'idle')   { startGame(); return; }
    if (gameState === 'paused') setState('running');
    enqueueDirection(d);
  });
});

/* ═══════════════════════════════════════════════════════════════
   Mobile: canvas swipe
   Two scalars instead of a {x,y} object allocation per touchstart.
   touchcancel clears the flag so interrupted gestures (notifications,
   incoming calls) never fire a phantom direction change.
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
draw(0);
showScreen('start');
rafId = requestAnimationFrame(rafLoop);
