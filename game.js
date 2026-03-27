/* ═══════════════════════════════════════════════════════════════
   Constants
═══════════════════════════════════════════════════════════════ */
const COLS          = 20;
const ROWS          = 20;
const CELL          = 20;
const CELL_HALF     = CELL >> 1;   // 10
const CELL_INNER    = CELL - 2;    // 18 — segment draw size
const TOTAL_CELLS   = COLS * ROWS; // 400

// Power-of-2 ring capacity enables fast bitwise wrap (& mask) instead of %
const RING_CAP  = 512;
const RING_MASK = RING_CAP - 1;

const MIN_INTERVAL    = 55;  // ms — speed floor
const SPECIAL_TTL     = 70;  // ticks before special food vanishes
const COMBO_WINDOW    = 8;   // max tick gap between eats for a combo
const INPUT_QUEUE_MAX = 2;   // direction changes buffered ahead
const SPECIAL_EVERY   = 5;   // spawn special food every N regular foods eaten

/* ═══════════════════════════════════════════════════════════════
   Shared, frozen direction vectors
   All of DIR_MAP, DPAD_MAP, and the `direction` variable reference
   these same four objects.  enqueueDirection() can therefore use a
   fast identity check (d === ref) to detect duplicate inputs.
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

// Integer cell key — |0 encourages V8 to keep the result as a Smi
const pos2key = (x, y) => (y * COLS + x) | 0;

/* ═══════════════════════════════════════════════════════════════
   Body colour lookup table — 31 strings built once at startup.
   Gradient: head (#34A853) → body rgb(70, 168–198, 83) → tail.
   Eliminates rebuildSnakeColors() and its per-eat string allocations.
═══════════════════════════════════════════════════════════════ */
const BODY_COLORS = Object.freeze(
  Array.from({ length: 31 }, (_, i) => 'rgb(70,' + (168 + i) + ',83)')
);

/* ═══════════════════════════════════════════════════════════════
   Star trig look-up tables — precomputed once.
   drawSpecialFood() was calling Math.cos/sin 10 times per frame.
   With these tables it pays 10 lookups + 10 multiplies instead.
═══════════════════════════════════════════════════════════════ */
const STAR_COS = new Float64Array(10);
const STAR_SIN = new Float64Array(10);
for (let i = 0; i < 10; i++) {
  const a    = (Math.PI / 5) * i - Math.PI * 0.5;
  STAR_COS[i] = Math.cos(a);
  STAR_SIN[i] = Math.sin(a);
}

/* ═══════════════════════════════════════════════════════════════
   RingDeque
   O(1) pushFront / popBack via index arithmetic on typed arrays.
   Power-of-2 capacity → bitwise AND instead of modulo.
   reset() reuses the same TypedArrays across games — zero allocation.
   getIdx(i) exposes the raw physical index so callers can read
   _xs[idx] and _ys[idx] with a single modulo, not two.
═══════════════════════════════════════════════════════════════ */
class RingDeque {
  constructor() {
    this._xs   = new Int16Array(RING_CAP);
    this._ys   = new Int16Array(RING_CAP);
    this._head = 0;
    this._size = 0;
  }

  reset()        { this._head = 0; this._size = 0; }
  get length()   { return this._size; }

  pushFront(x, y) {
    this._head           = (this._head - 1) & RING_MASK;
    this._xs[this._head] = x;
    this._ys[this._head] = y;
    if (this._size < RING_CAP) this._size++;
  }

  popBack() { if (this._size > 0) this._size--; }

  // Raw physical index for index i — callers use _xs[idx] and _ys[idx] directly
  getIdx(i)  { return (this._head + i) & RING_MASK; }
  getX(i)    { return this._xs[(this._head + i) & RING_MASK]; }
  getY(i)    { return this._ys[(this._head + i) & RING_MASK]; }
  headX()    { return this._xs[this._head]; }
  headY()    { return this._ys[this._head]; }
  tailKey()  {
    const i = (this._head + this._size - 1) & RING_MASK;
    return pos2key(this._xs[i], this._ys[i]);
  }
}

/* ═══════════════════════════════════════════════════════════════
   State
═══════════════════════════════════════════════════════════════ */
const snake   = new RingDeque(); // allocated once — reset() each game
const bodySet = new Set();       // allocated once — clear() each game

let direction;    // one of D_UP / D_DOWN / D_LEFT / D_RIGHT
const inputQueue = [];           // allocated once — .length = 0 each game

// Food objects reused across games — no heap allocation per eat
const _foodObj        = { x: 0, y: 0 };
const _specialFoodObj = { x: 0, y: 0, ttl: 0 };
let food;        // → _foodObj | null
let specialFood; // → _specialFoodObj | null
let foodsEaten;  // count of regular foods eaten (drives special food cadence)

let score, highScore, level;
let combo, lastEatTick, tickCount;
let stepInterval, baseSpeed;

let rafId, lastTimestamp, accumulator;
let gameState;   // 'idle' | 'running' | 'paused' | 'over' | 'dying'
let eatAnimTick;
let deathRafId;

// Dirty flags — skip textContent writes when values are unchanged
let _domScore = -1, _domBest = -1, _domLevel = -1;

/* ═══════════════════════════════════════════════════════════════
   Canvas + offscreen grid cache
═══════════════════════════════════════════════════════════════ */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');

const gridCanvas  = document.createElement('canvas');
gridCanvas.width  = canvas.width;
gridCanvas.height = canvas.height;
(function buildGrid() {
  const gx = gridCanvas.getContext('2d');
  gx.strokeStyle = 'rgba(0,0,0,0.04)';
  gx.lineWidth   = 0.5;
  for (let c = 0; c <= COLS; c++) {
    gx.beginPath(); gx.moveTo(c * CELL, 0); gx.lineTo(c * CELL, canvas.height); gx.stroke();
  }
  for (let r = 0; r <= ROWS; r++) {
    gx.beginPath(); gx.moveTo(0, r * CELL); gx.lineTo(canvas.width, r * CELL); gx.stroke();
  }
})();

/* ═══════════════════════════════════════════════════════════════
   roundRect shim
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
   Cached canvas bounding rect (invalidated by ResizeObserver)
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

const SCREEN_PANELS = { start: startScreen, pause: pauseScreen, gameover: gameOverScreen };
let _visiblePanel = null; // tracks which panel is currently shown

/* ═══════════════════════════════════════════════════════════════
   Difficulty selector
═══════════════════════════════════════════════════════════════ */
baseSpeed = 150;
document.querySelectorAll('.diff-btn').forEach(function(btn) {
  btn.addEventListener('click', function() {
    document.querySelectorAll('.diff-btn').forEach(function(b) { b.classList.remove('active'); });
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
      break;
    }
  }
}

/* ═══════════════════════════════════════════════════════════════
   Initialize / reset
   Reuses all persistent allocations — zero heap activity per game.
═══════════════════════════════════════════════════════════════ */
function initGame() {
  const midX = COLS >> 1;
  const midY = ROWS >> 1;

  snake.reset();
  snake.pushFront(midX - 1, midY); // body segment (index 1)
  snake.pushFront(midX,     midY); // head (index 0)

  bodySet.clear();
  bodySet.add(pos2key(midX,     midY));
  bodySet.add(pos2key(midX - 1, midY));

  direction       = D_RIGHT;
  inputQueue.length = 0; // truncate in place — reuses existing array

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
   Dense board (>60% full): reservoir sampling — O(n), provably
   uniform without copying bodySet.
   Sparse board: rejection sampling — O(1) expected.
   Neither path allocates: reuses _foodObj / _specialFoodObj.
═══════════════════════════════════════════════════════════════ */
function spawnFood(isSpecial) {
  const otherFood = isSpecial ? food : specialFood;
  const otherKey  = otherFood ? pos2key(otherFood.x, otherFood.y) : -1;
  const freeCount = TOTAL_CELLS - bodySet.size - (otherKey >= 0 ? 1 : 0);
  if (freeCount <= 0) return;

  let x, y;

  if (freeCount < TOTAL_CELLS * 0.4) {
    // Algorithm R (reservoir sampling, k=1): each free cell gets equal probability
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
   Identity check (d === ref) works because all direction values
   are the same frozen D_* singletons across DIR_MAP and DPAD_MAP.
═══════════════════════════════════════════════════════════════ */
function enqueueDirection(d) {
  if (inputQueue.length >= INPUT_QUEUE_MAX) return;
  const ref = inputQueue.length ? inputQueue[inputQueue.length - 1] : direction;
  if (d === ref) return;                         // identity check: same direction
  if (d.x === -ref.x && d.y === -ref.y) return; // 180° reversal
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

  if (hx < 0 || hx >= COLS || hy < 0 || hy >= ROWS) { setState('dying'); return; }

  // The tail vacates its cell this tick; remove it before collision check so the
  // snake can legally move into where its own tail was (the tail is leaving).
  const tailKey = snake.tailKey();
  bodySet.delete(tailKey);

  const headKey = pos2key(hx, hy);
  if (bodySet.has(headKey)) {
    bodySet.add(tailKey); // restore so death-flash renders the full body
    setState('dying'); return;
  }

  snake.pushFront(hx, hy);
  bodySet.add(headKey);

  let ate = false;

  // Regular food
  if (hx === food.x && hy === food.y) {
    ate         = true;
    eatAnimTick = tickCount;
    combo       = tickCount - lastEatTick <= COMBO_WINDOW ? combo + 1 : 1;
    lastEatTick = tickCount;
    foodsEaten++;

    const pts = 10 * combo;
    score    += pts;
    showParticle(hx, hy, '+' + pts, combo > 1);
    spawnFood();

    // Counter-based trigger avoids the score % 50 skip-over bug
    // that occurs when combo multipliers cause score to jump past a multiple of 50.
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
    // Snake grew: tail stays in the deque, so it must stay in bodySet too.
    // Without this, the tail cell is absent from bodySet for one tick,
    // creating a phantom passable cell at the end of the snake.
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
   RAF loop — fixed timestep
   draw() is called only when there is something to paint:
   • 'running'        → every frame (game is active)
   • 'paused'         → only when specialFood is present (star pulses)
   • 'dying'          → death animation drives its own draw() calls
   • 'idle' / 'over'  → overlay covers the canvas entirely; skip draw
═══════════════════════════════════════════════════════════════ */
function rafLoop(timestamp) {
  rafId = requestAnimationFrame(rafLoop);

  if (gameState === 'running') {
    const delta   = Math.min(timestamp - lastTimestamp, 200);
    lastTimestamp = timestamp;
    accumulator  += delta;
    while (accumulator >= stepInterval) {
      step();
      accumulator -= stepInterval;
      if (gameState !== 'running') break;
    }
    draw(timestamp);
  } else {
    lastTimestamp = timestamp;
    if (gameState === 'paused' && specialFood) draw(timestamp);
  }
}

/* ═══════════════════════════════════════════════════════════════
   Death flash animation
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
      draw(ts, flashes % 2 === 1);
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
function draw(timestamp, deathFlash) {
  deathFlash = deathFlash || false;

  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.fillStyle = '#fff';
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  ctx.drawImage(gridCanvas, 0, 0);

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

  ctx.save();
  ctx.globalAlpha = 0.35 + urgency * 0.65;
  ctx.fillStyle   = '#FBBC05';
  ctx.shadowColor = 'rgba(251,188,5,.8)';
  ctx.shadowBlur  = 8;
  ctx.beginPath();
  for (let i = 0; i < 10; i++) {
    const r = i & 1 ? inner : outer;
    // STAR_COS/STAR_SIN replace 10 Math.cos + 10 Math.sin calls per frame
    i ? ctx.lineTo(cx + STAR_COS[i] * r, cy + STAR_SIN[i] * r)
      : ctx.moveTo(cx + STAR_COS[i] * r, cy + STAR_SIN[i] * r);
  }
  ctx.closePath();
  ctx.fill();
  ctx.shadowBlur = 0;
  ctx.restore();
}

function drawSnake(deathFlash) {
  const headScale = computeHeadScale();
  const len       = snake.length;
  const half      = CELL_INNER * 0.5;

  // Cache internal deque fields to skip repeated property lookups
  const head = snake._head;
  const xs   = snake._xs;
  const ys   = snake._ys;

  for (let i = 0; i < len; i++) {
    // Single (head+i) & RING_MASK per segment — getX/getY would each compute it
    const idx = (head + i) & RING_MASK;
    const px  = xs[idx] * CELL + 1;
    const py  = ys[idx] * CELL + 1;

    if (deathFlash) {
      ctx.fillStyle = i === 0 ? '#EA4335' : '#f28b82';
    } else if (i === 0) {
      ctx.fillStyle = '#34A853';
    } else {
      // BODY_COLORS maps ratio i/len → one of 30 pre-built strings; zero allocation
      ctx.fillStyle = BODY_COLORS[Math.min(30, (i / len * 30 + 0.5) | 0)];
    }

    if (i === 0 && headScale !== 1) {
      ctx.save();
      ctx.translate(px + half, py + half);
      ctx.scale(headScale, headScale);
      ctx.translate(-(px + half), -(py + half));
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

// Touches only the two elements that actually change — the outgoing panel
// and the incoming panel — instead of bulk-toggling all three every call.
function showScreen(which) {
  if (_visiblePanel !== null) {
    SCREEN_PANELS[_visiblePanel].classList.add('hidden');
    _visiblePanel = null;
  }
  if (which === null) {
    overlay.classList.add('hidden');
    return;
  }
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

  scoreEl.classList.remove('pop');
  requestAnimationFrame(function() { scoreEl.classList.add('pop'); });

  el.addEventListener('animationend', function() { el.remove(); }, { once: true });
}

/* ═══════════════════════════════════════════════════════════════
   Game flow
═══════════════════════════════════════════════════════════════ */
function startGame() {
  cancelAnimationFrame(deathRafId);
  deathRafId    = 0; // clear stale handle
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
   Two scalars instead of allocating {x,y} on every touchstart.
   touchcancel clears the flag so interrupted gestures don't fire.
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
═══════════════════════════════════════════════════════════════ */
gameState = 'idle';
initGame();
draw(0);
showScreen('start');
rafId = requestAnimationFrame(rafLoop);
