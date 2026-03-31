/* ═══════════════════════════════════════════════════════════════
   Constants & Configuration
═══════════════════════════════════════════════════════════════ */
const COLS            = 20;
const ROWS            = 20;
const CELL            = 20;
const CELL_HALF       = CELL >> 1;         // 10
const CELL_INNER      = CELL - 2;          // 18 — segment draw size
const CELL_INNER_HALF = CELL_INNER * 0.5;  // 9  — used in head-scale transform
const TOTAL_CELLS     = COLS * ROWS;       // 400

// Logical canvas dimensions
const CW = COLS * CELL;
const CH = ROWS * CELL;

// Power-of-2 capacity enables bitwise AND in place of modulo inside RingDeque
const RING_CAP  = 512;
const RING_MASK = RING_CAP - 1;

const MIN_INTERVAL    = 55;  // ms — speed floor
const SPECIAL_TTL     = 70;  // ticks before special food vanishes
const COMBO_WINDOW    = 8;   // max tick gap between eats to continue a combo
const INPUT_QUEUE_MAX = 2;   // direction changes buffered ahead of steps
const SPECIAL_EVERY   = 5;   // spawn special food every N regular foods eaten

// Food circle geometry
const FOOD_R            = CELL_HALF - 2;        //  8
const FOOD_SHINE_OFFSET = FOOD_R * 0.28;        //  2.24
const FOOD_SHINE_R      = FOOD_R * 0.32;        //  2.56

/* ═══════════════════════════════════════════════════════════════
   Shared, frozen direction vectors (O(1) identity checks)
═══════════════════════════════════════════════════════════════ */
const D_UP    = Object.freeze({ x:  0, y: -1 });
const D_DOWN  = Object.freeze({ x:  0, y:  1 });
const D_LEFT  = Object.freeze({ x: -1, y:  0 });
const D_RIGHT = Object.freeze({ x:  1, y:  0 });

const DIR_MAP = {
  ArrowUp: D_UP,     w: D_UP,    W: D_UP,
  ArrowDown: D_DOWN, s: D_DOWN,  S: D_DOWN,
  ArrowLeft: D_LEFT, a: D_LEFT,  A: D_LEFT,
  ArrowRight: D_RIGHT, d: D_RIGHT, D: D_RIGHT,
};

const DPAD_MAP = { UP: D_UP, DOWN: D_DOWN, LEFT: D_LEFT, RIGHT: D_RIGHT };

// Integer cell key — |0 encourages V8 to represent the result as a Smi
const pos2key = (x, y) => (y * COLS + x) | 0;

/* ═══════════════════════════════════════════════════════════════
   Look-up Tables
═══════════════════════════════════════════════════════════════ */
// Body colors (31 strings built once at startup)
const BODY_COLORS = Object.freeze(
  Array.from({ length: 31 }, (_, i) => `rgb(70,${168 + i},83)`)
);

// Star trig look-up tables (Interleaved X and Y for spatial locality)
const STAR_COORDS = new Float64Array(20);
for (let i = 0; i < 10; i++) {
  const a = (Math.PI / 5) * i - Math.PI * 0.5;
  STAR_COORDS[i * 2]     = Math.cos(a);
  STAR_COORDS[i * 2 + 1] = Math.sin(a);
}

/* ═══════════════════════════════════════════════════════════════
   RingDeque — O(1) pushFront / popBack on typed arrays.
   Zero heap allocations during gameplay.
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
    this._size++;                  
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
   2-slot input ring (Scalar replacements for JS arrays)
═══════════════════════════════════════════════════════════════ */
let _iq0, _iq1, _iqLen = 0;

function enqueueDirection(d) {
  if (_iqLen >= INPUT_QUEUE_MAX) return;
  const ref = _iqLen === 0 ? direction : (_iqLen === 1 ? _iq0 : _iq1);
  if (d === ref || (d.x === -ref.x && d.y === -ref.y)) return; 
  if (_iqLen === 0) _iq0 = d; else _iq1 = d;
  _iqLen++;
}

/* ═══════════════════════════════════════════════════════════════
   State
═══════════════════════════════════════════════════════════════ */
const snake   = new RingDeque();
const bodyMap = new Uint8Array(TOTAL_CELLS); // Faster than JS Set: O(1) continuous memory

let direction;

// Reused food objects
const _foodObj        = { x: 0, y: 0 };
const _specialFoodObj = { x: 0, y: 0, ttl: 0 };
let food;        
let specialFood; 
let foodsEaten;

let score, highScore, level;
let combo, lastEatTick, tickCount;
let stepInterval, baseSpeed;

let rafId = 0, lastTimestamp, accumulator;
let gameState;   // 'idle' | 'running' | 'paused' | 'over' | 'dying'
let eatAnimTick;
let deathRafId = 0;

let _domScore = -1, _domBest = -1, _domLevel = -1;

/* ═══════════════════════════════════════════════════════════════
   Canvas Setup (with DPI Scaling for Retina Displays)
═══════════════════════════════════════════════════════════════ */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');
const dpr    = window.devicePixelRatio || 1;

canvas.style.width  = CW + 'px';
canvas.style.height = CH + 'px';
canvas.width  = Math.floor(CW * dpr);
canvas.height = Math.floor(CH * dpr);
ctx.scale(dpr, dpr);

/* ═══════════════════════════════════════════════════════════════
   Branchless roundRect polyfill
═══════════════════════════════════════════════════════════════ */
const fillRoundRect = typeof ctx.roundRect === 'function'
  ? function(x, y, w, h, r) {
      ctx.beginPath();
      ctx.roundRect(x, y, w, h, r);
      ctx.fill();
    }
  : function(x, y, w, h, r) {
      ctx.beginPath();
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
      ctx.fill();
    };

/* ═══════════════════════════════════════════════════════════════
   Offscreen grid renderer -> CSS Data URI blit override.
   Supports High DPI matching the main canvas.
═══════════════════════════════════════════════════════════════ */
(function buildGrid() {
  const gridCanvas  = document.createElement('canvas');
  gridCanvas.width  = Math.floor(CW * dpr);
  gridCanvas.height = Math.floor(CH * dpr);
  
  const gx = gridCanvas.getContext('2d');
  gx.scale(dpr, dpr);
  gx.strokeStyle = 'rgba(0,0,0,0.04)';
  gx.lineWidth   = 0.5;
  
  for (let c = 0; c <= COLS; c++) {
    gx.beginPath(); gx.moveTo(c * CELL, 0); gx.lineTo(c * CELL, CH); gx.stroke();
  }
  for (let r = 0; r <= ROWS; r++) {
    gx.beginPath(); gx.moveTo(0, r * CELL); gx.lineTo(CW, r * CELL); gx.stroke();
  }
  
  canvas.style.backgroundColor = '#fff';
  canvas.style.backgroundImage = `url(${gridCanvas.toDataURL()})`;
  canvas.style.backgroundSize  = `${CW}px ${CH}px`;
})();

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

baseSpeed = 150;
const diffBtns = document.querySelectorAll('.diff-btn');
diffBtns.forEach(function(btn) {
  btn.addEventListener('click', function() {
    diffBtns.forEach(function(b) { b.classList.remove('active'); });
    btn.classList.add('active');
    baseSpeed = parseInt(btn.dataset.speed, 10);
  });
});

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
      const isNewBest = score > highScore; 
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
═══════════════════════════════════════════════════════════════ */
function initGame() {
  const midX = COLS >> 1;
  const midY = ROWS >> 1;

  snake.reset();
  snake.pushFront(midX - 1, midY); 
  snake.pushFront(midX,     midY); 

  bodyMap.fill(0);
  bodyMap[pos2key(midX,     midY)] = 1;
  bodyMap[pos2key(midX - 1, midY)] = 1;

  direction = D_RIGHT;
  _iqLen    = 0; 

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
   Food spawning — Uint8Array evaluation
═══════════════════════════════════════════════════════════════ */
function spawnFood(isSpecial) {
  const otherFood = isSpecial ? food : specialFood;
  const otherKey  = otherFood ? pos2key(otherFood.x, otherFood.y) : -1;
  const freeCount = TOTAL_CELLS - snake.length - (otherKey >= 0 ? 1 : 0);
  if (freeCount <= 0) return;

  let x, y;

  if (freeCount < TOTAL_CELLS * 0.4) {
    // Dense: Algorithm R
    let seen = 0, chosen = -1;
    for (let k = 0; k < TOTAL_CELLS; k++) {
      if (bodyMap[k] === 0 && k !== otherKey) {
        if ((Math.random() * ++seen | 0) === 0) chosen = k;
      }
    }
    if (chosen < 0) return;
    x = chosen % COLS;
    y = chosen / COLS | 0;
  } else {
    // Sparse: 1x RNG projection loop avoids calling Math.random() twice per failure
    let k;
    do {
      k = Math.random() * TOTAL_CELLS | 0;
    } while (bodyMap[k] === 1 || k === otherKey);
    x = k % COLS;
    y = k / COLS | 0;
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
   Game step
═══════════════════════════════════════════════════════════════ */
function step() {
  tickCount++;

  if (_iqLen) {
    direction = _iq0;
    if (_iqLen === 2) _iq0 = _iq1;
    _iqLen--;
  }

  const hx = snake.headX() + direction.x;
  const hy = snake.headY() + direction.y;

  if (hx < 0 || hx >= COLS || hy < 0 || hy >= ROWS) { setState('dying'); return; }

  const tailKey = snake.tailKey();
  bodyMap[tailKey] = 0; 

  const headKey = pos2key(hx, hy);
  if (bodyMap[headKey] === 1) {
    bodyMap[tailKey] = 1; 
    setState('dying'); return;
  }

  snake.pushFront(hx, hy);
  bodyMap[headKey] = 1;

  let ate = false;

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

    if (!specialFood && foodsEaten % SPECIAL_EVERY === 0) spawnFood(true);
  }

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
    snake.popBack();
  } else {
    bodyMap[tailKey] = 1; 
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
   RAF loop
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
    if (gameState === 'running') draw(timestamp);
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
function draw(timestamp = 0, deathFlash = false) {
  // Clear uses logical size because of ctx.scale()
  ctx.clearRect(0, 0, CW, CH);

  if (food)        drawFoodCircle(food.x, food.y);
  if (specialFood) drawSpecialFood(specialFood.x, specialFood.y, timestamp, specialFood.ttl / SPECIAL_TTL);
  drawSnake(deathFlash);
}

function drawFoodCircle(col, row) {
  const cx = col * CELL + CELL_HALF;
  const cy = row * CELL + CELL_HALF;

  ctx.fillStyle = '#EA4335';
  ctx.beginPath(); ctx.arc(cx, cy, FOOD_R, 0, Math.PI * 2); ctx.fill();

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

  const prevAlpha = ctx.globalAlpha;
  ctx.globalAlpha = 0.35 + urgency * 0.65;
  ctx.fillStyle   = '#FBBC05';
  ctx.shadowColor = 'rgba(251,188,5,.8)';
  ctx.shadowBlur  = 8;

  ctx.beginPath();
  for (let i = 0; i < 10; i++) {
    const r  = i & 1 ? inner : outer;
    const sx = cx + STAR_COORDS[i * 2] * r;
    const sy = cy + STAR_COORDS[i * 2 + 1] * r;
    i ? ctx.lineTo(sx, sy) : ctx.moveTo(sx, sy);
  }
  ctx.closePath();
  ctx.fill();

  ctx.shadowBlur  = 0;
  ctx.shadowColor = 'transparent';
  ctx.globalAlpha = prevAlpha;
}

function drawSnake(deathFlash) {
  const headScale   = computeHeadScale();
  const len         = snake.length;
  const head        = snake._head;
  const xs          = snake._xs;
  const ys          = snake._ys;
  const colorFactor = 30 / len;
  const isScaled    = headScale !== 1;

  for (let i = 0; i < len; i++) {
    const idx = (head + i) & RING_MASK;
    const px  = xs[idx] * CELL + 1;
    const py  = ys[idx] * CELL + 1;

    if (deathFlash) {
      ctx.fillStyle = i === 0 ? '#EA4335' : '#f28b82';
    } else {
      ctx.fillStyle = i === 0 ? '#34A853' : BODY_COLORS[(i * colorFactor + 0.5) | 0];
    }

    if (i === 0) {
      if (isScaled) {
        ctx.save();
        ctx.translate(px + CELL_INNER_HALF, py + CELL_INNER_HALF);
        ctx.scale(headScale, headScale);
        ctx.translate(-(px + CELL_INNER_HALF), -(py + CELL_INNER_HALF));
        fillRoundRect(px, py, CELL_INNER, CELL_INNER, 6);
        ctx.restore();
      } else {
        fillRoundRect(px, py, CELL_INNER, CELL_INNER, 6);
      }
    } else {
      fillRoundRect(px, py, CELL_INNER, CELL_INNER, 4);
    }
  }

  if (!deathFlash) {
    drawEyes(xs[head] * CELL + CELL_HALF, ys[head] * CELL + CELL_HALF);
  }
}

function computeHeadScale() {
  const elapsed = tickCount - eatAnimTick;
  if (elapsed > 2) return 1;
  const t = Math.min(1, (accumulator / stepInterval + elapsed) / 3);
  return 1 + 0.28 * Math.sin(t * Math.PI);
}

function drawEyes(cx, cy) {
  const dx = direction.x;
  const dy = direction.y;

  let e1x, e1y, e2x, e2y;
  if      (dx ===  1) { e1x = cx + 4; e1y = cy - 3; e2x = cx + 4; e2y = cy + 3; }
  else if (dx === -1) { e1x = cx - 4; e1y = cy - 3; e2x = cx - 4; e2y = cy + 3; }
  else if (dy === -1) { e1x = cx - 3; e1y = cy - 4; e2x = cx + 3; e2y = cy - 4; }
  else                { e1x = cx - 3; e1y = cy + 4; e2x = cx + 3; e2y = cy + 4; }

  // Draw identical styles within a continuous path to minimize layout bounds calls
  ctx.fillStyle = '#fff';
  ctx.beginPath(); 
  ctx.arc(e1x, e1y, 2.5, 0, Math.PI * 2); 
  ctx.moveTo(e2x + 2.5, e2y);
  ctx.arc(e2x, e2y, 2.5, 0, Math.PI * 2); 
  ctx.fill();
  
  ctx.fillStyle = '#202124';
  ctx.beginPath(); 
  ctx.arc(e1x, e1y, 1.2, 0, Math.PI * 2); 
  ctx.moveTo(e2x + 1.2, e2y);
  ctx.arc(e2x, e2y, 1.2, 0, Math.PI * 2); 
  ctx.fill();
}

/* ═══════════════════════════════════════════════════════════════
   UI helpers
═══════════════════════════════════════════════════════════════ */
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
  
  // Calculate exact bounds right before injection to account for window scrolling
  const rect = canvas.getBoundingClientRect();
  
  el.className   = 'particle';
  el.textContent = text;
  el.style.left  = (rect.left + window.scrollX + col * CELL + CELL_HALF) + 'px';
  el.style.top   = (rect.top  + window.scrollY + row * CELL) + 'px';
  if (isCombo) el.style.color = '#FBBC05';
  
  document.body.appendChild(el);

  // Force DOM reflow to securely restart CSS animation
  scoreEl.classList.remove('pop');
  void scoreEl.offsetWidth; 
  scoreEl.classList.add('pop');

  // Safely cleanup DOM element (Fallback if 'animationend' fails due to background tab)
  const removeEl = () => { if (el.parentNode) el.remove(); };
  el.addEventListener('animationend', removeEl, { once: true });
  setTimeout(removeEl, 1000);
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
   Events
═══════════════════════════════════════════════════════════════ */
document.addEventListener('visibilitychange', function() {
  if (document.hidden && gameState === 'running') setState('paused');
});
window.addEventListener('blur', function() {
  if (gameState === 'running') setState('paused');
});

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

document.getElementById('startBtn').addEventListener('click', startGame);
document.getElementById('resumeBtn').addEventListener('click', function() { setState('running'); });
document.getElementById('retryBtn').addEventListener('click', startGame);
document.getElementById('restartFromPauseBtn').addEventListener('click', startGame);

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

/* Touch Events (Mobile Drag Optimization) */
let _txStart = 0, _tyStart = 0, _touching = false;

canvas.addEventListener('touchstart', function(e) {
  _txStart  = e.touches[0].clientX;
  _tyStart  = e.touches[0].clientY;
  _touching = true;
}, { passive: true });

// Prevent screen scrolling when swiping on the canvas
canvas.addEventListener('touchmove', function(e) {
  if (_touching) e.preventDefault();
}, { passive: false });

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
