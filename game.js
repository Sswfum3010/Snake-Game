/* ═══════════════════════════════════════════════════════════════
   Constants
═══════════════════════════════════════════════════════════════ */
const COLS           = 20;
const ROWS           = 20;
const CELL           = 20;
const TOTAL_CELLS    = COLS * ROWS;       // 400
const MIN_INTERVAL   = 55;               // ms — speed hard floor
const SPECIAL_TTL    = 70;               // ticks before special food vanishes
const COMBO_WINDOW   = 8;               // max ticks between eats for combo
const INPUT_QUEUE_MAX = 2;              // buffered direction changes

/* ═══════════════════════════════════════════════════════════════
   Ring Deque  ─  O(1) push_front / pop_back for the snake body.
   Replaces Array.unshift (O(n)) and Array.pop with index arithmetic.
   Capacity is TOTAL_CELLS + 1 to cover a fully-grown snake.
═══════════════════════════════════════════════════════════════ */
class RingDeque {
  constructor(capacity) {
    this._cap  = capacity;
    this._xs   = new Int16Array(capacity); // x coordinates
    this._ys   = new Int16Array(capacity); // y coordinates
    this._head = 0; // index of the logical front (snake head)
    this._size = 0;
  }

  get length() { return this._size; }

  // Insert a new element at the front (new snake head)
  pushFront(x, y) {
    this._head = (this._head - 1 + this._cap) % this._cap;
    this._xs[this._head] = x;
    this._ys[this._head] = y;
    this._size++;
  }

  // Remove the element at the back (old snake tail)
  popBack() {
    if (this._size > 0) this._size--;
  }

  // Read element at logical index i (0 = head)
  getX(i) { return this._xs[(this._head + i) % this._cap]; }
  getY(i) { return this._ys[(this._head + i) % this._cap]; }

  // Convenience accessors for head and tail
  headX() { return this._xs[this._head]; }
  headY() { return this._ys[this._head]; }
  tailX() { return this.getX(this._size - 1); }
  tailY() { return this.getY(this._size - 1); }
}

/* ═══════════════════════════════════════════════════════════════
   Integer coordinate encoding  ─  no string allocations per tick.
   Replaces Set<"x,y"> with Set<number>; V8 optimises integer sets.
═══════════════════════════════════════════════════════════════ */
const pos2key = (x, y) => y * COLS + x;

/* ═══════════════════════════════════════════════════════════════
   State
═══════════════════════════════════════════════════════════════ */
let snake;        // RingDeque  — current snake segments
let bodySet;      // Set<number> — occupied cells (integer keys)
let direction;    // {x, y} — active movement vector
let inputQueue;   // Array<{x,y}> — buffered direction inputs

let food;         // {x, y}
let specialFood;  // {x, y, ttl} | null

let score;
let highScore;
let level;
let combo;
let lastEatTick;
let tickCount;

let stepInterval; // ms per logic tick (decreases with level)
let baseSpeed;    // difficulty baseline chosen by the player

let rafId;        // handle for the main requestAnimationFrame loop
let lastTimestamp;
let accumulator;

let gameState;    // 'idle' | 'running' | 'paused' | 'over' | 'dying'
let eatAnimTick;  // tick of most recent food eat (head-bounce anim)
let deathRafId;   // rAF handle for death-flash sequence

// DOM-update dirty flags — avoid writing text nodes when values haven't changed
let _domScore = -1;
let _domBest  = -1;
let _domLevel = -1;

/* ═══════════════════════════════════════════════════════════════
   Canvas + offscreen grid
═══════════════════════════════════════════════════════════════ */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');

// Pre-render the static grid once into an offscreen canvas and blit each frame.
const gridCanvas    = document.createElement('canvas');
gridCanvas.width    = canvas.width;
gridCanvas.height   = canvas.height;
const gridCtx       = gridCanvas.getContext('2d');
(function buildGridCache() {
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
   roundRect shim  ─  use the native Canvas API (Chrome 99+, FF 112+,
   Safari 15.4+) and fall back to manual quadraticCurveTo only when
   the runtime lacks support.  Saves ~8 canvas calls per segment.
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
   getBoundingClientRect() triggers layout; we cache it and only
   invalidate when the canvas is actually resized.
═══════════════════════════════════════════════════════════════ */
let _canvasRect = canvas.getBoundingClientRect();
const _ro = new ResizeObserver(() => { _canvasRect = canvas.getBoundingClientRect(); });
_ro.observe(canvas);

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

/* ═══════════════════════════════════════════════════════════════
   Difficulty selector
═══════════════════════════════════════════════════════════════ */
baseSpeed = 150;
const diffBtns = document.querySelectorAll('.diff-btn');
diffBtns.forEach(btn => {
  btn.addEventListener('click', () => {
    diffBtns.forEach(b => b.classList.remove('active'));
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
   State machine  ─  single entry point for every state transition.
═══════════════════════════════════════════════════════════════ */
function setState(next) {
  gameState = next;

  switch (next) {
    case 'idle':
      showScreen('start');
      break;

    case 'running':
      showScreen(null);
      // Reset timing to prevent time debt from accumulating while paused
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
      // Capture new-best status before saveHighScore() updates the global
      const isNewBest = score > highScore;
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

  snake = new RingDeque(TOTAL_CELLS + 1);
  snake.pushFront(midX, midY);
  snake.pushFront(midX - 1, midY); // pushFront for second segment makes it the new head...
  // Rebuild: head first, then body behind it
  snake = new RingDeque(TOTAL_CELLS + 1);
  snake.pushFront(midX - 1, midY);
  snake.pushFront(midX, midY);     // head at index 0, body at index 1

  bodySet = new Set([pos2key(midX, midY), pos2key(midX - 1, midY)]);

  direction  = { x: 1, y: 0 };
  inputQueue = [];

  score        = 0;
  level        = 1;
  combo        = 0;
  lastEatTick  = -99;
  tickCount    = 0;
  eatAnimTick  = -99;
  specialFood  = null;
  stepInterval = baseSpeed;

  // Reset dirty flags so first updateScoreUI() always writes
  _domScore = -1;
  _domBest  = -1;
  _domLevel = -1;

  spawnFood();
  updateScoreUI();
}

/* ═══════════════════════════════════════════════════════════════
   Food spawning
   Excludes the snake body AND any existing food cell from candidates.
   Switches from rejection-sampling to an explicit free-list scan when
   the board exceeds 60% occupancy, preventing O(n) expected spin loops.
═══════════════════════════════════════════════════════════════ */
function spawnFood(isSpecial = false) {
  // Build the set of all cells that are off-limits for the new food
  const excluded = new Set(bodySet);
  if (food)        excluded.add(pos2key(food.x, food.y));
  if (specialFood) excluded.add(pos2key(specialFood.x, specialFood.y));

  const freeCount = TOTAL_CELLS - excluded.size;
  if (freeCount <= 0) return; // board is completely full

  let x, y;

  if (freeCount < TOTAL_CELLS * 0.4) {
    // Dense board: enumerate free cells, then pick one via reservoir sample
    let remaining = freeCount;
    let chosen    = -1;
    for (let k = 0; k < TOTAL_CELLS; k++) {
      if (!excluded.has(k)) {
        remaining--;
        // Reservoir sample: each free cell has equal probability
        if (Math.random() * (remaining + 1) < 1) chosen = k;
        if (remaining === 0) break;
      }
    }
    if (chosen === -1) return;
    x = chosen % COLS;
    y = Math.floor(chosen / COLS);
  } else {
    // Sparse board: rejection sampling converges in O(1) expected iterations
    do {
      x = Math.floor(Math.random() * COLS);
      y = Math.floor(Math.random() * ROWS);
    } while (excluded.has(pos2key(x, y)));
  }

  if (isSpecial) {
    specialFood = { x, y, ttl: SPECIAL_TTL };
  } else {
    food = { x, y };
  }
}

/* ═══════════════════════════════════════════════════════════════
   Input queue
   Validates new directions against the tail of the queue (or the
   current direction) to block 180° reversals and duplicate entries.
═══════════════════════════════════════════════════════════════ */
const DIR_MAP = {
  ArrowUp:    { x:  0, y: -1 },
  w:          { x:  0, y: -1 },
  ArrowDown:  { x:  0, y:  1 },
  s:          { x:  0, y:  1 },
  ArrowLeft:  { x: -1, y:  0 },
  a:          { x: -1, y:  0 },
  ArrowRight: { x:  1, y:  0 },
  d:          { x:  1, y:  0 },
};

function enqueueDirection(d) {
  if (inputQueue.length >= INPUT_QUEUE_MAX) return;
  const ref = inputQueue.length ? inputQueue[inputQueue.length - 1] : direction;
  if (d.x === -ref.x && d.y === -ref.y) return; // would reverse
  if (d.x ===  ref.x && d.y ===  ref.y) return; // duplicate
  inputQueue.push(d);
}

/* ═══════════════════════════════════════════════════════════════
   Game step  ─  one fixed-timestep logic tick
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

  // Self collision:
  // The tail vacates its cell this tick (it will be popped), so
  // temporarily remove it before checking the new head position.
  const tailKey = pos2key(snake.tailX(), snake.tailY());
  bodySet.delete(tailKey);

  const headKey = pos2key(hx, hy);
  if (bodySet.has(headKey)) {
    bodySet.add(tailKey); // restore tail so death flash renders correctly
    setState('dying'); return;
  }

  // Commit new head
  snake.pushFront(hx, hy);
  bodySet.add(headKey);

  let ate = false;

  // Regular food
  if (hx === food.x && hy === food.y) {
    ate         = true;
    eatAnimTick = tickCount;
    combo       = (tickCount - lastEatTick <= COMBO_WINDOW) ? combo + 1 : 1;
    lastEatTick = tickCount;

    const points = 10 * combo;
    score += points;
    showParticle(hx, hy, `+${points}`, combo > 1);
    spawnFood();

    if (!specialFood && score % 50 === 0) spawnFood(true);
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
    // Tail already removed from bodySet above; discard it from the deque
    snake.popBack();
  }

  // Tick special food countdown
  if (specialFood && --specialFood.ttl <= 0) specialFood = null;

  // Level progression
  const newLevel = Math.floor(score / 50) + 1;
  if (newLevel !== level) {
    level        = newLevel;
    stepInterval = Math.max(MIN_INTERVAL, baseSpeed - (level - 1) * 8);
  }

  updateScoreUI();
}

/* ═══════════════════════════════════════════════════════════════
   RAF loop  ─  fixed timestep with render each display frame.
   The accumulator decouples visual frame rate from game speed.
═══════════════════════════════════════════════════════════════ */
function rafLoop(timestamp) {
  rafId = requestAnimationFrame(rafLoop);

  if (gameState === 'running') {
    // Cap the spike to 200 ms to survive tab-restore surges
    const delta   = Math.min(timestamp - lastTimestamp, 200);
    lastTimestamp = timestamp;
    accumulator  += delta;

    while (accumulator >= stepInterval) {
      step();
      accumulator -= stepInterval;
      if (gameState !== 'running') break;
    }
  } else {
    lastTimestamp = timestamp;
  }

  draw(timestamp);
}

/* ═══════════════════════════════════════════════════════════════
   Death flash animation  ─  snake alternates red/green 5 times
   over ~600 ms before the game-over screen appears.
═══════════════════════════════════════════════════════════════ */
function runDeathAnimation() {
  let   flashes = 0;
  const TOTAL   = 10;   // 5 red + 5 normal
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

  // Blit the pre-rendered grid (single drawImage vs 82 canvas calls)
  ctx.drawImage(gridCanvas, 0, 0);

  if (food) drawFoodCircle(food.x, food.y);
  if (specialFood) drawSpecialFood(specialFood.x, specialFood.y, timestamp, specialFood.ttl / SPECIAL_TTL);

  drawSnake(deathFlash);
}

function drawFoodCircle(col, row) {
  const cx = col * CELL + CELL / 2;
  const cy = row * CELL + CELL / 2;
  const r  = CELL / 2 - 2;

  ctx.fillStyle = '#EA4335';
  ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();

  ctx.fillStyle = '#f28b82';
  ctx.beginPath(); ctx.arc(cx - r * .28, cy - r * .28, r * .32, 0, Math.PI * 2); ctx.fill();
}

function drawSpecialFood(col, row, timestamp, urgency) {
  const cx    = col * CELL + CELL / 2;
  const cy    = row * CELL + CELL / 2;
  const pulse = 0.85 + Math.sin(timestamp / 180) * 0.15;
  const outer = (CELL / 2 - 1) * pulse;
  const inner = outer * 0.42;

  ctx.save();
  ctx.globalAlpha = 0.35 + urgency * 0.65;
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

  for (let i = 0; i < len; i++) {
    const x = snake.getX(i);
    const y = snake.getY(i);

    const ratio = i / len;
    const green = Math.round(168 + ratio * 30);
    ctx.fillStyle = deathFlash
      ? (i === 0 ? '#EA4335' : '#f28b82')
      : (i === 0 ? '#34A853' : `rgb(70,${green},83)`);

    const px = x * CELL + 1;
    const py = y * CELL + 1;
    const sz = CELL - 2;
    const r  = i === 0 ? 6 : 4;

    if (i === 0 && headScale !== 1) {
      ctx.save();
      ctx.translate(px + sz / 2, py + sz / 2);
      ctx.scale(headScale, headScale);
      ctx.translate(-(px + sz / 2), -(py + sz / 2));
      fillRoundRect(px, py, sz, sz, r);
      ctx.restore();
    } else {
      fillRoundRect(px, py, sz, sz, r);
    }
  }

  if (!deathFlash) drawEyes();
}

// Smooth head-scale bounce after eating; interpolated within the current step
function computeHeadScale() {
  const elapsed = tickCount - eatAnimTick;
  if (elapsed > 2) return 1;
  const t = Math.min(1, (accumulator / stepInterval + elapsed) / 3);
  return 1 + 0.28 * Math.sin(t * Math.PI);
}

function drawEyes() {
  const cx = snake.headX() * CELL + CELL / 2;
  const cy = snake.headY() * CELL + CELL / 2;
  const d  = direction;

  const eyes =
    d.x ===  1 ? [[cx + 4, cy - 3], [cx + 4, cy + 3]] :
    d.x === -1 ? [[cx - 4, cy - 3], [cx - 4, cy + 3]] :
    d.y === -1 ? [[cx - 3, cy - 4], [cx + 3, cy - 4]] :
                 [[cx - 3, cy + 4], [cx + 3, cy + 4]];

  for (const [ex, ey] of eyes) {
    ctx.fillStyle = '#fff';
    ctx.beginPath(); ctx.arc(ex, ey, 2.5, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#202124';
    ctx.beginPath(); ctx.arc(ex, ey, 1.2, 0, Math.PI * 2); ctx.fill();
  }
}

/* ═══════════════════════════════════════════════════════════════
   UI helpers
═══════════════════════════════════════════════════════════════ */

// Dirty-flag DOM writes: only update a text node when its value changes.
function updateScoreUI() {
  const displayBest = Math.max(score, highScore);
  if (score       !== _domScore) { scoreEl.textContent = headerScoreEl.textContent = _domScore = score; }
  if (displayBest !== _domBest)  { highScoreEl.textContent = _domBest = displayBest; }
  if (level       !== _domLevel) { levelEl.textContent = _domLevel = level; }
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
  startScreen.classList.add('hidden');
  pauseScreen.classList.add('hidden');
  gameOverScreen.classList.add('hidden');

  if (which === null) {
    overlay.classList.add('hidden');
    return;
  }
  overlay.classList.remove('hidden');
  const panels = { start: startScreen, pause: pauseScreen, gameover: gameOverScreen };
  panels[which]?.classList.remove('hidden');
}

// Floating score particle; avoids layout reflow by using cached canvasRect.
function showParticle(col, row, text, isCombo = false) {
  const el = document.createElement('div');
  el.className   = 'particle';
  el.textContent = text;
  el.style.left  = `${_canvasRect.left + col * CELL + CELL / 2}px`;
  el.style.top   = `${_canvasRect.top  + row * CELL}px`;
  if (isCombo) el.style.color = '#FBBC05';
  document.body.appendChild(el);

  // Restart score-pop CSS animation without forcing a layout reflow.
  // Removing the class in one rAF and adding it in the next lets the browser
  // process the style change between frames rather than forcing offsetWidth.
  scoreEl.classList.remove('pop');
  requestAnimationFrame(() => scoreEl.classList.add('pop'));

  el.addEventListener('animationend', () => el.remove(), { once: true });
}

/* ═══════════════════════════════════════════════════════════════
   Game flow
═══════════════════════════════════════════════════════════════ */
function startGame() {
  cancelAnimationFrame(deathRafId);
  initGame();
  lastTimestamp = performance.now();
  accumulator   = 0;
  if (!rafId) rafId = requestAnimationFrame(rafLoop);
  setState('running');
}

function togglePause() {
  if (gameState === 'running') setState('paused');
  else if (gameState === 'paused') setState('running');
}

/* ═══════════════════════════════════════════════════════════════
   Auto-pause on tab switch or window blur
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
   Mobile: D-pad  (pointerdown for instant response; prevents ghost click)
═══════════════════════════════════════════════════════════════ */
const DPAD_MAP = {
  UP:    { x:  0, y: -1 }, DOWN:  { x: 0, y: 1 },
  LEFT:  { x: -1, y:  0 }, RIGHT: { x: 1, y: 0 },
};

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
═══════════════════════════════════════════════════════════════ */
let _touchOrigin = null;

canvas.addEventListener('touchstart', e => {
  _touchOrigin = { x: e.touches[0].clientX, y: e.touches[0].clientY };
}, { passive: true });

canvas.addEventListener('touchend', e => {
  if (!_touchOrigin) return;
  const dx = e.changedTouches[0].clientX - _touchOrigin.x;
  const dy = e.changedTouches[0].clientY - _touchOrigin.y;
  _touchOrigin = null;

  if (Math.abs(dx) < 12 && Math.abs(dy) < 12) return;

  const d = Math.abs(dx) > Math.abs(dy)
    ? (dx > 0 ? DPAD_MAP.RIGHT : DPAD_MAP.LEFT)
    : (dy > 0 ? DPAD_MAP.DOWN  : DPAD_MAP.UP);

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
rafId = requestAnimationFrame(rafLoop); // animate the start screen (star pulse, etc.)
