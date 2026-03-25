/* ═══════════════════════════════════════════
   Constants
═══════════════════════════════════════════ */
const COLS = 20;
const ROWS = 20;
const CELL = 20;

const MIN_INTERVAL    = 55;  // hard floor regardless of level
const SPECIAL_TTL     = 70;  // ticks before special food disappears
const INPUT_QUEUE_MAX = 2;   // direction changes buffered ahead

/* ═══════════════════════════════════════════
   State
═══════════════════════════════════════════ */
let snake;          // Array<{x,y}>, index 0 = head
let bodySet;        // Set<string> of "x,y" for O(1) collision checks
let direction;      // current movement vector {x,y}
let inputQueue;     // buffered direction changes between steps

let food;           // {x, y}
let specialFood;    // {x, y, ttl} | null

let score;
let highScore;
let level;
let combo;          // consecutive-eat streak
let lastEatTick;    // tick when last food was eaten (combo window)
let tickCount;      // total steps since game start

let stepInterval;   // ms per step (shrinks as level rises)
let baseSpeed;      // player-chosen difficulty baseline in ms

let rafId;          // requestAnimationFrame handle
let lastTimestamp;  // previous rAF timestamp for delta calculation
let accumulator;    // time debt (ms) for fixed-timestep logic

let gameState;      // 'idle' | 'running' | 'paused' | 'over' | 'dying'
let eatAnimTick;    // tick when food was last eaten (head scale anim)
let deathFrame;     // rAF handle for death flash sequence

/* ═══════════════════════════════════════════
   Canvas
═══════════════════════════════════════════ */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');

/* ═══════════════════════════════════════════
   DOM references
═══════════════════════════════════════════ */
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

/* ═══════════════════════════════════════════
   Difficulty selector
═══════════════════════════════════════════ */
const diffBtns = document.querySelectorAll('.diff-btn');
baseSpeed = 150;

diffBtns.forEach(btn => {
  btn.addEventListener('click', () => {
    diffBtns.forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    baseSpeed = parseInt(btn.dataset.speed, 10);
  });
});

/* ═══════════════════════════════════════════
   Persistent high score
═══════════════════════════════════════════ */
highScore = parseInt(localStorage.getItem('snakeHighScore') || '0', 10);
highScoreEl.textContent = highScore;

/* ═══════════════════════════════════════════
   State machine — single entry point for all transitions
═══════════════════════════════════════════ */
function setState(next) {
  gameState = next;

  switch (next) {
    case 'idle':
      showScreen('start');
      break;

    case 'running':
      showScreen(null);
      // Reset timing so accumulated debt from paused state doesn't carry over
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

    case 'over':
      saveHighScore();
      finalScoreText.textContent = `Score: ${score}`;
      newBestText.classList.toggle('hidden', score <= 0 || score < highScore);
      showScreen('gameover');
      break;
  }
}

/* ═══════════════════════════════════════════
   Initialize / reset
═══════════════════════════════════════════ */
function initGame() {
  const midX = Math.floor(COLS / 2);
  const midY = Math.floor(ROWS / 2);

  snake      = [{ x: midX, y: midY }, { x: midX - 1, y: midY }];
  bodySet    = buildBodySet(snake);
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

  spawnFood();
  updateScoreUI();
}

/* Build a coordinate Set from the snake array for O(1) lookups */
function buildBodySet(arr) {
  const s = new Set();
  for (const seg of arr) s.add(`${seg.x},${seg.y}`);
  return s;
}

/* ═══════════════════════════════════════════
   Food spawning
   Uses reservoir sampling when the board is crowded (>60% full)
   to avoid pathological rejection-sampling spin loops.
═══════════════════════════════════════════ */
function spawnFood(isSpecial = false) {
  const totalCells = COLS * ROWS;
  const occupied   = snake.length + (food ? 1 : 0) + (specialFood ? 1 : 0);

  if (occupied > totalCells * 0.6) {
    // Collect all free cells explicitly then pick one at random
    const free = [];
    for (let y = 0; y < ROWS; y++) {
      for (let x = 0; x < COLS; x++) {
        if (!bodySet.has(`${x},${y}`)) free.push({ x, y });
      }
    }
    if (!free.length) return; // board completely full
    const pos = free[Math.floor(Math.random() * free.length)];
    isSpecial ? (specialFood = { ...pos, ttl: SPECIAL_TTL }) : (food = pos);
    return;
  }

  // Sparse board: rejection sampling is fast on average
  let pos;
  do {
    pos = { x: Math.floor(Math.random() * COLS), y: Math.floor(Math.random() * ROWS) };
  } while (bodySet.has(`${pos.x},${pos.y}`));

  isSpecial ? (specialFood = { ...pos, ttl: SPECIAL_TTL }) : (food = pos);
}

/* ═══════════════════════════════════════════
   Input queue
   Buffers up to INPUT_QUEUE_MAX direction changes between ticks
   so rapid corner inputs (e.g. right→down in quick succession) aren't dropped.
═══════════════════════════════════════════ */
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
  // Validate against the last queued dir (or current) to block 180° reversals and duplicates
  const ref = inputQueue.length ? inputQueue[inputQueue.length - 1] : direction;
  if (d.x === -ref.x && d.y === -ref.y) return;
  if (d.x ===  ref.x && d.y ===  ref.y) return;
  inputQueue.push(d);
}

/* ═══════════════════════════════════════════
   Game step — fixed-timestep logic tick
═══════════════════════════════════════════ */
function step() {
  tickCount++;

  // Consume the oldest queued direction input
  if (inputQueue.length) direction = inputQueue.shift();

  const head = {
    x: snake[0].x + direction.x,
    y: snake[0].y + direction.y,
  };

  // Wall collision
  if (head.x < 0 || head.x >= COLS || head.y < 0 || head.y >= ROWS) {
    setState('dying'); return;
  }

  // Self collision:
  // The tail vacates its cell this tick, so remove it from the set before checking.
  const tail = snake[snake.length - 1];
  bodySet.delete(`${tail.x},${tail.y}`);

  if (bodySet.has(`${head.x},${head.y}`)) {
    bodySet.add(`${tail.x},${tail.y}`); // restore for accurate death-flash render
    setState('dying'); return;
  }

  // Commit head movement
  snake.unshift(head);
  bodySet.add(`${head.x},${head.y}`);

  let ate = false;

  // Regular food
  if (head.x === food.x && head.y === food.y) {
    ate = true;
    eatAnimTick = tickCount;

    // Combo: each eat within 8 ticks of the previous one increments the streak
    combo = (tickCount - lastEatTick <= 8) ? combo + 1 : 1;
    lastEatTick = tickCount;

    const points = 10 * combo;
    score += points;
    showParticle(head, `+${points}`, combo > 1);
    spawnFood();

    // Trigger special food every 50 points earned
    if (!specialFood && score % 50 === 0) spawnFood(true);
  }

  // Special food
  if (specialFood && head.x === specialFood.x && head.y === specialFood.y) {
    ate = true;
    const points = 30 * Math.max(combo, 1);
    score += points;
    showParticle(head, `+${points}`, true);
    specialFood = null;
    combo++;
    lastEatTick = tickCount;
  }

  if (!ate) snake.pop(); // tail already removed from bodySet above

  // Decrement special food countdown
  if (specialFood) {
    specialFood.ttl--;
    if (specialFood.ttl <= 0) specialFood = null;
  }

  // Level up: interval shrinks by 8 ms per level, floors at MIN_INTERVAL
  const newLevel = Math.floor(score / 50) + 1;
  if (newLevel !== level) {
    level        = newLevel;
    stepInterval = Math.max(MIN_INTERVAL, baseSpeed - (level - 1) * 8);
  }

  updateScoreUI();
}

/* ═══════════════════════════════════════════
   RAF loop — drives rendering at display refresh rate,
   advances game logic in fixed-size steps to decouple
   visual frame rate from game speed.
═══════════════════════════════════════════ */
function rafLoop(timestamp) {
  rafId = requestAnimationFrame(rafLoop);

  if (gameState === 'running') {
    // Cap delta to 200 ms to avoid a spiral of death after tab focus loss
    const delta = Math.min(timestamp - lastTimestamp, 200);
    lastTimestamp = timestamp;
    accumulator  += delta;

    while (accumulator >= stepInterval) {
      step();
      accumulator -= stepInterval;
      if (gameState !== 'running') break;
    }
  } else {
    lastTimestamp = timestamp; // keep timestamp fresh during pause/idle
  }

  draw(timestamp);
}

/* ═══════════════════════════════════════════
   Death flash animation
   Alternates snake color between red and normal over ~600 ms.
═══════════════════════════════════════════ */
function runDeathAnimation() {
  let flashCount    = 0;
  const TOTAL_FLASH = 10;  // 5 on / 5 off
  const FLASH_MS    = 60;
  let prev          = performance.now();

  function frame(ts) {
    if (ts - prev >= FLASH_MS) {
      prev = ts;
      flashCount++;
      draw(ts, flashCount % 2 === 1); // odd frames = red
    }
    deathFrame = flashCount < TOTAL_FLASH
      ? requestAnimationFrame(frame)
      : (setState('over'), undefined);
  }

  deathFrame = requestAnimationFrame(frame);
}

/* ═══════════════════════════════════════════
   Rendering
═══════════════════════════════════════════ */
function draw(timestamp = 0, deathFlash = false) {
  const w = canvas.width;
  const h = canvas.height;

  ctx.clearRect(0, 0, w, h);
  ctx.fillStyle = '#fff';
  ctx.fillRect(0, 0, w, h);

  drawGrid(w, h);

  if (food) drawFoodCircle(food.x, food.y, '#EA4335', '#f28b82');
  if (specialFood) drawSpecialFood(specialFood.x, specialFood.y, timestamp, specialFood.ttl / SPECIAL_TTL);

  drawSnake(deathFlash, timestamp);
}

function drawGrid(w, h) {
  ctx.save();
  ctx.strokeStyle = 'rgba(0,0,0,0.04)';
  ctx.lineWidth   = 0.5;
  for (let c = 0; c <= COLS; c++) {
    ctx.beginPath(); ctx.moveTo(c * CELL, 0); ctx.lineTo(c * CELL, h); ctx.stroke();
  }
  for (let r = 0; r <= ROWS; r++) {
    ctx.beginPath(); ctx.moveTo(0, r * CELL); ctx.lineTo(w, r * CELL); ctx.stroke();
  }
  ctx.restore();
}

function drawSnake(deathFlash, timestamp) {
  const headScale = computeHeadScale();
  const len       = snake.length;

  for (let i = 0; i < len; i++) {
    const seg    = snake[i];
    const isHead = i === 0;
    const ratio  = i / len;

    const green = Math.round(168 + ratio * 30);
    let fillColor = isHead ? '#34A853' : `rgb(70,${green},83)`;
    if (deathFlash) fillColor = isHead ? '#EA4335' : '#f28b82';

    ctx.fillStyle = fillColor;

    const px = seg.x * CELL + 1;
    const py = seg.y * CELL + 1;
    const sz = CELL - 2;

    if (isHead && headScale !== 1) {
      ctx.save();
      ctx.translate(px + sz / 2, py + sz / 2);
      ctx.scale(headScale, headScale);
      ctx.translate(-(px + sz / 2), -(py + sz / 2));
      drawRoundRect(px, py, sz, sz, 6);
      ctx.restore();
    } else {
      drawRoundRect(px, py, sz, sz, isHead ? 6 : 4);
    }
  }

  if (!deathFlash) drawEyes(snake[0]);
}

/* Returns a scale factor >1 briefly after eating (head bounce effect) */
function computeHeadScale() {
  const elapsed = tickCount - eatAnimTick;
  if (elapsed > 2) return 1;
  // Interpolate within the current step for smoothness
  const t = Math.min(1, (accumulator / stepInterval + elapsed) / 3);
  return 1 + 0.28 * Math.sin(t * Math.PI);
}

/* Shared round-rect fill primitive */
function drawRoundRect(x, y, w, h, r) {
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
}

function drawFoodCircle(col, row, color, shine) {
  const cx = col * CELL + CELL / 2;
  const cy = row * CELL + CELL / 2;
  const r  = CELL / 2 - 2;

  ctx.fillStyle = color;
  ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();

  // Specular highlight
  ctx.fillStyle = shine;
  ctx.beginPath(); ctx.arc(cx - r * .28, cy - r * .28, r * .32, 0, Math.PI * 2); ctx.fill();
}

/* Special food: pulsing star that fades as its TTL expires */
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
    const px    = cx + Math.cos(angle) * r;
    const py    = cy + Math.sin(angle) * r;
    i === 0 ? ctx.moveTo(px, py) : ctx.lineTo(px, py);
  }
  ctx.closePath();
  ctx.fill();
  ctx.shadowBlur = 0;
  ctx.restore();
}

function drawEyes(head) {
  const cx = head.x * CELL + CELL / 2;
  const cy = head.y * CELL + CELL / 2;
  const d  = direction;

  const eyes =
    d.x ===  1 ? [{ x: cx + 4, y: cy - 3 }, { x: cx + 4, y: cy + 3 }] :
    d.x === -1 ? [{ x: cx - 4, y: cy - 3 }, { x: cx - 4, y: cy + 3 }] :
    d.y === -1 ? [{ x: cx - 3, y: cy - 4 }, { x: cx + 3, y: cy - 4 }] :
                 [{ x: cx - 3, y: cy + 4 }, { x: cx + 3, y: cy + 4 }];

  for (const e of eyes) {
    ctx.fillStyle = '#fff';
    ctx.beginPath(); ctx.arc(e.x, e.y, 2.5, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#202124';
    ctx.beginPath(); ctx.arc(e.x, e.y, 1.2, 0, Math.PI * 2); ctx.fill();
  }
}

/* ═══════════════════════════════════════════
   UI helpers
═══════════════════════════════════════════ */
function updateScoreUI() {
  scoreEl.textContent       = score;
  highScoreEl.textContent   = Math.max(score, highScore);
  levelEl.textContent       = level;
  headerScoreEl.textContent = score;
}

function saveHighScore() {
  if (score > highScore) {
    highScore = score;
    localStorage.setItem('snakeHighScore', highScore);
    highScoreEl.textContent = highScore;
  }
}

function showScreen(which) {
  startScreen.classList.add('hidden');
  pauseScreen.classList.add('hidden');
  gameOverScreen.classList.add('hidden');

  if (which === null) {
    overlay.classList.add('hidden');
  } else {
    overlay.classList.remove('hidden');
    const map = { start: startScreen, pause: pauseScreen, gameover: gameOverScreen };
    if (map[which]) map[which].classList.remove('hidden');
  }
}

/* Floating score particle at the head's canvas position */
function showParticle(seg, text, isCombo = false) {
  const rect = canvas.getBoundingClientRect();
  const el   = document.createElement('div');
  el.className   = 'particle';
  el.textContent = text;
  el.style.left  = `${rect.left + seg.x * CELL + CELL / 2}px`;
  el.style.top   = `${rect.top  + seg.y * CELL}px`;
  if (isCombo) el.style.color = '#FBBC05';
  document.body.appendChild(el);

  scoreEl.classList.remove('pop');
  void scoreEl.offsetWidth; // force reflow to restart animation
  scoreEl.classList.add('pop');

  el.addEventListener('animationend', () => el.remove(), { once: true });
}

/* ═══════════════════════════════════════════
   Game flow
═══════════════════════════════════════════ */
function startGame() {
  cancelAnimationFrame(deathFrame);
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

/* ═══════════════════════════════════════════
   Keyboard input
═══════════════════════════════════════════ */
document.addEventListener('keydown', e => {
  const SCROLL_KEYS = ['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', ' '];
  if (SCROLL_KEYS.includes(e.key)) e.preventDefault();

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

/* ═══════════════════════════════════════════
   Buttons
═══════════════════════════════════════════ */
document.getElementById('startBtn').addEventListener('click', startGame);
document.getElementById('resumeBtn').addEventListener('click', () => setState('running'));
document.getElementById('retryBtn').addEventListener('click', startGame);
document.getElementById('restartFromPauseBtn').addEventListener('click', startGame);

/* ═══════════════════════════════════════════
   Mobile: D-pad
═══════════════════════════════════════════ */
const DPAD_MAP = {
  UP:    { x: 0, y: -1 }, DOWN:  { x:  0, y: 1 },
  LEFT:  { x: -1, y: 0 }, RIGHT: { x:  1, y: 0 },
};

document.querySelectorAll('.dpad-btn[data-dir]').forEach(btn => {
  btn.addEventListener('pointerdown', e => {
    e.preventDefault(); // prevent ghost click after touch
    const d = DPAD_MAP[btn.dataset.dir];
    if (!d) return;
    if (gameState === 'idle')   { startGame(); return; }
    if (gameState === 'paused') setState('running');
    enqueueDirection(d);
  });
});

/* ═══════════════════════════════════════════
   Mobile: canvas swipe
═══════════════════════════════════════════ */
let touchOrigin = null;

canvas.addEventListener('touchstart', e => {
  touchOrigin = { x: e.touches[0].clientX, y: e.touches[0].clientY };
}, { passive: true });

canvas.addEventListener('touchend', e => {
  if (!touchOrigin) return;
  const dx = e.changedTouches[0].clientX - touchOrigin.x;
  const dy = e.changedTouches[0].clientY - touchOrigin.y;
  touchOrigin = null;

  if (Math.abs(dx) < 12 && Math.abs(dy) < 12) return; // ignore taps

  const d = Math.abs(dx) > Math.abs(dy)
    ? (dx > 0 ? DPAD_MAP.RIGHT : DPAD_MAP.LEFT)
    : (dy > 0 ? DPAD_MAP.DOWN  : DPAD_MAP.UP);

  if (gameState === 'idle')   { startGame(); return; }
  if (gameState === 'paused') setState('running');
  enqueueDirection(d);
}, { passive: true });

/* ═══════════════════════════════════════════
   Boot
═══════════════════════════════════════════ */
gameState = 'idle';
initGame();
draw(0);
showScreen('start');
// Start the RAF loop immediately so the start screen animates (star pulse etc.)
rafId = requestAnimationFrame(rafLoop);
