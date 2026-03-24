/* ── Constants ── */
const COLS = 20;
const ROWS = 20;
const CELL = 20; // pixels per grid cell

/* ── State ── */
let snake, direction, nextDirection, food, specialFood;
let score, highScore, level;
let gameLoop, speed;
let gameState; // 'idle' | 'running' | 'paused' | 'over'

/* ── Canvas ── */
const canvas = document.getElementById('gameCanvas');
const ctx    = canvas.getContext('2d');

/* ── UI elements ── */
const overlay         = document.getElementById('overlay');
const startScreen     = document.getElementById('startScreen');
const pauseScreen     = document.getElementById('pauseScreen');
const gameOverScreen  = document.getElementById('gameOverScreen');
const scoreEl         = document.getElementById('score');
const highScoreEl     = document.getElementById('highScore');
const levelEl         = document.getElementById('level');
const headerScoreEl   = document.getElementById('headerScore');
const finalScoreText  = document.getElementById('finalScoreText');
const newBestText     = document.getElementById('newBestText');

/* ── Difficulty buttons ── */
const diffBtns = document.querySelectorAll('.diff-btn');
diffBtns.forEach(btn => {
  btn.addEventListener('click', () => {
    diffBtns.forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    speed = parseInt(btn.dataset.speed, 10);
  });
});
speed = 150; // default: Easy

/* ── Persist high score in localStorage ── */
highScore = parseInt(localStorage.getItem('snakeHighScore') || '0', 10);
highScoreEl.textContent = highScore;

/* ── Spawn food at a random empty cell ── */
function spawnFood(isSpecial = false) {
  let pos;
  do {
    pos = {
      x: Math.floor(Math.random() * COLS),
      y: Math.floor(Math.random() * ROWS)
    };
  } while (snake.some(s => s.x === pos.x && s.y === pos.y));

  if (isSpecial) {
    specialFood = { ...pos, ttl: 60 }; // disappears after 60 ticks
  } else {
    food = pos;
  }
}

/* ── Initialize / reset game state ── */
function initGame() {
  const midX = Math.floor(COLS / 2);
  const midY = Math.floor(ROWS / 2);

  snake         = [{ x: midX, y: midY }, { x: midX - 1, y: midY }];
  direction     = { x: 1, y: 0 };
  nextDirection = { x: 1, y: 0 };
  score         = 0;
  level         = 1;
  specialFood   = null;

  spawnFood();
  updateScoreUI();
}

/* ── Move snake one step ── */
function step() {
  direction = nextDirection;

  const head = {
    x: snake[0].x + direction.x,
    y: snake[0].y + direction.y
  };

  // Wall collision
  if (head.x < 0 || head.x >= COLS || head.y < 0 || head.y >= ROWS) {
    endGame(); return;
  }

  // Self collision
  if (snake.some(s => s.x === head.x && s.y === head.y)) {
    endGame(); return;
  }

  snake.unshift(head);

  let ate = false;

  // Check regular food
  if (head.x === food.x && head.y === food.y) {
    score += 10;
    ate = true;
    spawnFood();
    showParticle(head, '+10');

    // Spawn a special food every 5 regular foods
    if (score % 50 === 0 && !specialFood) spawnFood(true);
  }

  // Check special food
  if (specialFood && head.x === specialFood.x && head.y === specialFood.y) {
    score += 30;
    ate = true;
    specialFood = null;
    showParticle(head, '+30');
  }

  if (!ate) snake.pop();

  // Tick special food TTL
  if (specialFood) {
    specialFood.ttl--;
    if (specialFood.ttl <= 0) specialFood = null;
  }

  // Level up every 50 points
  const newLevel = Math.floor(score / 50) + 1;
  if (newLevel !== level) {
    level = newLevel;
    // Gradually increase speed by reducing interval
    const boostSpeed = Math.max(55, speed - (level - 1) * 8);
    clearInterval(gameLoop);
    gameLoop = setInterval(tick, boostSpeed);
  }

  updateScoreUI();
  draw();
}

/* ── Main tick (called by setInterval) ── */
function tick() {
  if (gameState === 'running') step();
}

/* ── Draw everything ── */
function draw() {
  const w = canvas.width;
  const h = canvas.height;

  // Background
  ctx.fillStyle = '#fff';
  ctx.fillRect(0, 0, w, h);

  // Grid lines
  ctx.strokeStyle = 'rgba(0,0,0,0.04)';
  ctx.lineWidth = 0.5;
  for (let c = 0; c <= COLS; c++) {
    ctx.beginPath();
    ctx.moveTo(c * CELL, 0);
    ctx.lineTo(c * CELL, h);
    ctx.stroke();
  }
  for (let r = 0; r <= ROWS; r++) {
    ctx.beginPath();
    ctx.moveTo(0, r * CELL);
    ctx.lineTo(w, r * CELL);
    ctx.stroke();
  }

  // Regular food — red circle with shine
  drawFood(food.x, food.y, '#EA4335', '#f28b82');

  // Special food — yellow star
  if (specialFood) {
    const pulse = 0.85 + Math.sin(Date.now() / 180) * 0.15;
    drawStar(specialFood.x, specialFood.y, pulse);
  }

  // Snake body segments
  snake.forEach((seg, i) => {
    const ratio = i / snake.length;
    // Gradient: head is vivid green, tail fades slightly
    const g = Math.round(168 + ratio * 30);
    ctx.fillStyle = i === 0 ? '#34A853' : `rgb(70,${g},83)`;
    drawRoundRect(seg.x * CELL + 1, seg.y * CELL + 1, CELL - 2, CELL - 2, i === 0 ? 6 : 4);
  });

  // Eyes on the head
  drawEyes(snake[0]);
}

/* ── Round rect helper ── */
function drawRoundRect(x, y, w, h, r) {
  ctx.beginPath();
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
  ctx.fill();
}

/* ── Draw food circle ── */
function drawFood(col, row, color, shine) {
  const cx = col * CELL + CELL / 2;
  const cy = row * CELL + CELL / 2;
  const r  = CELL / 2 - 2;

  ctx.fillStyle = color;
  ctx.beginPath();
  ctx.arc(cx, cy, r, 0, Math.PI * 2);
  ctx.fill();

  // Shine highlight
  ctx.fillStyle = shine;
  ctx.beginPath();
  ctx.arc(cx - r * .28, cy - r * .28, r * .32, 0, Math.PI * 2);
  ctx.fill();
}

/* ── Draw 5-point star for special food ── */
function drawStar(col, row, scale = 1) {
  const cx = col * CELL + CELL / 2;
  const cy = row * CELL + CELL / 2;
  const outerR = (CELL / 2 - 1) * scale;
  const innerR = outerR * 0.42;
  const points = 5;

  ctx.fillStyle = '#FBBC05';
  ctx.shadowColor = 'rgba(251,188,5,.6)';
  ctx.shadowBlur  = 6;
  ctx.beginPath();
  for (let i = 0; i < points * 2; i++) {
    const angle = (Math.PI / points) * i - Math.PI / 2;
    const r = i % 2 === 0 ? outerR : innerR;
    const px = cx + Math.cos(angle) * r;
    const py = cy + Math.sin(angle) * r;
    i === 0 ? ctx.moveTo(px, py) : ctx.lineTo(px, py);
  }
  ctx.closePath();
  ctx.fill();
  ctx.shadowBlur = 0;
}

/* ── Draw eyes on snake head ── */
function drawEyes(head) {
  const cx = head.x * CELL + CELL / 2;
  const cy = head.y * CELL + CELL / 2;

  // Eye offsets depend on movement direction
  let eye1, eye2;
  const d = direction;

  if (d.x === 1) {
    eye1 = { x: cx + 4, y: cy - 3 };
    eye2 = { x: cx + 4, y: cy + 3 };
  } else if (d.x === -1) {
    eye1 = { x: cx - 4, y: cy - 3 };
    eye2 = { x: cx - 4, y: cy + 3 };
  } else if (d.y === -1) {
    eye1 = { x: cx - 3, y: cy - 4 };
    eye2 = { x: cx + 3, y: cy - 4 };
  } else {
    eye1 = { x: cx - 3, y: cy + 4 };
    eye2 = { x: cx + 3, y: cy + 4 };
  }

  [eye1, eye2].forEach(e => {
    ctx.fillStyle = '#fff';
    ctx.beginPath();
    ctx.arc(e.x, e.y, 2.5, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillStyle = '#202124';
    ctx.beginPath();
    ctx.arc(e.x, e.y, 1.2, 0, Math.PI * 2);
    ctx.fill();
  });
}

/* ── Update all score-related DOM elements ── */
function updateScoreUI() {
  scoreEl.textContent       = score;
  highScoreEl.textContent   = Math.max(score, highScore);
  levelEl.textContent       = level;
  headerScoreEl.textContent = score;
}

/* ── Floating +points particle ── */
function showParticle(seg, text) {
  const rect  = canvas.getBoundingClientRect();
  const el    = document.createElement('div');
  el.className     = 'particle';
  el.textContent   = text;
  el.style.left    = `${rect.left + seg.x * CELL + CELL / 2}px`;
  el.style.top     = `${rect.top  + seg.y * CELL}px`;
  document.body.appendChild(el);

  // Animate score display
  scoreEl.classList.remove('pop');
  void scoreEl.offsetWidth; // reflow
  scoreEl.classList.add('pop');

  el.addEventListener('animationend', () => el.remove());
}

/* ── Start game ── */
function startGame() {
  initGame();
  showScreen(null);
  gameState = 'running';
  gameLoop  = setInterval(tick, speed);
  draw();
}

/* ── Pause / resume ── */
function togglePause() {
  if (gameState === 'running') {
    gameState = 'paused';
    showScreen('pause');
  } else if (gameState === 'paused') {
    resumeGame();
  }
}

function resumeGame() {
  if (gameState !== 'paused') return;
  showScreen(null);
  gameState = 'running';
}

/* ── End game ── */
function endGame() {
  clearInterval(gameLoop);
  gameState = 'over';

  const isNewBest = score > highScore;
  if (isNewBest) {
    highScore = score;
    localStorage.setItem('snakeHighScore', highScore);
    highScoreEl.textContent = highScore;
  }

  finalScoreText.textContent = `Score: ${score}`;
  newBestText.classList.toggle('hidden', !isNewBest);
  showScreen('gameover');
}

/* ── Show the right overlay panel ── */
function showScreen(which) {
  startScreen.classList.add('hidden');
  pauseScreen.classList.add('hidden');
  gameOverScreen.classList.add('hidden');

  if (which === null) {
    overlay.classList.add('hidden');
  } else {
    overlay.classList.remove('hidden');
    if (which === 'start')    startScreen.classList.remove('hidden');
    if (which === 'pause')    pauseScreen.classList.remove('hidden');
    if (which === 'gameover') gameOverScreen.classList.remove('hidden');
  }
}

/* ── Keyboard input ── */
document.addEventListener('keydown', e => {
  const key = e.key;

  // Prevent page scroll on arrow keys
  if (['ArrowUp','ArrowDown','ArrowLeft','ArrowRight',' '].includes(key)) {
    e.preventDefault();
  }

  // Direction map: disallow 180° reversal
  const dirs = {
    ArrowUp:    { x:  0, y: -1 },
    w:          { x:  0, y: -1 },
    ArrowDown:  { x:  0, y:  1 },
    s:          { x:  0, y:  1 },
    ArrowLeft:  { x: -1, y:  0 },
    a:          { x: -1, y:  0 },
    ArrowRight: { x:  1, y:  0 },
    d:          { x:  1, y:  0 },
  };

  if (dirs[key]) {
    const d = dirs[key];
    // Block 180° reversal
    if (d.x !== -direction.x || d.y !== -direction.y) {
      nextDirection = d;
    }
    return;
  }

  // Pause
  if (key === 'p' || key === 'P') { togglePause(); return; }

  // Space: start or resume
  if (key === ' ') {
    if (gameState === 'idle')   { startGame();   return; }
    if (gameState === 'paused') { resumeGame();  return; }
  }
});

/* ── Button event listeners ── */
document.getElementById('startBtn').addEventListener('click', startGame);
document.getElementById('resumeBtn').addEventListener('click', resumeGame);
document.getElementById('retryBtn').addEventListener('click', startGame);
document.getElementById('restartFromPauseBtn').addEventListener('click', startGame);

/* ── Mobile D-pad ── */
document.querySelectorAll('.dpad-btn[data-dir]').forEach(btn => {
  btn.addEventListener('click', () => {
    const map = {
      UP:    { x:  0, y: -1 },
      DOWN:  { x:  0, y:  1 },
      LEFT:  { x: -1, y:  0 },
      RIGHT: { x:  1, y:  0 },
    };
    const d = map[btn.dataset.dir];
    if (d && (d.x !== -direction.x || d.y !== -direction.y)) {
      nextDirection = d;
    }
    // If idle or paused, start / resume on first tap
    if (gameState === 'idle')   startGame();
    if (gameState === 'paused') resumeGame();
  });
});

/* ── Swipe support for mobile ── */
let touchStart = null;
canvas.addEventListener('touchstart', e => {
  touchStart = { x: e.touches[0].clientX, y: e.touches[0].clientY };
}, { passive: true });

canvas.addEventListener('touchend', e => {
  if (!touchStart) return;
  const dx = e.changedTouches[0].clientX - touchStart.x;
  const dy = e.changedTouches[0].clientY - touchStart.y;
  if (Math.abs(dx) < 10 && Math.abs(dy) < 10) return; // ignore taps

  let d;
  if (Math.abs(dx) > Math.abs(dy)) {
    d = dx > 0 ? { x: 1, y: 0 } : { x: -1, y: 0 };
  } else {
    d = dy > 0 ? { x: 0, y: 1 } : { x: 0, y: -1 };
  }
  if (d.x !== -direction.x || d.y !== -direction.y) nextDirection = d;
  touchStart = null;
}, { passive: true });

/* ── Animate special food even when snake hasn't moved ── */
function animateSpecial() {
  if (gameState === 'running' && specialFood) draw();
  requestAnimationFrame(animateSpecial);
}
requestAnimationFrame(animateSpecial);

/* ── Init ── */
gameState = 'idle';
initGame();
draw();
showScreen('start');
