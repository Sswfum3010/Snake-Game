# Google-Style Snake Game 🐍

<div align="center">
  <img width="862" height="670" alt="20260401-142423" src="https://github.com/user-attachments/assets/350a520a-1af4-4880-a2e2-a8886c015279" />
</div>

A clean, responsive, and modern implementation of the classic Snake Game, inspired by the Google product UI. Built entirely with vanilla HTML5, CSS3, and JavaScript, this game offers a fun experience across both desktop and mobile devices.

## 📸 Overview

This project features a polished web interface with the classic Google logo styling and a dynamic HTML5 `<canvas>` rendering engine. The game is highly customizable and responsive, making it fully playable on mobile browsers using an interactive on-screen D-pad.

## ✨ Features

- **Google-Themed UI:** A sleek top navigation bar mimicking the familiar Google branding.
- **Three Difficulty Levels:** Choose your pace between Easy (150ms), Medium (100ms), and Hard (65ms).
- **Persistent High Scores:** Keeps track of your "Best" score locally in your browser using `localStorage`.
- **Level Progression:** Watch your level increase as you collect more food.
- **Responsive Design:** Includes an on-screen D-pad that appears automatically for touch-device users.
- **Overlay Screens:** Clean modal interfaces for the Start Menu, Pause Screen, and Game Over summary (with a "New Best!" celebration).
- **Smooth Keyboard Controls:** Support for both standard Arrow keys and WASD.

## 🎮 How to Play

### Controls
* **Desktop:**
  * **Movement:** `<kbd>W</kbd> <kbd>A</kbd> <kbd>S</kbd> <kbd>D</kbd>` or `<kbd>↑</kbd> <kbd>↓</kbd> <kbd>←</kbd> <kbd>→</kbd>`
  * **Pause:** `<kbd>P</kbd>`
  * **Start/Resume:** `<kbd>Space</kbd>`
* **Mobile/Touch:**
  * Use the on-screen **D-pad** located below the game canvas to navigate the snake.

### Gameplay
1. Select your preferred difficulty from the start screen.
2. Click **Play** (or press Space) to begin.
3. Guide the snake to eat the food (apples) on the board.
4. Each food eaten increases your score and occasionally your level.
5. Avoid running into the walls or your own tail, or it's Game Over!

## 🛠️ Technologies Used

* **HTML5:** Core structure and `<canvas>` rendering context.
* **CSS3:** Responsive styling, Google-themed UI, flexbox layouts, and custom overlay transitions. Fonts are imported via Google Fonts (Google Sans & Roboto Mono).
* **JavaScript (Vanilla):** Game loop mechanics, collision detection, input event listeners, DOM manipulation, and state management.

## 🚀 Running Locally

Since this is a vanilla frontend project with no build steps or dependencies, getting it running is incredibly simple:

1. **Clone the repository:**
   ```bash
   git clone https://github.com/Sswfum3010/Snake-Game.git
   ```
2. **Navigate to the directory:**
   ```bash
   cd Snake-Game
   ```
3. **Open the game:**
   Simply open the `index.html` file in your preferred web browser:
   - Double-click the file in your file explorer, OR
   - Run a local live server if you are using an editor like VS Code (via the "Live Server" extension).

## 📄 License

This project is licensed under the terms of the MIT License. See the [LICENSE](LICENSE) file for more details.
