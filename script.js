

const ENTITIES = [
  { id: 'farmer', name: 'Farmer', index: 0 },
  { id: 'fox', name: 'Fox', index: 1 },
  { id: 'goose', name: 'Goose', index: 2 },
  { id: 'beans', name: 'Beans', index: 3 }
];

const INITIAL_STATE = [0, 0, 0, 0];
const GOAL_STATE = [1, 1, 1, 1];

// --- 2. APPLICATION RUNTIME STATE ---

let currentState = [...INITIAL_STATE];
let crossingCount = 0;
let isGameActive = false;
let isGameOverUnsafe = false;
let lastActionTaken = "Initial state: All entities are waiting on the Left Bank.";
let inTransitItem = null;

let bfsSolution = null;
let currentStepIndex = 0;
let autoPlayInterval = null;

// --- 3. DOM ELEMENT REFERENCES ---

const elStateDisplay = document.getElementById('state-display');
const elCrossingCount = document.getElementById('crossing-count');
const elSafetyIndicator = document.getElementById('safety-indicator');
const elGoalIndicator = document.getElementById('goal-indicator');
const elStatusMessage = document.getElementById('status-message');
const elGameStatusPill = document.getElementById('game-status-pill');

const elLeftEntities = document.getElementById('left-entities');
const elRightEntities = document.getElementById('right-entities');
const elLeftCountTag = document.getElementById('left-count-tag');
const elRightCountTag = document.getElementById('right-count-tag');
const elBoat = document.getElementById('boat');
const elBoatOccupants = document.getElementById('boat-occupants');

const elBtnStart = document.getElementById('btn-start');
const elBtnMoveAlone = document.getElementById('btn-move-alone');
const elBtnTakeFox = document.getElementById('btn-take-fox');
const elBtnTakeGoose = document.getElementById('btn-take-goose');
const elBtnTakeBeans = document.getElementById('btn-take-beans');
const elBtnReset = document.getElementById('btn-reset');

const elBtnSolveBfs = document.getElementById('btn-solve-bfs');
const elBtnPrevStep = document.getElementById('btn-prev-step');
const elBtnNextStep = document.getElementById('btn-next-step');
const elBtnAutoPlay = document.getElementById('btn-auto-play');

const elSolutionList = document.getElementById('solution-list');
const elBfsSummaryTag = document.getElementById('bfs-summary-tag');
const elMetricExplored = document.getElementById('metric-explored');
const elMetricVisited = document.getElementById('metric-visited');
const elMetricCrossings = document.getElementById('metric-crossings');

// --- 4. CORE AI LOGIC: STATE SAFETY & RULE-BASED PLANNING ---

function isSafeState(state) {
  const [F, X, G, B] = state;

  if (F === G) {
    return true;
  }

  if (X === G) {
    return false;
  }

  if (G === B) {
    return false;
  }

  return true;
}

function getUnsafeReason(state) {
  const [F, X, G, B] = state;

  if (F !== G) {
    const unsupervisedBank = G === 0 ? "Left Bank" : "Right Bank";

    if (X === G && G === B) {
      return `Critical failure on the ${unsupervisedBank}: The Farmer left the Fox, Goose, and Beans unsupervised! The Fox ate the Goose, and the Goose ate the Beans!`;
    }

    if (X === G) {
      return `Predator conflict on the ${unsupervisedBank}: The Farmer left the Fox and Goose unsupervised! The Fox ate the Goose!`;
    }

    if (G === B) {
      return `Food conflict on the ${unsupervisedBank}: The Farmer left the Goose and Beans unsupervised! The Goose ate the Beans!`;
    }
  }

  return null;
}

function getSafeExplanation(state, actionName) {
  const [F, X, G, B] = state;

  if (isGoal(state)) {
    return "Goal state reached! All four entities have crossed safely to the Right Bank.";
  }

  if (F === 0 && X === 0 && G === 0 && B === 0) {
    return "Initial configuration: All entities are resting safely on the Left Bank.";
  }

  if (F === G) {
    return "Safe: The Farmer is present with the Goose, preventing any harm from occurring.";
  }

  const gooseBank = G === 0 ? "Left Bank" : "Right Bank";
  const foxBeansBank = X === 0 ? "Left Bank" : "Right Bank";

  return `Safe: The Goose is alone on the ${gooseBank}, and the Fox and Beans are on the ${foxBeansBank} (foxes do not eat beans).`;
}

function isGoal(state) {
  return state[0] === 1 &&
         state[1] === 1 &&
         state[2] === 1 &&
         state[3] === 1;
}

function stateToKey(state) {
  return state.join(',');
}

// --- 5. SUCCESSOR STATE GENERATION ---

function getValidSuccessors(state) {
  const [F, X, G, B] = state;
  const newF = 1 - F;
  const targetBankName = newF === 1 ? "Right Bank" : "Left Bank";
  const successors = [];

  // Farmer takes Goose
  if (G === F) {
    const nextState = [newF, X, 1 - G, B];

    if (isSafeState(nextState)) {
      successors.push({
        state: nextState,
        action: `Farmer takes Goose to ${targetBankName}`,
        itemIndex: 2,
        explanation: getSafeExplanation(nextState, "Farmer takes Goose")
      });
    }
  }

  // Farmer takes Fox
  if (X === F) {
    const nextState = [newF, 1 - X, G, B];

    if (isSafeState(nextState)) {
      successors.push({
        state: nextState,
        action: `Farmer takes Fox to ${targetBankName}`,
        itemIndex: 1,
        explanation: getSafeExplanation(nextState, "Farmer takes Fox")
      });
    }
  }

  // Farmer takes Beans
  if (B === F) {
    const nextState = [newF, X, G, 1 - B];

    if (isSafeState(nextState)) {
      successors.push({
        state: nextState,
        action: `Farmer takes Beans to ${targetBankName}`,
        itemIndex: 3,
        explanation: getSafeExplanation(nextState, "Farmer takes Beans")
      });
    }
  }

  // Farmer crosses alone
  const aloneState = [newF, X, G, B];

  if (isSafeState(aloneState)) {
    successors.push({
      state: aloneState,
      action: `Farmer returns alone to ${targetBankName}`,
      itemIndex: null,
      explanation: getSafeExplanation(aloneState, "Farmer crosses alone")
    });
  }

  return successors;
}

// --- 6. BREADTH-FIRST SEARCH (BFS) ALGORITHM ---

function runBreadthFirstSearch() {
  const rootNode = {
    state: [...INITIAL_STATE],
    path: [{
      stepNumber: 0,
      state: [...INITIAL_STATE],
      action: "Initial State: All entities on Left Bank",
      explanation: "Safe: Everyone starts securely on the Left Bank.",
      itemIndex: null
    }]
  };

  const queue = [rootNode];

  const visited = new Set();
  visited.add(stateToKey(INITIAL_STATE));

  let exploredCount = 0;

  while (queue.length > 0) {
    const currentNode = queue.shift();
    exploredCount++;

    const currentState = currentNode.state;

    if (isGoal(currentState)) {
      return {
        path: currentNode.path,
        exploredCount: exploredCount,
        visitedCount: visited.size
      };
    }

    const successors = getValidSuccessors(currentState);

    for (let i = 0; i < successors.length; i++) {
      const succ = successors[i];
      const succKey = stateToKey(succ.state);

      if (!visited.has(succKey)) {
        visited.add(succKey);

        const newPath = [
          ...currentNode.path,
          {
            stepNumber: currentNode.path.length,
            state: succ.state,
            action: succ.action,
            explanation: succ.explanation,
            itemIndex: succ.itemIndex
          }
        ];

        queue.push({
          state: succ.state,
          path: newPath
        });
      }
    }
  }

  return null;
}

// --- 7. USER INTERFACE RENDERING ---
function render() {
  const [F, X, G, B] = currentState;

  elStateDisplay.textContent = `(${F}, ${X}, ${G}, ${B})`;
  elCrossingCount.textContent = crossingCount;

  elLeftEntities.innerHTML = '';
  elRightEntities.innerHTML = '';
  elBoatOccupants.innerHTML = '';

  let leftCount = 0;
  let rightCount = 0;

  // Display entities without emojis
  ENTITIES.forEach(entity => {
    const pos = currentState[entity.index];

    const card = document.createElement('div');
    card.className = 'entity-card';
    card.id = `entity-${entity.id}`;

    card.innerHTML = `
      <div class="entity-name">${entity.name}</div>
      <div class="entity-state-tag">
        ${pos === 0 ? 'Left (0)' : 'Right (1)'}
      </div>
    `;

    if (pos === 0) {
      elLeftEntities.appendChild(card);
      leftCount++;
    } else {
      elRightEntities.appendChild(card);
      rightCount++;
    }
  });

  // Empty bank placeholders
  if (leftCount === 0) {
    elLeftEntities.innerHTML =
      '<div class="empty-bank-text">All entities have crossed!</div>';
  }

  if (rightCount === 0) {
    elRightEntities.innerHTML =
      '<div class="empty-bank-text">Bank is currently empty.</div>';
  }

  elLeftCountTag.textContent = `${leftCount} Entities`;
  elRightCountTag.textContent = `${rightCount} Entities`;

  // Position the boat
  if (F === 0) {
    elBoat.className = 'boat boat-left';
  } else {
    elBoat.className = 'boat boat-right';
  }

  // Display Farmer inside boat without emoji
  const farmerOccupant = document.createElement('span');
  farmerOccupant.className = 'boat-occupant-badge';
  farmerOccupant.title = 'Farmer';
  farmerOccupant.textContent = 'Farmer';
  elBoatOccupants.appendChild(farmerOccupant);

  // Display carried item without emoji
  if (inTransitItem !== null) {
    const itemEntity = ENTITIES[inTransitItem];

    const itemOccupant = document.createElement('span');
    itemOccupant.className = 'boat-occupant-badge';
    itemOccupant.title = itemEntity.name;
    itemOccupant.textContent = itemEntity.name;

    elBoatOccupants.appendChild(itemOccupant);
  }

  // Safety and goal evaluation
  const safe = isSafeState(currentState);
  const goalAchieved = isGoal(currentState);

  if (safe) {
    elSafetyIndicator.textContent = "Safe State";
    elSafetyIndicator.className = "dash-value badge-safe";
  } else {
    elSafetyIndicator.textContent = "Unsafe State";
    elSafetyIndicator.className = "dash-value badge-unsafe";
  }

  if (goalAchieved) {
    elGoalIndicator.textContent = "Goal Reached!";
    elGameStatusPill.textContent = "Puzzle Solved!";
    elGameStatusPill.className = "status-pill status-solved";
  } else if (!safe) {
    elGoalIndicator.textContent = "Failed";
    elGameStatusPill.textContent = "Unsafe State!";
    elGameStatusPill.className = "status-pill status-failed";
  } else if (isGameActive) {
    elGoalIndicator.textContent = "In Progress";
    elGameStatusPill.textContent = "Game Active";
    elGameStatusPill.className = "status-pill status-active";
  } else {
    elGoalIndicator.textContent = "Ready";
    elGameStatusPill.textContent = "Game Ready";
    elGameStatusPill.className = "status-pill status-ready";
  }

  updateButtonStates();
  highlightActiveSolutionStep();
}

// Enable or disable buttons according to the current state
function updateButtonStates() {
  const [F, X, G, B] = currentState;

  if (!isGameActive || isGameOverUnsafe || isGoal(currentState)) {
    elBtnMoveAlone.disabled = true;
    elBtnTakeFox.disabled = true;
    elBtnTakeGoose.disabled = true;
    elBtnTakeBeans.disabled = true;
    return;
  }

  elBtnMoveAlone.disabled = false;

  elBtnTakeFox.disabled = (X !== F);
  elBtnTakeGoose.disabled = (G !== F);
  elBtnTakeBeans.disabled = (B !== F);
}

// Highlight the active BFS solution step
function highlightActiveSolutionStep() {
  if (!bfsSolution) return;

  const items = document.querySelectorAll('.solution-step-item');

  items.forEach((item, index) => {
    if (index === currentStepIndex) {
      item.classList.add('active-step');
      item.scrollIntoView({
        behavior: 'smooth',
        block: 'nearest'
      });
    } else {
      item.classList.remove('active-step');
    }
  });

  if (elBtnPrevStep) {
    elBtnPrevStep.disabled = (currentStepIndex <= 0);
  }

  if (elBtnNextStep) {
    elBtnNextStep.disabled =
      (currentStepIndex >= bfsSolution.length - 1);
  }
}

// Display status messages
function showMessage(text, type = 'info') {
  elStatusMessage.innerHTML = text;
  elStatusMessage.className = `alert-banner ${type}-alert`;
}

// --- 8. MANUAL USER INTERACTION HANDLERS ---

// Start the game
function handleStartGame() {
  isGameActive = true;
  isGameOverUnsafe = false;
  inTransitItem = null;

  elBtnStart.disabled = true;

  showMessage(
    "Game started! Move the farmer alone or take a companion across the river.",
    "info"
  );

  render();
}

// Perform a crossing action
function performCrossing(itemIndex) {
  if (!isGameActive || isGameOverUnsafe) return;

  const [F, X, G, B] = currentState;
  const newF = 1 - F;

  const targetBank =
    newF === 1 ? "Right Bank" : "Left Bank";

  // Check whether the selected item is on the farmer's bank
  if (itemIndex !== null && currentState[itemIndex] !== F) {
    const itemName = ENTITIES[itemIndex].name;

    showMessage(
      `Illegal Move! The ${itemName} is on the opposite bank from the farmer.`,
      "warning"
    );

    return;
  }

  const nextState = [...currentState];
  nextState[0] = newF;

  let actionText = "";

  if (itemIndex !== null) {
    nextState[itemIndex] = newF;

    const itemName = ENTITIES[itemIndex].name;

    actionText =
      `Farmer took the ${itemName} to the ${targetBank}.`;

    inTransitItem = itemIndex;
  } else {
    actionText =
      `Farmer crossed alone to the ${targetBank}.`;

    inTransitItem = null;
  }

  currentState = nextState;
  crossingCount++;
  lastActionTaken = actionText;

  // Check safety of the new state
  if (!isSafeState(currentState)) {
    isGameOverUnsafe = true;

    const unsafeReason = getUnsafeReason(currentState);

    showMessage(
      `<strong>UNSAFE STATE OCCURRED!</strong> ${unsafeReason}<br>
      Click <strong>"Reset"</strong> to try again!`,
      "danger"
    );

  } else if (isGoal(currentState)) {
    showMessage(
      `<strong>CONGRATULATIONS!</strong> You successfully brought all entities to the Right Bank in ${crossingCount} crossings!`,
      "success"
    );

  } else {
    const safeReason =
      getSafeExplanation(currentState, actionText);

    showMessage(
      `${actionText}<br><small>${safeReason}</small>`,
      "success"
    );
  }

  render();
}

// Reset the puzzle
function handleReset() {
  currentState = [...INITIAL_STATE];
  crossingCount = 0;
  isGameActive = false;
  isGameOverUnsafe = false;
  inTransitItem = null;
  currentStepIndex = 0;

  if (autoPlayInterval) {
    clearInterval(autoPlayInterval);
    autoPlayInterval = null;

    if (elBtnAutoPlay) {
      elBtnAutoPlay.textContent = "Auto Play";
    }
  }

  elBtnStart.disabled = false;

  if (elBtnAutoPlay) {
    elBtnAutoPlay.disabled = !bfsSolution;
  }

  showMessage(
    "Puzzle reset. Click <strong>'Start Game'</strong> to play manually.",
    "info"
  );

  render();
}

// --- 9. AI SOLUTION & BFS SOLVER HANDLERS ---
function handleSolveBFS() {
  const result = runBreadthFirstSearch();

  if (!result) {
    showMessage("No solution found by BFS.", "danger");
    return;
  }

  bfsSolution = result.path;
  currentStepIndex = 0;

  // Update AI metrics
  if (elMetricExplored) {
    elMetricExplored.textContent = result.exploredCount;
  }

  if (elMetricVisited) {
    elMetricVisited.textContent = result.visitedCount;
  }

  if (elMetricCrossings) {
    elMetricCrossings.textContent = result.path.length - 1;
  }

  if (elBfsSummaryTag) {
    elBfsSummaryTag.textContent =
      `Optimal: ${result.path.length - 1} Crossings`;
  }

  // Populate BFS solution list
  if (elSolutionList) {
    elSolutionList.innerHTML = '';

    bfsSolution.forEach((step, index) => {
      const stepItem = document.createElement('div');

      stepItem.className =
        `solution-step-item ${index === 0 ? 'active-step' : ''}`;

      stepItem.dataset.index = index;

      const [f, x, g, b] = step.state;

      stepItem.innerHTML = `
        <div class="step-badge">${index === 0 ? 'Start' : index}</div>

        <div class="step-info">
          <div class="step-action">${step.action}</div>

          <div class="step-details">
            <span>
              Resulting State:
              <code class="step-state-code">(${f}, ${x}, ${g}, ${b})</code>
            </span>

            <span class="step-reason">
              ${step.explanation}
            </span>
          </div>
        </div>
      `;

      stepItem.addEventListener('click', () => {
        jumpToStep(index);
      });

      elSolutionList.appendChild(stepItem);
    });
  }

  if (elBtnPrevStep) elBtnPrevStep.disabled = true;
  if (elBtnNextStep) elBtnNextStep.disabled = false;
  if (elBtnAutoPlay) elBtnAutoPlay.disabled = false;

  jumpToStep(0);

  showMessage(
    `<strong>BFS Search Complete!</strong>
    Discovered optimal shortest path with <strong>7 crossings</strong>
    after exploring ${result.exploredCount} states.
    Use <strong>"Next Step"</strong> or <strong>"Auto Play"</strong>
    to inspect each move.`,
    "info"
  );
}

// Navigate to a specific BFS solution step
function jumpToStep(stepIdx) {
  if (
    !bfsSolution ||
    stepIdx < 0 ||
    stepIdx >= bfsSolution.length
  ) {
    return;
  }

  currentStepIndex = stepIdx;

  const step = bfsSolution[stepIdx];

  currentState = [...step.state];
  crossingCount = step.stepNumber;
  inTransitItem = step.itemIndex;

  isGameActive = true;
  isGameOverUnsafe = false;

  if (isGoal(currentState)) {
    showMessage(
      `<strong>Step ${stepIdx} (Goal State):</strong>
      ${step.action}. ${step.explanation}`,
      "success"
    );

  } else if (stepIdx === 0) {
    showMessage(
      `<strong>Step 0 (Initial State):</strong>
      ${step.action}. ${step.explanation}`,
      "info"
    );

  } else {
    showMessage(
      `<strong>Step ${stepIdx}:</strong>
      ${step.action}.<br>
      <small>${step.explanation}</small>`,
      "info"
    );
  }

  render();
}

// Move to the next BFS step
function handleNextStep() {
  if (
    !bfsSolution ||
    currentStepIndex >= bfsSolution.length - 1
  ) {
    return;
  }

  jumpToStep(currentStepIndex + 1);
}

// Move to the previous BFS step
function handlePrevStep() {
  if (!bfsSolution || currentStepIndex <= 0) {
    return;
  }

  jumpToStep(currentStepIndex - 1);
}

// Automatically play the BFS solution
function handleToggleAutoPlay() {
  if (!bfsSolution) return;

  if (autoPlayInterval) {
    // Stop autoplay
    clearInterval(autoPlayInterval);
    autoPlayInterval = null;

    if (elBtnAutoPlay) {
      elBtnAutoPlay.textContent = "Auto Play";
    }

    showMessage(
      "Auto Play paused. You can continue stepping manually.",
      "info"
    );

  } else {
    // Restart from the beginning if already completed
    if (currentStepIndex >= bfsSolution.length - 1) {
      jumpToStep(0);
    }

    if (elBtnAutoPlay) {
      elBtnAutoPlay.textContent = "Pause";
    }

    showMessage(
      "Auto Play running through the AI BFS solution...",
      "info"
    );

    autoPlayInterval = setInterval(() => {
      if (currentStepIndex < bfsSolution.length - 1) {
        jumpToStep(currentStepIndex + 1);

      } else {
        clearInterval(autoPlayInterval);
        autoPlayInterval = null;

        if (elBtnAutoPlay) {
          elBtnAutoPlay.textContent = "Auto Play";
        }

        showMessage(
          "Auto Play completed! Optimal 7-crossing plan demonstrated.",
          "success"
        );
      }
    }, 1400);
  }
}

// --- 10. ATTACH EVENT LISTENERS ---

function initEventListeners() {

  // Manual controls
  elBtnStart.addEventListener('click', handleStartGame);

  elBtnMoveAlone.addEventListener(
    'click',
    () => performCrossing(null)
  );

  elBtnTakeFox.addEventListener(
    'click',
    () => performCrossing(1)
  );

  elBtnTakeGoose.addEventListener(
    'click',
    () => performCrossing(2)
  );

  elBtnTakeBeans.addEventListener(
    'click',
    () => performCrossing(3)
  );

  elBtnReset.addEventListener('click', handleReset);

  // AI controls
  if (elBtnSolveBfs) {
    elBtnSolveBfs.addEventListener('click', handleSolveBFS);
  }

  if (elBtnPrevStep) {
    elBtnPrevStep.addEventListener('click', handlePrevStep);
  }

  if (elBtnNextStep) {
    elBtnNextStep.addEventListener('click', handleNextStep);
  }

  if (elBtnAutoPlay) {
    elBtnAutoPlay.addEventListener('click', handleToggleAutoPlay);
  }
}

// --- 11. INITIALIZATION ---

document.addEventListener('DOMContentLoaded', () => {
  initEventListeners();
  render();
});