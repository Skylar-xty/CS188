# multiAgents.py
# --------------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


from util import manhattanDistance
from game import Directions
import random, util

from game import Agent
from pacman import GameState

class ReflexAgent(Agent):
    """
    A reflex agent chooses an action at each choice point by examining
    its alternatives via a state evaluation function.

    The code below is provided as a guide.  You are welcome to change
    it in any way you see fit, so long as you don't touch our method
    headers.
    """


    def getAction(self, gameState: GameState):
        """
        You do not need to change this method, but you're welcome to.

        getAction chooses among the best options according to the evaluation function.

        Just like in the previous project, getAction takes a GameState and returns
        some Directions.X for some X in the set {NORTH, SOUTH, WEST, EAST, STOP}
        """
        # Collect legal moves and successor states
        legalMoves = gameState.getLegalActions()

        # Choose one of the best actions
        scores = [self.evaluationFunction(gameState, action) for action in legalMoves]
        bestScore = max(scores)
        bestIndices = [index for index in range(len(scores)) if scores[index] == bestScore]
        chosenIndex = random.choice(bestIndices) # Pick randomly among the best

        "Add more of your code here if you want to"

        return legalMoves[chosenIndex]

    def evaluationFunction(self, currentGameState: GameState, action):
        """
        Design a better evaluation function here.

        The evaluation function takes in the current and proposed successor
        GameStates (pacman.py) and returns a number, where higher numbers are better.

        The code below extracts some useful information from the state, like the
        remaining food (newFood) and Pacman position after moving (newPos).
        newScaredTimes holds the number of moves that each ghost will remain
        scared because of Pacman having eaten a power pellet.

        Print out these variables to see what you're getting, then combine them
        to create a masterful evaluation function.
        """
        # Useful information you can extract from a GameState (pacman.py)
        successorGameState = currentGameState.generatePacmanSuccessor(action)
        newPos = successorGameState.getPacmanPosition()    #pacman position after moving
        newFood = successorGameState.getFood()             #remaining food
        newGhostStates = successorGameState.getGhostStates()
        newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]

        "*** YOUR CODE HERE ***"
        #debugging
        # print(newFood,"ddd")
        # print(newPos,"ddd")
        # print(newGhostStates,"ddd")
        # print(newFood.asList(),"dd")
        # for ghost in newGhostStates:
        #     print(type(ghost),"1",type(newGhostStates),"2",ghost.getPosition())
        # print("ddd")
        if(newFood.asList()):
            food_value = min([manhattanDistance(newPos, food_new)for food_new in newFood.asList()])
            food_value = 1/food_value
        else:
            food_value = 0
        # if(newGhostStates):
        for ghost in newGhostStates:
            ghost_value = manhattanDistance(newPos, ghost.getPosition())
        # ghost_value = (manhattanDistance(newPos,ghost.getPosition()) for ghost in newGhostStates)
        # else:
            # ghost_value = 0

        score = 2*successorGameState.getScore() + ghost_value*pow(food_value,1.5)
        # score = 2*successorGameState.getScore() + 1.5* food_value + 0.05*ghost_value
        # return successorGameState.getScore()
        return score

def scoreEvaluationFunction(currentGameState: GameState):
    """
    This default evaluation function just returns the score of the state.
    The score is the same one displayed in the Pacman GUI.

    This evaluation function is meant for use with adversarial search agents
    (not reflex agents).
    """
    return currentGameState.getScore()

class MultiAgentSearchAgent(Agent):
    """
    This class provides some common elements to all of your
    multi-agent searchers.  Any methods defined here will be available
    to the MinimaxPacmanAgent, AlphaBetaPacmanAgent & ExpectimaxPacmanAgent.

    You *do not* need to make any changes here, but you can if you want to
    add functionality to all your adversarial search agents.  Please do not
    remove anything, however.

    Note: this is an abstract class: one that should not be instantiated.  It's
    only partially specified, and designed to be extended.  Agent (game.py)
    is another abstract class.
    """

    def __init__(self, evalFn = 'scoreEvaluationFunction', depth = '2'):
        self.index = 0 # Pacman is always agent index 0
        self.evaluationFunction = util.lookup(evalFn, globals())
        self.depth = int(depth)

class MinimaxAgent(MultiAgentSearchAgent):
    """
    Your minimax agent (question 2)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the minimax action from the current gameState using self.depth
        and self.evaluationFunction.

        Here are some method calls that might be useful when implementing minimax.

        gameState.getLegalActions(agentIndex):
        Returns a list of legal actions for an agent
        agentIndex=0 means Pacman, ghosts are >= 1

        gameState.generateSuccessor(agentIndex, action):
        Returns the successor game state after an agent takes an action

        gameState.getNumAgents():
        Returns the total number of agents in the game

        gameState.isWin():
        Returns whether or not the game state is a winning state

        gameState.isLose():
        Returns whether or not the game state is a losing state
        """
        "*** YOUR CODE HERE ***"
        #debugging
        # print(gameState.getNumAgents())
        # print(gameState.getLegalActions())
        # print(self.depth)

        num_of_ghosts = gameState.getNumAgents() - 1
        def max_value(state, depth): #simply for pacman
            v=-1*float('inf')
            depth+=1
            if state.isWin() or state.isLose() or depth == self.depth:
                return self.evaluationFunction(state)
            # print(self.index,"aaaa")
            for action in state.getLegalActions(0):
                next_state = state.generateSuccessor(0, action)
                v = max(v,min_value(next_state,1,depth))
            return v

        def min_value(state, ghost_index, curr_depth):
            v=float('inf')
            if state.isWin() or state.isLose():
                return self.evaluationFunction(state)
            for action in state.getLegalActions(ghost_index):
                next_state = state.generateSuccessor(ghost_index,action)
                if ghost_index != num_of_ghosts:   #for ghost move
                    v = min(v,min_value(next_state, ghost_index+1, curr_depth))
                elif ghost_index == num_of_ghosts: #for pacman move
                    v = min(v,max_value(next_state, curr_depth))
            return v

        # if gameState.isWin() or gameState.isLose():
        #     return self.evaluationFunction(gameState)

        legalMoves = gameState.getLegalActions(self.index)

        # action2choose = 0
        pacman_max = -1*float('inf')
        for action in legalMoves:
            next_state = gameState.generateSuccessor(self.index,action)
            current_max = min_value(next_state, 1, 0)
            if current_max > pacman_max:
                pacman_max = current_max
                action2choose = action
        return action2choose
        # util.raiseNotDefined()

class AlphaBetaAgent(MultiAgentSearchAgent):
    """
    Your minimax agent with alpha-beta pruning (question 3)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the minimax action using self.depth and self.evaluationFunction
        """
        "*** YOUR CODE HERE ***"
        util.raiseNotDefined()

class ExpectimaxAgent(MultiAgentSearchAgent):
    """
      Your expectimax agent (question 4)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the expectimax action using self.depth and self.evaluationFunction

        All ghosts should be modeled as choosing uniformly at random from their
        legal moves.
        """
        "*** YOUR CODE HERE ***"
        util.raiseNotDefined()

def betterEvaluationFunction(currentGameState: GameState):
    """
    Your extreme ghost-hunting, pellet-nabbing, food-gobbling, unstoppable
    evaluation function (question 5).

    DESCRIPTION: <write something here so we know what you did>
    """
    "*** YOUR CODE HERE ***"
    util.raiseNotDefined()

# Abbreviation
better = betterEvaluationFunction
