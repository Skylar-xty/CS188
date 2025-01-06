# logicPlan.py
# ------------
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


"""
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

from typing import Dict, List, Tuple, Callable, Generator, Any
import util
import sys
import logic
import game

from logic import conjoin, disjoin
from logic import PropSymbolExpr, Expr, to_cnf, pycoSAT, parseExpr, pl_true

import itertools
import copy

pacman_str = 'P'
food_str = 'FOOD'
wall_str = 'WALL'
pacman_wall_str = pacman_str + wall_str
DIRECTIONS = ['North', 'South', 'East', 'West']
blocked_str_map = dict([(direction, (direction + "_blocked").upper()) for direction in DIRECTIONS])
geq_num_adj_wall_str_map = dict([(num, "GEQ_{}_adj_walls".format(num)) for num in range(1, 4)])
DIR_TO_DXDY_MAP = {'North':(0, 1), 'South':(0, -1), 'East':(1, 0), 'West':(-1, 0)}


#______________________________________________________________________________
# QUESTION 1

def sentence1() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    expr1 = Expr('A') | Expr('B')
    expr2 = (~Expr('A'))%(~Expr('B')|Expr('C'))
    # expr3 = ~Expr('A')|~Expr('B')|Expr('C')
    expr3 = disjoin(~Expr('A'),~Expr('B'),Expr('C'))
    expr = [expr1,expr2,expr3]
    expr = conjoin(expr)
    return expr
    # util.raiseNotDefined()

    "*** END YOUR CODE HERE ***"


def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    "*** BEGIN YOUR CODE HERE ***"
    expr1 = Expr('C')%(Expr('B')|Expr('D'))
    expr2 = Expr('A') >> (~Expr('B') & (~Expr('D')))
    expr3 = (~(Expr('B') & ~Expr('C'))) >> Expr('A')
    expr4 = (~Expr('D')) >> Expr('C')
    expr = [expr1, expr2, expr3, expr4]
    expr = conjoin(expr)
    return expr
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.

    Pacman cannot both be alive at time 0 and be born at time 0.

    Pacman is born at time 0.
    """
    "*** BEGIN YOUR CODE HERE ***"
    PacmanAlive_0 = PropSymbolExpr('PacmanAlive', time=0)
    PacmanAlive_1 = PropSymbolExpr('PacmanAlive', time=1)
    PacmanBorn_0 = PropSymbolExpr('PacmanBorn', time=0)
    PacmanKilled_0 = PropSymbolExpr('PacmanKilled', time=0)

    # Sentence 1:
    expr1 = (PacmanAlive_1 % ((PacmanAlive_0 & ~PacmanKilled_0) | (~PacmanAlive_0 & PacmanBorn_0)))

    # Sentence 2:
    expr2 = ~(PacmanAlive_0 & PacmanBorn_0)

    # Sentence 3:
    expr3 = PacmanBorn_0
    # expr = [expr1, expr2, expr3]
    expr = conjoin([expr1, expr2, expr3])
    # expr = expr1&expr2&expr3
    return expr
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    # to_cnf converts the input sentence into Conjunctive Normal Form(the form required
    # by the SAT solver)
    cnf_sentence = to_cnf(sentence)
    # pass it to the SAT solver to find a satisfying assignment to the symbols in sentence
    return pycoSAT(cnf_sentence)

def findModelUnderstandingCheck() -> Dict[Expr, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    """
    a = Expr('A')
    "*** BEGIN YOUR CODE HERE ***"
    print("a.__dict__ is:", a.__dict__) # might be helpful for getting ideas
    a.op = 'a'
    model = {a: True}
    return model
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    """
    "*** BEGIN YOUR CODE HERE ***"
    test = premise & (~conclusion)
    # test = premise >> conclusion
    model = findModel(test)

    return model is False
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    """
    "*** BEGIN YOUR CODE HERE ***"
    # print("assignments:",assignments)
    return pl_true((~inverse_statement), assignments)
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 2

def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single 
    Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals  ist is true.
    >>> A = PropSymbolExpr('A');
    >>> B = PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print(pl_true(atleast1,model1))
    False
    >>> model2 = {A:False, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    >>> model3 = {A:True, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    """
    "*** BEGIN YOUR CODE HERE ***"
    return disjoin(*literals)
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    itertools.combinations may be useful here.
    """
    "*** BEGIN YOUR CODE HERE ***"
    clauses = []
    for (lit1, lit2) in itertools.combinations(literals,2):
        clause = disjoin(~lit1, ~lit2)
        clauses.append(clause)

    return conjoin(*clauses)
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    "*** BEGIN YOUR CODE HERE ***"
    at_least_one = atLeastOne(literals)
    at_most_one = atMostOne(literals)
    return conjoin(at_least_one,at_most_one)
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 3

def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]=None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    #generates an expression defining the sufficient and necessary conditions for
    #Pacman to be at (x,y) at t
    now, last = time, time - 1
    # print("last:",last)
    possible_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t
    # the if statements give a small performance boost and are required for q4 and q5 correctness
    if walls_grid[x][y+1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    
    "*** BEGIN YOUR CODE HERE ***"
    # any one of them being true would be enough
    possible_causes_expr = disjoin(possible_causes)
    # print("last",last)

    successor_state_axiom = PropSymbolExpr(pacman_str, x, y, time=now) % possible_causes_expr

    return successor_state_axiom
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1

    moved_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    if walls_grid[x][y+1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin([~PropSymbolExpr(pacman_str, x, y, time=last) , ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    failed_move_causes: List[Expr] = [] # using merged variables, improves speed significantly
    auxilary_expression_definitions: List[Expr] = []
    for direction in DIRECTIONS:
        dx, dy = DIR_TO_DXDY_MAP[direction]
        wall_dir_clause = PropSymbolExpr(wall_str, x + dx, y + dy) & PropSymbolExpr(direction, time=last)
        wall_dir_combined_literal = PropSymbolExpr(wall_str + direction, x + dx, y + dy, time=last)
        failed_move_causes.append(wall_dir_combined_literal)
        auxilary_expression_definitions.append(wall_dir_combined_literal % wall_dir_clause)

    failed_move_causes_sent: Expr = conjoin([
        PropSymbolExpr(pacman_str, x, y, time=last),
        disjoin(failed_move_causes)])

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin([moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)


def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing all of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    pacphysics_sentences = []

    "*** BEGIN YOUR CODE HERE ***"
    # util.raiseNotDefined()
    # the variable for whether Pacman is at (x,y) at time t is PropSymbolExpr(pacman_str,x,y,time=t)
    # wall exists at (x,y) is PropSymbolExpr(wall_str,x,y,time=t)
    # 1.for all (x, y) in all_coords:
    #   If a wall is at (x, y) --> Pacman is not at (x, y)
    print("walls_grid:", walls_grid)
    print("all_coords:", all_coords)
    for coordinate in all_coords:
        pacphysics_sentences.append(PropSymbolExpr(wall_str, coordinate[0], coordinate[1]) >>
                                    ~PropSymbolExpr(pacman_str, coordinate[0], coordinate[1], time = t))
    # for x, y in all_coords:
    #     # if walls_grid[x][y]:
    #     if
    #     pacphysics_sentences.append(PropSymbolExpr(pacman_str, x, y, time=t))
    # 2.Pacman is at exactly one of the squares at timestep t.
    pacphysics_sentences.append(exactlyOne([PropSymbolExpr(pacman_str, x, y, time=t) for x, y in non_outer_wall_coords]))
    # 3.Pacman takes exactly one action at timestep t.
    actions = ['North', 'South', 'East', 'West']
    pacphysics_sentences.append(exactlyOne([PropSymbolExpr(action, time=t) for action in actions]))

    # 4.Results of calling sensorModel(...), unless None.
    if sensorModel is not None:
        pacphysics_sentences.append(sensorModel(t, non_outer_wall_coords))

    # 5.Results of calling successorAxioms(...), describing how Pacman can end in various
    #    locations on this time step. Consider edge cases. Don't call if None.
    if successorAxioms and walls_grid and t:
        pacphysics_sentences.append(successorAxioms(t, walls_grid, non_outer_wall_coords))

    "*** END YOUR CODE HERE ***"

    return conjoin(pacphysics_sentences)


def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
    Given:
        - x1_y1 = (x1, y1), a potential location at time t = 1
        - x0_y0 = (x0, y0), Pacman's location at time t = 0
        - action0 = one of the four items in DIRECTIONS, Pacman's action at time t = 0
        - action1 = to ensure match with autograder solution
        - problem = an instance of logicAgents.LocMapProblem
    Note:
        - there's no sensorModel because we know everything about the world
        - the successorAxioms should be allLegalSuccessorAxioms where needed
    Return:
        - a model where Pacman is at (x1, y1) at time t = 1
        - a model where Pacman is not at (x1, y1) at time t = 1
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # We know which coords are walls:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]
    KB.append(conjoin(map_sent))
    "*** BEGIN YOUR CODE HERE ***"
    # add to KB:
    # 1.pacphysics_axioms
    print("wall_grid:",walls_grid)
    # print("wall_list:",walls_list)
    KB.append(pacphysicsAxioms(0, all_coords, non_outer_wall_coords, walls_grid,None,allLegalSuccessorAxioms))#,walls_grid=walls_list))
    KB.append(pacphysicsAxioms(1, all_coords, non_outer_wall_coords, walls_grid,None,allLegalSuccessorAxioms))#,walls_grid=walls_list))
    # 2.pacman's current location(x0,y0)
    KB.append(PropSymbolExpr(pacman_str, x0_y0[0], x0_y0[1], time=0))

    # 3.pacman takes action0,1
    KB.append(PropSymbolExpr(action0, time=0))
    KB.append(PropSymbolExpr(action1, time=1))
    # For t=1, generate successor axioms based on possible movements and wall constraints
    # successor_axioms = allLegalSuccessorAxioms(1, walls_grid, non_outer_wall_coords=non_outer_wall_coords)
    # KB.append(successor_axioms)

    KB = conjoin(KB)
    # Query the SAT solver to find a model where Pacman is at (x1, y1) at time t=1
    KBatx1y1 = [KB, PropSymbolExpr(pacman_str, x1_y1[0], x1_y1[1], time=1)]
    model1 = findModel(conjoin(KBatx1y1))

    # Query the SAT solver to find a model where Pacman is NOT at (x1, y1) at time t=1
    KBwithoutatx1y1 = [KB, ~PropSymbolExpr(pacman_str, x1_y1[0], x1_y1[1], time=1)]
    model2 = findModel(conjoin(KBwithoutatx1y1))

    model = (model1, model2)
    return model
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 4

def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), 
            range(height + 2)))
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    # util.raiseNotDefined()
    # 1.Add to KB: Initial knowledge: Pacman’s initial location at timestep 0
    KB.append(logic.PropSymbolExpr(pacman_str, x0, y0, time=0))

    for t in range(50):
        print("timestamp:", t)
        # 2.Initial knowledge: Pacman can only be at exactlyOne of the locations in non_wall_coords at timestep t
        pacman_expr = exactlyOne([logic.PropSymbolExpr(pacman_str, x, y, time=t) for x, y in non_wall_coords])
        KB.append(pacman_expr)

        # 3.a satisfying assignment for the variables given the KB
        goal_state = logic.PropSymbolExpr(pacman_str, xg, yg, time=t)
        model = findModel(goal_state & conjoin(KB))
        if model:
            return extractActionSequence(model, actions)
        # 4.Pacman takes exactly one action per timestep.
        possible_actions = exactlyOne([logic.PropSymbolExpr(action, time=t) for action in actions])
        KB.append(possible_actions)

        # 5.Transition Model sentences: call pacmanSuccessorAxiomSingle(...) for all possible pacman positions in non_wall_coords
        for x, y in non_wall_coords:
            KB.append(pacmanSuccessorAxiomSingle(x, y, t + 1, walls_grid))

    # No solution exists
    return None


    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls.asList()
    (x0, y0), food = problem.start
    food = food.asList()

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    # util.raiseNotDefined()
    #Pacman's initial location
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))

    # Initialize Food[x,y]_t variables
    for food_coords in food: KB.append(logic.PropSymbolExpr(food_str, food_coords[0], food_coords[1], time=0))

    for t in range(50):
        #1.Pacman can only be at exactlyOne of the locations in non_wall_coords at timestep t
        pacman_state = exactlyOne([PropSymbolExpr(pacman_str, x,y, time=t) for x,y in non_wall_coords])
        KB.append(pacman_state)
        # 2.goal_state
        goal_state = [~PropSymbolExpr(food_str, food_coord[0], food_coord[1], time=t) for food_coord in food]
        model = findModel(conjoin(goal_state + KB))
        if model:
            return extractActionSequence(model, actions)

        # 3. Pacman takes exactly one action per timestep
        possible_actions = exactlyOne([PropSymbolExpr(action, time=t) for action in actions])
        KB.append(possible_actions)

        for wall_coord in non_wall_coords:
            KB.append(pacmanSuccessorAxiomSingle(wall_coord[0], wall_coord[1], t + 1, walls))

        for food_x,food_y in food:
            pacman_s = PropSymbolExpr(pacman_str, food_x, food_y, time=t)
            food_s = PropSymbolExpr(food_str, food_x, food_y, time=t)
            next_food = PropSymbolExpr(food_str, food_x, food_y, time=t + 1)

            food2get = food_s & pacman_s
            food2avoid = food_s & ~pacman_s

            KB.append(food2avoid >> next_food)
            KB.append(food2get>> ~next_food)

    # No solution exists
    return None

    "*** END YOUR CODE HERE ***"




def helper1(agent, KB, t, all_coords, non_outer_wall_coords, map):
    KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, map, sensorAxioms, allLegalSuccessorAxioms))
    KB.append(PropSymbolExpr(agent.actions[t], time=t))
    KB.append(fourBitPerceptRules(t, agent.getPercepts()))


def helper2(KB, t, state, possible_loc):
    cKB = conjoin(KB)
    pacman_loc = PropSymbolExpr(pacman_str, state[0], state[1], time=t)
    if findModel(cKB & pacman_loc) :
        possible_loc.append((state[0], state[1]))
    elif entails(cKB, pacman_loc):
        KB.append(pacman_loc)
    else:
        KB.append(~pacman_loc)


def helper3(KB, coord, map):

    wall = logic.PropSymbolExpr(wall_str, coord[0], coord[1])
    cKB = logic.conjoin(KB)
    if entails(cKB, wall):
        KB.append(wall)
        map[coord[0]][coord[1]] = 1
    elif entails(cKB, ~wall):
        KB.append(~wall)
        map[coord[0]][coord[1]] = 0
#______________________________________________________________________________
# QUESTION 6

def localization(problem, agent) -> Generator:
    '''
    problem: a LocalizationProblem instance
    agent: a LocalizationLogicAgent instance
    '''
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    # util.raiseNotDefined()

    for coord in all_coords:
        if coord not in walls_list:
            KB.append(~PropSymbolExpr(wall_str, coord[0], coord[1]))
        else:
            KB.append(PropSymbolExpr(wall_str, coord[0], coord[1]))

    for t in range(0, agent.num_timesteps):
        helper1(agent, KB, t, all_coords, non_outer_wall_coords, walls_grid)
        possible_locations = list()
        for wall in non_outer_wall_coords:
            helper2(KB, t, wall, possible_locations)

        agent.moveToNextState(agent.actions[t])

        yield possible_locations
    # for t in range(agent.num_timesteps):
    #     "*** END YOUR CODE HERE ***"
    #     # yield possible_locations


#______________________________________________________________________________
# QUESTION 7

def mapping(problem, agent) -> Generator:
    '''
    problem: a MappingProblem instance
    agent: a MappingLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # Pacman knows that the outer border of squares are all walls
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    KB.append(logic.PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))
    KB.append(~logic.PropSymbolExpr(wall_str, pac_x_0, pac_y_0))

    for t in range(agent.num_timesteps):
        helper1(agent, KB, t, all_coords, non_outer_wall_coords, known_map)

        for wall in non_outer_wall_coords:
            helper3(KB, wall, known_map)

        agent.moveToNextState(agent.actions[t])

        yield known_map

    # util.raiseNotDefined()
    #
    # for t in range(agent.num_timesteps):
    #     "*** END YOUR CODE HERE ***"
    #     yield known_map

#______________________________________________________________________________
# QUESTION 8

def slam(problem, agent) -> Generator:
    '''
    problem: a SLAMProblem instance
    agent: a SLAMLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # We know that the outer_coords are all walls.
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    # util.raiseNotDefined()
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))
    known_map[pac_x_0][pac_y_0] = 0
    KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))

    for t in range(agent.num_timesteps):
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, SLAMSensorAxioms, SLAMSuccessorAxioms))
        KB.append(PropSymbolExpr(agent.actions[t], time=t))
        KB.append(numAdjWallsPerceptRules(t, agent.getPercepts()))

        possible_loc = list()
        for wall in non_outer_wall_coords:
            helper3(KB, wall, known_map)
            helper2(KB, t, wall, possible_loc)

        # Call agent.moveToNextState(action_t) on the current agent action at timestep t
        agent.moveToNextState(agent.actions[t])

        yield (known_map, possible_loc)

        # for t in range(agent.num_timesteps):
        "*** END YOUR CODE HERE ***"
        # yield (known_map, possible_locations)


# Abbreviations
plp = positionLogicPlan
loc = localization
mp = mapping
flp = foodLogicPlan
# Sometimes the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)

#______________________________________________________________________________
# Important expression generating functions, useful to read for understanding of this project.


def sensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (
                PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time = t)
        all_percept_exprs.append(percept_unit_clause % disjoin(percept_exprs))

    return conjoin(all_percept_exprs + combo_var_def_exprs)


def fourBitPerceptRules(t: int, percepts: List) -> Expr:
    """
    Localization and Mapping both use the 4 bit sensor, which tells us True/False whether
    a wall is to pacman's north, south, east, and west.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 4, "Percepts must be a length 4 list."

    percept_unit_clauses = []
    for wall_present, direction in zip(percepts, DIRECTIONS):
        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        if not wall_present:
            percept_unit_clause = ~PropSymbolExpr(blocked_str_map[direction], time=t)
        percept_unit_clauses.append(percept_unit_clause) # The actual sensor readings
    return conjoin(percept_unit_clauses)


def numAdjWallsPerceptRules(t: int, percepts: List) -> Expr:
    """
    SLAM uses a weaker numAdjWallsPerceptRules sensor, which tells us how many walls pacman is adjacent to
    in its four directions.
        000 = 0 adj walls.
        100 = 1 adj wall.
        110 = 2 adj walls.
        111 = 3 adj walls.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 3, "Percepts must be a length 3 list."

    percept_unit_clauses = []
    for i, percept in enumerate(percepts):
        n = i + 1
        percept_literal_n = PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t)
        if not percept:
            percept_literal_n = ~percept_literal_n
        percept_unit_clauses.append(percept_literal_n)
    return conjoin(percept_unit_clauses)


def SLAMSensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        blocked_dir_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        all_percept_exprs.append(blocked_dir_clause % disjoin(percept_exprs))

    percept_to_blocked_sent = []
    for n in range(1, 4):
        wall_combos_size_n = itertools.combinations(blocked_str_map.values(), n)
        n_walls_blocked_sent = disjoin([
            conjoin([PropSymbolExpr(blocked_str, time=t) for blocked_str in wall_combo])
            for wall_combo in wall_combos_size_n])
        # n_walls_blocked_sent is of form: (N & S) | (N & E) | ...
        percept_to_blocked_sent.append(
            PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t) % n_walls_blocked_sent)

    return conjoin(all_percept_exprs + combo_var_def_exprs + percept_to_blocked_sent)


def allLegalSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = pacmanSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)


def SLAMSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = SLAMSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)

#______________________________________________________________________________
# Various useful functions, are not needed for completing the project but may be useful for debugging


def modelToString(model: Dict[Expr, bool]) -> str:
    """Converts the model to a string for printing purposes. The keys of a model are 
    sorted before converting the model to a string.
    
    model: Either a boolean False or a dictionary of Expr symbols (keys) 
    and a corresponding assignment of True or False (values). This model is the output of 
    a call to pycoSAT.
    """
    if model == False:
        return "False" 
    else:
        # Dictionary
        modelList = sorted(model.items(), key=lambda item: str(item[0]))
        return str(modelList)


def extractActionSequence(model: Dict[Expr, bool], actions: List) -> List:
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[2]":True, "P[3,4,0]":True, "P[3,3,0]":False, "West[0]":True, "GhostScary":True, "West[2]":False, "South[1]":True, "East[0]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print(plan)
    ['West', 'South', 'North']
    """
    plan = [None for _ in range(len(model))]
    for sym, val in model.items():
        parsed = parseExpr(sym)
        if type(parsed) == tuple and parsed[0] in actions and val:
            action, _, time = parsed
            plan[time] = action
    #return list(filter(lambda x: x is not None, plan))
    return [x for x in plan if x is not None]


# Helpful Debug Method
def visualizeCoords(coords_list, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    for (x, y) in itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)):
        if (x, y) in coords_list:
            wallGrid.data[x][y] = True
    print(wallGrid)


# Helpful Debug Method
def visualizeBoolArray(bool_arr, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    wallGrid.data = copy.deepcopy(bool_arr)
    print(wallGrid)

class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()
        
    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()
