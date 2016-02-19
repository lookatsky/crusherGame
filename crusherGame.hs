-- A Crusher Board Game Implementation in Haskell.
-- This application finds the next best move for a player by generating a search tree of possible next boards, and perform min-max search
-- to pick the best move.
-- written by Zoe Wang, Christopher Yang, Stacy Cheng.

-- Some comments are copied over (and modified if needed) from the starter file if they are still applicable to our code

-- Sections in this file:
-- 1.  CUSTOM DATA TYPES
-- 2.  CRUSHER
-- 3.  STATE SEARCHER
-- 4.  MINIMAX
-- 5.  GENERATE TREE
-- 6.  GENERATE STATES
-- 7.  GENERATE MOVES
-- 8.  GENERATE SLIDES
-- 9.  GENERATE LEAPS
-- 10. GENERATE GRID
-- 11. BOARD EVALUATOR

-- -----------------------------------------------------------------------------
-- 1. CUSTOM DATA TYPES
-- -----------------------------------------------------------------------------

-- Represents possible pieces on the board:
-- - D: Unoccupied
-- - W: White
-- - B: Black
data Piece = D | W | B deriving (Eq, Show)

-- A board is a list of pieces.
type Board = [Piece]

-- A grid is a list of points.
type Point = (Int,Int)
type Grid  = [Point]

-- A state is a list of tiles indicating the location of each piece.
type Tile  = (Piece,Point)
type State = [Tile]

-- A move can either be a slide or a leap.
-- - Slide: W or B moving to an unoccupied location.
-- - Leap:  W or B moving over a friendly piece to a location that is
--          unoccupied or occupied by an enemy piece.
type Move  = (Point,Point)
type Slide = (Point,Point)
type Jump  = (Point,Point,Point)

-- Represents a search tree where each node is a possible board after
-- making a valid move on its parent board.
type BoardTree = Tree Board
data Tree a = Node {depth :: Int, board :: a, nextBoards :: [Tree a]} deriving (Show)

-- Converts a string of pieces into a corresponding board representation.
stringToBoard :: String  -> Board
stringToBoard s = map (\ x -> check x) s
    where
        check 'W' = W
        check 'B' = B
        check 'D' = D
        check '-' = D

-- Converts a list of pieces into its corresponding string representation.
boardToString :: Board -> String
boardToString b = map (\ x -> check x) b
    where
        check W = 'W'
        check B = 'B'
        check D = '-'

-- -----------------------------------------------------------------------------
-- 2. CRUSHER
-- -----------------------------------------------------------------------------
--
-- crusher
--
-- This function consumes a list of boards, a player, the depth of
-- search tree, the size of the provide boards, and produces the
-- next best board possible for the provided player, and accordingly
-- makes the move and returns new board consed onto the list of boards
--
-- Arguments:
-- -- (current:old): current represents the most recent board, old is
--                   the history of all boards already seen in game
-- -- p: W or B representing the player the program is
-- -- d: an Integer indicating depth of search tree
-- -- n: an Integer representing the dimensions of the board
--
-- Returns: a list of String with the new current board consed onto the front
--
crusher :: [String] -> Piece -> Int -> Int -> [String]
crusher (current:old) p d n
    | bestBoard == current = (current:old)
    | otherwise = (bestBoard:(current:old))
        where
            board = stringToBoard current
            history = map (\ x-> stringToBoard x) (current:old)
            grid = generateGrid n (n - 1) (2 * (n-1)) []
            slides = generateSlides grid n
            jumps = generateLeaps grid n
            bestBoard = boardToString (stateSearch board history grid slides jumps p d n)

-- -----------------------------------------------------------------------------
-- 3. STATE SEARCHER
-- -----------------------------------------------------------------------------

--
-- stateSearch
--
-- This function consumes the arguments described below, based on the internal
-- representation of the game, if there is no point in playing the game as the
-- current board is in a state where the game has ended then just return the
-- board, else generate a search tree till the specified depth and apply
-- minimax to it by using the appropriately generated heuristic
--
-- Arguments:
-- -- board: a Board representing the most recent board
-- -- history: a list of Boards of representing all boards already seen
-- -- grid: the Grid representing the coordinate-grid the game being played
-- -- slides: the list of all Slides possible for the given grid
-- -- jumps: the list of all Jumps possible for the given grid
-- -- player: W or B representing the player the program is
-- -- depth: an Integer indicating depth of search tree
-- -- num: an Integer representing the dimensions of the board
--
-- Returns: the current board if game is over,
--          otherwise produces the next best board
--
stateSearch :: Board -> [Board] -> Grid -> [Slide] -> [Jump] -> Piece -> Int -> Int -> Board
stateSearch board history grid slides jumps player depth num
                             | gameOver  num board = board
                             | otherwise                   = minimax generatedTree True player history num
                            where generatedTree = generateTree board history grid slides jumps player depth num


-- -----------------------------------------------------------------------------
-- 4. MINIMAX
-- -----------------------------------------------------------------------------
--
-- minimax
--
-- This function implements the minimax algorithm and produces
-- the next best board that the program should make a move to
--
-- Arguments:
-- -- (Node _ b children): a BoardTree to apply minimax algorithm on
-- -- maxPlayer : True if looking for maximum value (at a player level)
-- -- player: The piece to be the max player
-- -- history : a list of Boards of representing all boards already seen
-- -- n : The dimension of the board
--
-- Returns: the next best board
--
minimax :: BoardTree -> Bool -> Piece -> [Board] -> Int -> Board
minimax (Node d b []) maxPlayer player history n = b
minimax (Node d b children) maxPlayer player history n
                                | maxFilter == [] = []
                                | otherwise = snd (head (maxFilter))
                       where valBoards = minimaxHelper children (not(maxPlayer)) player history n
                             maxScore = maximum (fst (unzip valBoards))
                             maxFilter = filter ((== maxScore).fst) valBoards

minimaxHelper :: [BoardTree] -> Bool -> Piece -> [Board] -> Int -> [(Int,Board)]
minimaxHelper [] maxPlayer player history n = []
minimaxHelper (c:cs) maxPlayer player history n = [calculateMinMax c maxPlayer player history n] ++ minimaxHelper cs maxPlayer player history n

-- Actually calculates the score for each board state.
-- If the consumed tree is a leaf, then use the board evaluator to score it.
-- If the consumed tree has children, then takes the max or min score among its children
-- depending on what level the parent is in.
calculateMinMax :: BoardTree -> Bool -> Piece -> [Board] -> Int -> (Int,Board)
calculateMinMax (Node d b []) maxPlayer player history n = ((boardEvaluator player n b), b)
calculateMinMax (Node d b children) maxPlayer player history n = (desiredScore, b)
              where valBoardList = minimaxHelper children (not(maxPlayer)) player history n
                    scoreList = fst (unzip valBoardList)
                    desiredScore
                        | maxPlayer = maximum scoreList
                        | otherwise = minimum scoreList

-- -----------------------------------------------------------------------------
-- 5. GENERATE TREE
-- -----------------------------------------------------------------------------

--
-- generateTree
--
-- This function consumes the arguments described below, and builds a search
-- tree till specified depth from scratch by using the current board and
-- generating all the next states recursively; however it doesn't generate
-- children of those states which are in a state where the game has ended.
--
-- Arguments:
-- -- board: a Board representing the most recent board
-- -- history: a list of Boards of representing all boards already seen
-- -- grid: the Grid representing the coordinate-grid the game being played
-- -- slides: the list of all Slides possible for the given grid
-- -- jumps: the list of all Jumps possible for the given grid
-- -- player: W or B representing the player the program is
-- -- depth: an Integer indicating depth of search tree
-- -- n: an Integer representing the dimensions of the board
--
-- Returns: the corresponding BoardTree generated till specified depth
--
generateTree :: Board -> [Board] -> Grid -> [Slide] -> [Jump] -> Piece -> Int -> Int -> BoardTree
generateTree board history grid slides jumps player depth n = generateTree_hp board history grid slides jumps player depth n 0

-- Checks whether or not to generate children trees
-- If we've reached the specified depth or the game is over at this point then
-- generate a tree with no children
-- Else, generate a node with children.
generateTree_hp :: Board -> [Board] -> Grid -> [Slide] -> [Jump] -> Piece -> Int -> Int -> Int -> BoardTree
generateTree_hp board history grid slides jumps player depth n currentDepth
                      | depth == currentDepth = Node depth board []
                      | gameOver n board = Node depth board []
                      | otherwise  = Node currentDepth board nextTree
                      where nextTree = generateChildrenTree nextBoards history grid slides jumps player depth n currentDepth
                            nextBoards = generateNewStates board history grid slides jumps player

-- Generates a tree's children states
generateChildrenTree :: [Board] -> [Board] -> Grid -> [Slide] -> [Jump] -> Piece -> Int -> Int -> Int -> [BoardTree]
generateChildrenTree [] history grid slides jumps player depth n currentDepth = []
generateChildrenTree (nb:bs) history grid slides jumps player depth n currentDepth = (firstTree:restTree)
                      where firstTree = generateTree_hp nb (nb:history) grid slides jumps nextPlayer depth n (currentDepth + 1)
                            restTree = generateChildrenTree bs history grid slides jumps player depth n currentDepth
                            nextPlayer
                                | player == W  = B
                                | otherwise    = W

-- -----------------------------------------------------------------------------
-- 6. GENERATE STATES
-- -----------------------------------------------------------------------------

--
-- generateNewStates
--
-- This function consumes the arguments described below, it first generates a
-- list of valid moves, applies those moves to the current board to generate
-- a list of next boards, and then checks whether or not that move would
-- have been possible by filtering out those boards already seen before
--
-- Arguments:
-- -- board: a Board representing the most recent board
-- -- history: a list of Boards of representing all boards already seen
-- -- grid: the Grid representing the coordinate-grid the game being played
-- -- slides: the list of all Slides possible for the given grid
-- -- jumps: the list of all Jumps possible for the given grid
-- -- player: W or B representing the player the program is
--
-- Returns: the list of next boards
--
generateNewStates :: Board -> [Board] -> Grid -> [Slide] -> [Jump] -> Piece -> [Board]
generateNewStates board history grid slides jumps player =
                      removeInvalidBoards (generatePossibleBoards moves board state player) history
                      where moves = moveGenerator state slides jumps player
                            state = zip board grid

generatePossibleBoards :: [Move] -> Board -> State -> Piece ->[Board]
generatePossibleBoards moves board state player
                       | moves == [] = []
                       | otherwise = generateBoardsForSingleMove (head moves) board state player ++ generatePossibleBoards (tail moves) board state player

generateBoardsForSingleMove :: Move -> Board -> State -> Piece -> [Board]
generateBoardsForSingleMove (p1,p2) board state player = [fst (unzip newState)]
                            where newState = map (\ x-> update x) state
                                  update (piece,point)
                                           | point == p1 = (D,point)
                                           | point == p2 = (player,point)
                                           | otherwise = (piece,point)

removeInvalidBoards :: [Board] -> [Board] -> [Board]
removeInvalidBoards [] history = []
removeInvalidBoards (b:bs) history
            | elem b history = removeInvalidBoards bs history
            | otherwise = (b:removeInvalidBoards bs history)

-- -----------------------------------------------------------------------------
-- 7. GENERATE MOVES
-- -----------------------------------------------------------------------------

--
-- moveGenerator
--
-- This function consumes a state, a list of possible jumps,
-- a list of possible slides and a player from whose perspective
-- to generate moves, to check which of these jumps and slides
-- the player could actually make, and produces a list of valid moves
--
-- Arguments:
-- -- state: a State representing the most recent state
-- -- slides: the list of all Slides possible for the given grid
-- -- jumps: the list of all Jumps possible for the given grid
-- -- player: W or B representing the player the program is
--
-- Returns: the list of all valid moves that the player could make
--
moveGenerator :: State -> [Slide] -> [Jump] -> Piece -> [Move]
moveGenerator state slides jumps player = moveGenHelper state slides jumps player state

moveGenHelper :: State -> [Slide] -> [Jump] -> Piece -> State -> [Move]
moveGenHelper currentState slides jumps player originalState
    | currentState == [] = []
    | (fst (head currentState)) == player = findMoveforTile (head currentState) slides jumps originalState ++ moveGenHelper (tail currentState) slides jumps player originalState
    | otherwise = moveGenHelper (tail currentState) slides jumps player originalState

findMoveforTile :: Tile -> [Slide] -> [Jump] -> State -> [Move]
findMoveforTile tile slides jumps state = generateValidSlides tile slides state ++ generateValidJumps tile jumps state

generateValidJumps :: Tile -> [Jump] -> State -> [Move]
generateValidJumps tile [] state = []
generateValidJumps (piece,point) ((p1,p2,p3):restJumps) state
                         | p1 == point  = generateJumpMove (p1,p2,p3) state piece ++ generateValidJumps (piece,point) restJumps state
                         | otherwise = generateValidJumps (piece,point) restJumps state

generateValidSlides :: Tile -> [Slide] -> State -> [Move]
generateValidSlides tile [] state = []
generateValidSlides (piece,point) ((p1,p2):restSlides) state
                         | p1 == point  = generateSlideMove(p1,p2) state ++ generateValidSlides (piece,point) restSlides state
                         | otherwise = generateValidSlides (piece,point) restSlides state

findTileFromState :: State -> Point -> [Tile]
findTileFromState state point
                    | pointFilter == [] = []
                    | otherwise = [(head pointFilter)]
                    where pointFilter = filter ((== point).snd) state

generateJumpMove :: Jump -> State -> Piece ->[Move]
generateJumpMove (p1,p2,p3) state piece
                    | p2Tile == [] = []
                    | p3Tile == [] = []
                    | (fst (head p2Tile)) == piece && (fst (head p3Tile)) /= piece = [(p1,p3)]
                    | otherwise = []
                    where p2Tile = findTileFromState state p2
                          p3Tile = findTileFromState state p3

generateSlideMove :: Slide ->State -> [Move]
generateSlideMove (p1,p2) state
                    | p2Tile == [] = []
                    | (fst (head p2Tile)) == D  = [(p1,p2)]
                    | otherwise = []
                    where p2Tile = findTileFromState state p2

-- -----------------------------------------------------------------------------
-- 8. GENERATE SLIDES
-- -----------------------------------------------------------------------------

-- generateSlides (generateGrid 3 2 4 []) 3 for n = 3
generateSlides :: Grid -> Int -> [Slide]
generateSlides b n
    | b == []   = []
    | otherwise = generateSlides' (head b) (generateAdjPoints (head b) n) n ++
                  generateSlides  (tail b) n

-- Generates all possible slide moves a piece at (x,y) can make.
generateSlides' :: Point -> [Point] -> Int -> [Slide]
generateSlides' (x,y) adjPoints n
    | adjPoints == [] = []
    | otherwise       = ((x,y), (head adjPoints)):(generateSlides' (x,y) (tail adjPoints) n)

-- Generates all possible points a piece at (x,y) can slide to.
-- Calls one of the helper functions depending on where on the board the point is.
generateAdjPoints :: Point -> Int -> [Point]
generateAdjPoints (x,y) n
    | y <  n - 1 = removeInvalidPoints (generateAdjPointsTop (x,y)) n
    | y == n - 1 = removeInvalidPoints (generateAdjPointsMid (x,y)) n
    | y >  n - 1 = removeInvalidPoints (generateAdjPointsLow (x,y)) n

generateAdjPointsTop :: Point -> [Point]
generateAdjPointsMid :: Point -> [Point]
generateAdjPointsLow :: Point -> [Point]
generateAdjPointsTop (x,y) = [(x-1,y-1), (x,y-1),   (x-1,y), (x+1,y), (x,y+1),   (x+1,y+1)]
generateAdjPointsMid (x,y) = [(x-1,y-1), (x,y-1),   (x-1,y), (x+1,y), (x-1,y+1), (x,y+1)  ]
generateAdjPointsLow (x,y) = [(x,y-1),   (x+1,y-1), (x-1,y), (x+1,y), (x-1,y+1), (x,y+1)  ]

-- Removes invalid points from a list of points for a board with n hexes.
removeInvalidPoints :: [Point] -> Int -> [Point]
removeInvalidPoints points n
    | points == []                 = []
    | isPointValid (head points) n = (head points):(removeInvalidPoints (tail points) n)
    | otherwise                    = removeInvalidPoints (tail points) n

-- Checks if a point is out of the bounds for a board with n hexes.
isPointValid :: Point -> Int -> Bool
isPointValid (x,y) n
    | x < 0 || y < 0         = False
    | y < n                 = x < y + n
    | y >= n && y < 2 * n - 1 = x <= 3 * n - y - 3
    | otherwise              = False

-- -----------------------------------------------------------------------------
-- 9. GENERATE LEAPS
-- -----------------------------------------------------------------------------

generateLeaps :: Grid -> Int -> [Jump]
generateLeaps b n
         | b == [] = []
         | otherwise = generateLeap (head b) n ++ generateLeaps(tail b) n

generateLeap :: Point -> Int -> [Jump]
generateLeap (x,y) n = generateJumps (x,y) (generateAdjPoints (x,y) n) n

generateJumps :: Point -> [Point] -> Int -> [Jump]
generateJumps (x,y) adjPoints n
                    |adjPoints == []  = []
                    |otherwise        = (generateJump (x,y) (head adjPoints) n) ++ generateJumps (x,y) (tail adjPoints) n

generateJump :: Point -> Point -> Int -> [Jump]
generateJump (x,y) (x1,y1) n
                | y1 == y && not(isPointValid(x2,y2) n)   = []
                | y1 == y                                 = [((x,y),(x1,y1),(x2,y2))]
                | y1 == n - 1 && not(isPointValid(x2m, y2) n) = []
                | y1 == n - 1  = [((x,y),(x1,y1),(x2m,y2))]
                | isPointValid (x2,y2) n  = [((x,y),(x1,y1),(x2,y2))]
                | otherwise  = []
                    where deltaX = x - x1
                          deltaY = y - y1
                          y2     = y1 - deltaY
                          x2m   = x1-(deltaX+1)
                          x2     = x1 - deltaX

-- -----------------------------------------------------------------------------
-- 10. GENERATE GRID
-- -----------------------------------------------------------------------------

--
-- generateGrid
--
-- This function consumes three integers (described below) specifying how to
-- properly generate the grid and also a list as an accumulator; to generate a
-- regular hexagon of side length n, pass n (n- 1) (2 * (n - 1)) and []
--
-- Arguments:
-- -- n1: one more than max x-coordinate in the row, initialized always to n
-- -- n2: the number of rows away from the middle row of the grid
-- -- n3: the current y-coordinate i.e the current row number
-- -- acc: an accumulator that keeps track of accumulating rows of grid
--       initialized to []
--
-- Note: This function on being passed 3 2 4 [] would produce
--     [(0,0),(1,0),(2,0)
--      (0,1),(1,1),(2,1),(3,1)
--      (0,2),(1,2),(2,2),(3,2),(4,2)
--      (0,3),(1,3),(2,3),(3,3)
--      (0,4),(1,4),(2,4)]
--
-- Returns: the corresponding Grid i.e the acc when n3 == -1
--
generateGrid :: Int -> Int -> Int -> Grid -> Grid
generateGrid n1 n2 n3 acc
    | n3 == -1  = acc
    | otherwise = generateGrid nn1 (n2 - 1) (n3 - 1) (row ++ acc)
        where
            row = map (\ x -> (x,n3)) [0 .. (n1 - 1)]
            nn1 = if n2 > 0 then n1 + 1 else n1 - 1

-- -----------------------------------------------------------------------------
-- 11. BOARD EVALUATOR
-- -----------------------------------------------------------------------------

-- Assigns a goodness to the given board depending on who the player is
--
-- If the player's pieces are less than n then it means they have lost
-- If the opponent's pieces are less than n then it means the player won
--
boardEvaluator :: Piece -> Int -> Board -> Int
boardEvaluator player n board
   | player == W && countWhite board < n = -10
   | player == W && countBlack board < n = 10
   | player == W = countWhite board - countBlack board
   | player == B && countBlack board < n = -10
   | player == B && countWhite board < n = 10
   | otherwise = countBlack board - countWhite board

countBlack :: Board -> Int
countBlack board
    | board == []       = 0
    | (head board) == B = 1 + countBlack (tail board)
    | otherwise         = countBlack (tail board)

countWhite :: Board -> Int
countWhite board
    | board == []       = 0
    | (head board) == W = 1 + countWhite (tail board)
    | otherwise         = countWhite (tail board)

-- The game is over if one side's pieces are less than n
gameOver :: Int -> Board -> Bool
gameOver n board
  | (countWhite board) < n || (countBlack board) < n = True
  | otherwise = False
