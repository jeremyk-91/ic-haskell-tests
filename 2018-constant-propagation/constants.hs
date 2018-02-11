import Data.Maybe
import Data.List

type Id = String

type Function = (Id, [Id], Block)

type Block = [Statement]

data Statement = Assign Id Exp |
                 If Exp Block Block |
                 DoWhile Block Exp 
               deriving (Eq, Show)

data Exp = Const Int | Var Id | Apply Op Exp Exp | Phi Exp Exp
         deriving (Eq, Show)

data Op = Add | Mul | Eq | Gtr 
        deriving (Eq, Show)

------------------------------------------------------------------------
-- Given functions to support the interpreter...

lookUp :: (Eq a, Show a) => a -> [(a, b)] -> b
lookUp i table
  = fromMaybe (error ("lookup failed on identifier: " ++ show i)) 
              (lookup i table) 

execFun :: Function -> [Int] -> State
execFun (name, args, p) vs
  = execBlock p (zip args vs)

------------------------------------------------------------------------
-- Part I

type State = [(Id, Int)]

update :: (Id, Int) -> State -> State
update (id, newValue) []
  = [(id, newValue)]
update (id, newValue) (binding:bindings)
  | key == id = (id, newValue):bindings
  | otherwise = [binding] ++ (update (id, newValue) bindings)
  where (key, _) = binding

apply :: Op -> Int -> Int -> Int
apply Add x y
  = x + y
apply Mul x y
  = x * y
apply Eq x y
  | x == y    = 1
  | otherwise = 0
apply Gtr x y
  | x > y     = 1
  | otherwise = 0

eval :: Exp -> State -> Int
-- Pre: the variables in the expression will all be bound in the given state 
-- Pre: expressions do not contain phi instructions
eval (Const value) _
  = value
eval (Var key) state
  = lookUp key state
eval (Apply op exp1 exp2) state
  = apply op (eval exp1 state) (eval exp2 state)
eval (Phi e1 e2) state
  = error "Unexpected phi instruction in eval!"

execStatement :: Statement -> State -> State
execStatement (Assign id exp) state
  = update (id, newVal) state
    where newVal = eval exp state
execStatement (If conditionExp block1 block2) state
  | conditionValue == 1 = execBlock block1 state
  | conditionValue == 0 = execBlock block2 state
  | otherwise           = error "Condition evaluated to a non-0 or 1 value."
  where conditionValue = eval conditionExp state
execStatement (DoWhile block conditionExp) state
  | rerun == 1 = execStatement (DoWhile block conditionExp) state'
  | rerun == 0 = state'
  | otherwise  = error "Condition evaluated to a non-0 or 1 value."
  where state' = execBlock block state
        rerun  = eval conditionExp state' -- condition checked after loop

execBlock :: Block -> State -> State
execBlock [] state
  = state
execBlock (statement:statements) state
  = execBlock statements state'
    where state' = execStatement statement state

------------------------------------------------------------------------
-- Given function for testing propagateConstants...

-- Converts a function in SSA form into its optimised SSA form...
applyPropagate :: Function -> Function
applyPropagate (name, args, body)
  = (name, args, propagateConstants body)

------------------------------------------------------------------------
-- PART II

foldConst :: Exp -> Exp
-- Pre: the expression is in SSA form
foldConst (Const val)
  = Const val
foldConst (Var id)
  = Var id
foldConst (Apply op (Const c1) (Const c2))
  = Const (apply op c1 c2)
foldConst (Apply Add (Var id) (Const 0))
  = Var id
foldConst (Apply Add (Const 0) (Var id))
  = Var id
foldConst (Apply op e1 e2)
  = Apply op (foldConst e1) (foldConst e2)
foldConst (Phi (Const c1) (Const c2))
  | c1 == c2  = Const c1
  | otherwise = Phi (Const c1) (Const c2)
foldConst (Phi e1 e2)
  = Phi (foldConst e1) (foldConst e2)

sub :: Id -> Int -> Exp -> Exp
-- Pre: the expression is in SSA form
sub id value exp
  = foldConst(sub' id value exp)

-- Substitutes a value into an expression, but does not fold constants.
-- foldConst itself is recursive, so this will suffice.
sub' :: Id -> Int -> Exp -> Exp
sub' id value (Var varNodeId)
  | varNodeId == id = Const value
  | otherwise       = Var varNodeId
sub' id value (Const int)
  = Const int
sub' id value (Apply op exp1 exp2)
  = Apply op (sub' id value exp1) (sub' id value exp2)
sub' id value (Phi exp1 exp2)
  = Phi (sub' id value exp1) (sub' id value exp2)

-- Use (by uncommenting) any of the following, as you see fit...
type Worklist = [(Id, Int)]

scan :: Id -> Int -> Block -> (Worklist, Block)
scan id value []
  = ([], [])
scan id value (statement:statements)
  = (worklist ++ worklist', block ++ block')
    where
      (worklist, block) = processStatement id value statement
      (worklist', block') = scan id value statements

processStatement :: Id -> Int -> Statement -> (Worklist, Block)
processStatement id value (Assign statementId statementExp)
  = processAssign (Assign statementId substitutedExp)
    where
      substitutedExp = sub id value statementExp
processStatement id value (If conditionExp block1 block2)
  = (worklist1 ++ worklist2, [(If substitutedCondition block1' block2')])
    where
      substitutedCondition = sub id value conditionExp
      (worklist1, block1') = scan id value block1
      (worklist2, block2') = scan id value block2
processStatement id value (DoWhile block conditionExp)
  = (worklist, [(DoWhile block' substitutedCondition)])
    where
      substitutedCondition = sub id value conditionExp
      (worklist, block') = scan id value block

processAssign :: Statement -> (Worklist, Block)
-- Special case. No use in adding $return to the work-list, since it
-- isn't used anywhere.
processAssign (Assign "$return" (Const constValue))
  = ([], [(Assign "$return" (Const constValue))])
processAssign (Assign statementId (Const constValue)) 
  = ([(statementId, constValue)], []) 
processAssign (Assign statementId statementExp)
  = ([], [(Assign statementId statementExp)])

-- Function implementation looks fun, but it's a bit spicy
-- scan :: (Exp -> Exp) -> Block -> (Exp -> Exp, Block)
 
propagateConstants :: Block -> Block
-- Pre: the block is in SSA form
propagateConstants block 
  = propagateConstants' (initialWorklist, block)
    where
      (initialWorklist, _) = scan "$INVALID" 0 block

propagateConstants' :: (Worklist, Block) -> Block
propagateConstants' ([], block)
  = block
propagateConstants' ((id, value):bindings, block)
  = propagateConstants' (bindings ++ newBindings, newBlock)
    where
      (newBindings, newBlock) = scan id value block 

------------------------------------------------------------------------
-- Given functions for testing unPhi...

-- Applies unPhi to a given function...
applyUnPhi :: Function -> Function
applyUnPhi (name, args, body)
  = (name, args, unPhi body)

-- Combines propagation/folding and unPhi to convert a function from its
-- unoptimised SSA form to a final non-SSA form...
optimise :: Function -> Function
optimise (name, args, body)
  = (name, args, unPhi (propagateConstants body))

------------------------------------------------------------------------
-- PART III

unPhi :: Block -> Block
-- Pre: the block is in SSA form
unPhi []
  = []

-- This handles multiple statements, because the pattern will match after
-- the first statement is removed.
unPhi ((If exp block1 block2):(Assign id (Phi exp1 exp2)):statements)
  = unPhi ((If exp block1' block2'):statements)
    where
      block1' = block1 ++ [(Assign id exp1)]
      block2' = block2 ++ [(Assign id exp2)]

-- Need to propagate (because of possibility of nested blocks)
unPhi ((If exp block1 block2):statements)
  = (If exp (unPhi block1) (unPhi block2)):(unPhi statements)

-- Again this handles multiple statements because the pattern still matches
-- after the first statement is removed.
unPhi ((DoWhile ((Assign id (Phi exp1 exp2)):body) conditionExp):statements)
  = (Assign id exp1):(unPhi ((newDoWhileStatement):statements))
    where
      newDoWhileStatement = DoWhile (body ++ [(Assign id exp2)]) conditionExp

-- Need to propagate (because of possibility of nested blocks)
unPhi ((DoWhile block exp):statements)
  = (DoWhile (unPhi block) exp):(unPhi statements)

-- Catchall case
unPhi (statement:statements)
  = statement:(unPhi statements)

------------------------------------------------------------------------
-- Part IV

makeSSA :: Function -> Function
makeSSA (name, args, block) 
  = (name, args, transform block)

-- Converts a function body to SSA format.
transform :: Block -> Block
transform block
  = fst $ transform' block []    

-- Converts a function body to SSA format, by applying rules.
transform' :: Block -> UsageMap -> (Block, UsageMap)
transform' [] map
  = ([], map)

-- Begin with any needed intermediate expressions for the RHS.
-- Then execute the new assignment, and translate everything else.
transform' ((Assign id exp):statements) map
  = (intermediates ++ [newAssignment] ++ laterStatements, finalMap)
    where
      (intermediates, newExp, map') = splitExpression exp map
      (newId, _, map'') = getIdentifier id map'
      newAssignment = Assign newId newExp
      (laterStatements, finalMap) = transform' statements map''

-- If: Begin with any needed intermediate expressions for the condition.
-- Then, translate both blocks; don't reuse variables on either side.
-- Keep track of ALL variables that changed at some point ('mod-set').
-- You can get this from comparing maps.
-- At the end, assign each variable to PHI of its final value on each branch.
transform' ((If conditionExp block1 block2):statements) map
  = (intermediates 
       ++ [If newCondition block1' block2'] 
       ++ phiAssignments 
       ++ laterStatements,
     finalMap)
    where
      (intermediates, newCondition, map') = splitExpression conditionExp map
      (block1', map'') = transform' block1 map'
      (block2', map''') = transform' block2 map''
      (phiAssignments, postPhiMap) = plantIfPhis map' map'' map'''
      (laterStatements, finalMap) = transform' statements postPhiMap

-- Do/While: Each target of an assignment in the loop body must get a
-- PHI in the beginning, to the value at the end of the loop or the
-- value before entering the loop in the first place.
-- The while condition is evaluated with the mapping after processing the-
-- loop body.
transform' ((While block conditionExp):statements) map
  = undefined -- TODO timeout

-- Usage Map for handling new instances of variables
type UsageMap = [(Id, Int)]

-- Retrieves a fresh identifier for the given raw variable.
getIdentifier :: Id -> UsageMap -> (Id, Int, UsageMap)
getIdentifier "$return" map
  = ("$return", 0, map)
getIdentifier id []
  = (id ++ "0", 0, [(id, 1)])
getIdentifier id (binding:bindings)
  | id == bindingId 
    = (id ++ show(bindingCount), bindingCount, (id, bindingCount + 1):bindings)
  | otherwise       
    = (returnedId, returnedCount, binding:returnedBindings)
  where
    (bindingId, bindingCount) = binding
    (returnedId, returnedCount, returnedBindings) = getIdentifier id bindings

getCurrentVersion :: Id -> UsageMap -> (Id, UsageMap)
getCurrentVersion "$return" map
  = ("$return", map)
getCurrentVersion id []
  = (returnedId, returnedBindings)
  where
    (returnedId, _, returnedBindings) = getIdentifier id []
getCurrentVersion id (binding:bindings)
  | id == bindingId 
    = (id ++ show(bindingCount - 1), binding:bindings)
  | otherwise
    = (returnedId, returnedBindings)
  where
    (bindingId, bindingCount) = binding
    (returnedId, returnedBindings) = getCurrentVersion id bindings

-- Given an expression, converts it into a sequence of single assignments.
-- e.g. (Assign Id (Apply Add (Apply Add (Var x) (Var y)) (Var z)))
--      would become two statements, one for x + y (call this $i), and then
--      one for $i + z.
-- Pre: No phi functions
splitExpression :: Exp -> UsageMap -> (Block, Exp, UsageMap)
splitExpression (Const value) map
  = ([], Const value, map)
splitExpression (Var id) map
  = ([], Var (fst(getCurrentVersion id map)), map)
splitExpression (Apply op exp1 exp2) map
  | alreadySSA 
    = let
        (_, newExp1, _) = splitExpression exp1 map
        (_, newExp2, _) = splitExpression exp2 map
      in
        ([], Apply op newExp1 newExp2, map)
  | otherwise  
    = storeTemporary (Apply op exp1 exp2) map
  where
    alreadySSA = (isTerminal exp1) && (isTerminal exp2)

-- Pre: Expression is SSA assignable.
storeTemporary :: Exp -> UsageMap -> (Block, Exp, UsageMap)
storeTemporary (Const value) map
  = ([], Const value, map)
storeTemporary (Var id) map
  = ([], Var (fst (getCurrentVersion id map)), map)
storeTemporary (Apply op exp1 exp2) map
  | isSSAAssignable (Apply op exp1 exp2)
    = let
        internalId = "$internal"
        (newId, _, map') = getIdentifier internalId map
        (_, newExp1, _) = splitExpression exp1 map
        (_, newExp2, _) = splitExpression exp2 map
      in
        ([Assign newId (Apply op exp1 exp2)], Var newId, map')
  | otherwise
    = let
        (assignments1, newExp1, map') = storeTemporary exp1 map
        (assignments2, newExp2, map'') = storeTemporary exp2 map'
      in
        (assignments1 ++ assignments2, (Apply op newExp1 newExp2), map'')

-- Determines whether an expression is 'terminal' - that is, whether it is
-- merely a Const or Var, or a single operator application to Consts/Vars.
isTerminal :: Exp -> Bool
isTerminal (Const value) 
  = True
isTerminal (Var id) 
  = True
isTerminal _ 
  = False

-- Determines whether an expression is permissible as the RHS of an assignment
-- in SSA.
isSSAAssignable :: Exp -> Bool
isSSAAssignable (Const value) 
  = True
isSSAAssignable (Var id) 
  = True
isSSAAssignable (Apply op exp1 exp2)
  = isTerminal exp1 && isTerminal exp2

-- Computes all required PHI(v1, v2) values for variables
plantIfPhis :: UsageMap -> UsageMap -> UsageMap -> (Block, UsageMap)
plantIfPhis original afterIf afterElse
  = plantIfPhis' original afterIf afterElse afterElse allChanged
  where
    allChanged = union (modset original afterIf) (modset original afterElse)

-- Compute values to be used for PHI for one variable at a time
plantIfPhis' :: UsageMap -> UsageMap -> UsageMap -> UsageMap -> 
                [Id] -> (Block, UsageMap)
plantIfPhis' original afterIf afterElse final []
  = ([], final)
plantIfPhis' original afterIf afterElse accumulator (id:ids)
  = ([Assign newId (Phi (Var varAfterIf) (Var varAfterElse))] ++ otherPhis,
     final)
  where
    oldVersion = lookupWithFailure id original
    versionAfterIf = lookupWithFailure id afterIf
    versionAfterElse = lookupWithFailure id afterElse
    realVersionAfterElse 
      = if versionAfterIf == versionAfterElse
        then oldVersion
        else versionAfterElse
    varAfterIf = id ++ show(versionAfterIf)
    varAfterElse = id ++ show(realVersionAfterElse)
    (newId, _, newMap) = getIdentifier id accumulator
    (otherPhis, final) 
      = plantIfPhis' original afterIf afterElse newMap ids

-- Computes the variables that have changed between two usage maps.
modset :: UsageMap -> UsageMap -> [Id]
modset _ []
  = []
modset before (newBinding:bindings)
  | changed   = bindingId:(modset before bindings)
  | otherwise = modset before bindings
  where
    (bindingId, bindingVersion) = newBinding
    oldVersion = lookupWithFailure bindingId before
    changed = oldVersion /= bindingVersion

lookupWithFailure :: Id -> UsageMap -> Int
lookupWithFailure id map
  = fromMaybe (0) (lookup id map) - 1 -- TODO hack

------------------------------------------------------------------------
-- Predefined functions for displaying functions and blocks...

opNames
  = [(Add, "+"), (Mul, "*"), (Eq, "=="), (Gtr, ">")]

precTable
  = [(Add, 1), (Mul, 2), (Eq, 0), (Gtr, 0)]

prec op
  = lookUp op precTable

showArgs [] 
  = ""
showArgs as
  = foldr1 (\a s -> a ++ (", " ++ s)) as

showExp :: Int -> Exp -> String
showExp _ (Const n) 
  = show n
showExp _ (Var id) 
  = id
showExp n (Apply op' e e') 
  | n > n'    = "(" ++ s ++ ")"
  | otherwise = s
  where 
    n' = prec op'
    s = showExp n' e ++ " " ++ fromJust (lookup op' opNames ) ++ " " ++ 
        showExp n' e'
showExp _ (Phi e e')
  = "PHI(" ++ showArgs (map (showExp 0) [e, e']) ++ ")"

showLine s n k
  =  putStrLn (show n ++ ": " ++ replicate (k + 2 - length (show n)) ' ' ++ s)

showBlock' b n
  = showBlock'' b n 2
  where
    showBlock'' :: Block -> Int -> Int -> IO Int
    showBlock'' [] n k
      = return n
    showBlock'' (s : b) n k
      = do n'  <- showStatement s n k
           n'' <- showBlock'' b n' k
           return n''
    showStatement (Assign id e) n k
      = do showLine (id ++ " = " ++ showExp 0 e) n k
           return (n + 1)
    showStatement (If p q []) n k
      = do showLine ("if " ++ "(" ++ showExp 0 p ++ ") {") n k
           n' <- showBlock'' q (n + 1) (k + 2)
           showLine "}" n' k 
           return (n' + 1)
    showStatement (If p q r) n k
      = do showLine ("if " ++ "(" ++ showExp 0 p ++ ") {") n k
           n'  <- showBlock'' q (n + 1) (k + 2)
           showLine "} else {" n' k 
           n'' <- showBlock'' r (n' + 1) (k + 2)
           showLine "}" n'' k
           return (n'' + 1)
    showStatement (DoWhile b p) n k
      = do showLine "do {" n k
           n' <- showBlock'' b (n + 1) (k + 2)
           showLine ("} while " ++ showExp 9 p) n' k
           return (n' + 1)

showFun :: Function -> IO()
showFun (name, args, body)
  = do putStrLn ("1:  " ++ name ++ "(" ++ showArgs args ++ ") {")
       n <- showBlock' body 2
       showLine "}" n 0

showBlock ::  Block -> IO()
showBlock b
  = do n <- showBlock' b 1
       return ()

------------------------------------------------------------------------
-- Example state and expressions for testing...

s1 :: State
s1 = [("x", 7), ("y", 8)]

e1, e2, e3, e4, e5 :: Exp
e1 = Var "x"
e2 = Apply Mul (Apply Add (Var "x") (Const 1)) (Var "y")
e3 = Phi (Const 2) (Const 2)
e4 = Apply Add (Const 0) (Var "x")
e5 = Apply Add (Var "a") (Var "x")

------------------------------------------------------------------------
-- Example functions...

-- Figure 1...
example :: Function
example 
  = ("example",["x"],[Assign "a" (Const 1),Assign "b" (Apply Add (Var "x")
    (Const 2)),Assign "c" (Const 3),If (Apply Eq (Var "x") (Const 10)) 
    [Assign "a" (Const 1),Assign "c" (Const 5)] [],Assign "d" 
    (Apply Add (Var "a") (Const 3)),Assign "e" (Apply Add (Var "d") (Var "b")),
    Assign "$return" (Apply Add (Var "e") (Var "c"))])
    
exampleSSA :: Function
exampleSSA
  = ("example",["x"],[Assign "a0" (Const 1),Assign "b0" (Apply Add (Var "x")
    (Const 2)),Assign "c0" (Const 3),If (Apply Eq (Var "x") (Const 10)) [Assign
    "a1" (Const 1),Assign "c1" (Const 5)] [],Assign "a2" (Phi (Var "a1") (Var
    "a0")),Assign "c2" (Phi (Var "c1") (Var "c0")),Assign "d0" (Apply Add (Var
    "a2") (Const 3)),Assign "e0" (Apply Add (Var "d0") (Var "b0")),
    Assign "$return" (Apply Add (Var "e0") (Var "c2"))])
    
exampleSSAPropagated :: Function
exampleSSAPropagated
  = ("example",["x"],[Assign "b0" (Apply Add (Var "x") (Const 2)),If (Apply Eq
    (Var "x") (Const 10)) [] [],Assign "c2" (Phi (Const 5) (Const 3)),
    Assign "e0" (Apply Add (Const 4) (Var "b0")),Assign "$return" 
    (Apply Add (Var "e0") (Var "c2"))])

exampleOptimised :: Function
exampleOptimised 
  = ("example",["x"],[Assign "b0" (Apply Add (Var "x") (Const 2)),If (Apply Eq
    (Var "x") (Const 10)) [Assign "c2" (Const 5)] [Assign "c2" (Const 3)],Assign
    "e0" (Apply Add (Const 4) (Var "b0")),Assign "$return" (Apply Add (Var "e0")
    (Var "c2"))])
    

-- Figure 2 (there is no SSA version of this)...
fact :: Function
fact 
  = ("fact", 
     ["n"], 
     [If (Apply Eq (Var "n") (Const 0))
        [Assign "$return" (Const 1)]
        [Assign "prod" (Const 1),
         Assign "i" (Var "n"),
         DoWhile 
           [Assign "prod" (Apply Mul (Var "prod") (Var "i")),
            Assign "i" (Apply Add (Var "i") (Const (-1)))
           ] 
           (Apply Gtr (Var "i") (Const 0)),
         Assign "$return" (Var "prod")
        ]
     ]
    )


-- Summation loop, specialised loop for the case k=0...
loop :: Function
loop 
  = ("loop",["n"],[Assign "i" (Var "n"),Assign "k" (Const 0),Assign "sum"
    (Const 0),If (Apply Eq (Var "i") (Const 0)) [Assign "$return" (Const 0)]
    [DoWhile [Assign "sum" (Apply Add (Var "sum") (Apply Mul (Apply Add 
    (Var "i") (Apply Mul (Const 2) (Var "k"))) (Apply Add (Apply Add (Var "i") 
    (Apply Mul (Const 2) (Var "k"))) (Const 1)))),Assign "i" (Apply Add 
    (Var "i") (Const (-1)))] (Apply Gtr (Var "i") (Const 0)),
    Assign "$return" (Var "sum")]])
    
loopSSA :: Function
loopSSA
  = ("loop",["n"],[Assign "i0" (Var "n"),Assign "k0" (Const 0),Assign "sum0"
    (Const 0),If (Apply Eq (Var "i0") (Const 0)) [Assign "$return" (Const 0)]
    [DoWhile [Assign "sum1" (Phi (Var "sum0") (Var "sum2")),Assign "i1" 
    (Phi (Var "i0") (Var "i2")),Assign "k1" (Apply Mul (Var "k0") (Const 2)),
    Assign "a0" (Apply Add (Var "i1") (Var "k1")),Assign "k2" (Apply Mul 
    (Var "k0") (Const 2)),Assign "b0" (Apply Add (Var "k2") (Const 1)),
    Assign "b1" (Apply Add (Var "i1") (Var "b0")),Assign "m0" (Apply Mul 
    (Var "a0") (Var "b1")),Assign "sum2" (Apply Add (Var "sum1") (Var "m0")),
    Assign "i2" (Apply Add (Var "i1") (Const (-1)))] (Apply Gtr (Var "i2") 
    (Const 0)),Assign "$return" (Var "sum2")]])
    
loopSSAPropagated :: Function
loopSSAPropagated 
  = ("loop",["n"],[Assign "i0" (Var "n"),If (Apply Eq (Var "i0") (Const 0))
    [Assign "$return" (Const 0)] [DoWhile [Assign "sum1" (Phi (Const 0) (Var
    "sum2")),Assign "i1" (Phi (Var "i0") (Var "i2")),Assign "a0" (Var "i1"),
    Assign "b1" (Apply Add (Var "i1") (Const 1)),Assign "m0" (Apply Mul 
    (Var "a0") (Var "b1")),Assign "sum2" (Apply Add (Var "sum1") (Var "m0")),
    Assign "i2" (Apply Add (Var "i1") (Const (-1)))] (Apply Gtr (Var "i2") 
    (Const 0)),Assign "$return" (Var "sum2")]])
 
loopOptimised :: Function
loopOptimised 
  = ("loop",["n"],[Assign "i0" (Var "n"),If (Apply Eq (Var "i0") (Const 0))
    [Assign "$return" (Const 0)] [Assign "sum1" (Const 0),Assign "i1" (Var
    "i0"),DoWhile [Assign "a0" (Var "i1"),Assign "b1" (Apply Add (Var "i1") 
    (Const 1)),Assign "m0" (Apply Mul (Var "a0") (Var "b1")),Assign "sum2" 
    (Apply Add (Var "sum1") (Var "m0")),Assign "i2" (Apply Add (Var "i1") 
    (Const (-1))),Assign "sum1" (Var "sum2"),Assign "i1" (Var "i2")] 
    (Apply Gtr (Var "i2") (Const 0)),Assign "$return" (Var "sum2")]])
    

-- Basic block (no conditionals or loops)...
basicBlock :: Function
basicBlock 
  = ("basicBlock",[],[Assign "x" (Const 1),Assign "y" (Const 2),Assign "x"
    (Apply Add (Var "x") (Var "y")),Assign "y" (Apply Mul (Var "x") (Const
    3)),Assign "$return" (Var "y")])
    
basicBlockSSA :: Function
basicBlockSSA 
  = ("basicBlock",[],[Assign "x0" (Const 1),Assign "y0" (Const 2),Assign "x1"
    (Apply Add (Var "x0") (Var "y0")),Assign "y1" (Apply Mul (Var "x1") (Const
    3)),Assign "$return" (Var "y1")])
    
basicBlockSSAPropagated :: Function
basicBlockSSAPropagated
  = ("basicBlock", [], [Assign "$return" (Const 9)])

-- (This is the same as above, as there were no phi functions.)
basicBlockOptimised :: Function
basicBlockOptimised
  = ("basicBlock", [], [Assign "$return" (Const 9)])

-- Computes the maximum of two integers; useful for testing unPhi...
max2 :: Function
max2 
  = ("max2",["x","y"],[If (Apply Gtr (Var "x") (Var "y")) [Assign "m" (Var "x")]
    [Assign "m" (Var "y")],Assign "$return" (Var "m")])

max2SSA :: Function
max2SSA 
  = ("max2",["x","y"],[If (Apply Gtr (Var "x") (Var "y")) [Assign "m0" (Var
    "x")] [Assign "m1" (Var "y")],Assign "m2" (Phi (Var "m0") (Var "m1")),Assign
    "$return" (Var "m2")])

max2SSAPropagated :: Function
max2SSAPropagated
  = ("max2",["x","y"],[If (Apply Gtr (Var "x") (Var "y")) [Assign "m0" (Var
    "x")] [Assign "m1" (Var "y")],Assign "m2" (Phi (Var "m0") (Var "m1")),Assign
    "$return" (Var "m2")])

max2Optimised :: Function
max2Optimised 
  = ("max2",["x","y"],[If (Apply Gtr (Var "x") (Var "y")) [Assign "m0" (Var
    "x"),Assign "m2" (Var "m0")] [Assign "m1" (Var "y"),Assign "m2" (Var
    "m1")],Assign "$return" (Var "m2")])


