import Data.Char
import Data.List
import Data.Fixed


-- ======================================= --
-- ============= TYPES STUFF ============= --
-- ======================================= --

type Vars = String
type Name = String
type Value = Double
type Env = [(Vars,Value)]

data AExpr = Var Vars | Const Value | Add AExpr AExpr | Mul AExpr AExpr
           | Sub AExpr AExpr | Div AExpr AExpr | Mod AExpr AExpr | Sin AExpr 
           | Cos AExpr | Tan AExpr | FindHypotenuse AExpr AExpr | FindLeg AExpr AExpr
           | Exp AExpr AExpr | Ln AExpr | Fact AExpr | Inter AExpr AExpr AExpr
           | Popul AExpr AExpr AExpr | FCall Name [AExpr]
  deriving Show

data BOps = AddOp | MulOp | SubOp | DivOp | ModOp | FindHop | FindL
          | ExpOp
  deriving Show

data UOps = SinOp | CosOp | TanOp | LnOp | FactOp
  deriving Show

data TOps = IntOp | PopOp
  deriving Show

data Token = VSym String | CSym Double | BOp BOps | LPar | RPar | PA AExpr
           | Err String | AssignOp | QuitK | UOp UOps | TOp TOps | PList [AExpr]
           | Comma | Eq | DefK | NSym String
  deriving Show

-- ======================================= --
-- =========== EVALUATION STUFF ========== --
-- ======================================= --


eval :: ([FunDef],Env) -> AExpr -> Value
eval (fd,env) (Var x) = maybe (error "Variable not found") id (lookup x env)
eval (fd,env) (FindHypotenuse a b) = sqrt ((eval (fd,env) a)^2 + (eval (fd,env) b)^2)
eval (fd,env) (FindLeg a b) 
  | eval (fd,env) a <= eval (fd,env) b = sqrt ((eval (fd,env) b)^2 - (eval (fd,env) a)^2)
  | otherwise = sqrt ((eval (fd,env) a)^2 - (eval (fd,env) b)^2)
eval env (Const n) = n
eval env (Add e1 e2) = eval env e1 + eval env e2
eval env (Mul e1 e2) = eval env e1 * eval env e2
eval env (Sub e1 e2) = eval env e1 - eval env e2
eval env (Div e1 e2) = eval env e1 / eval env e2
eval env (Mod e1 e2) = mod' (eval env e1) (eval env e2)
eval env (Exp e1 e2) = eval env e1 ** eval env e2
eval env (Sin e) = sin (eval env e)
eval env (Cos e) = cos (eval env e)
eval env (Tan e) = tan (eval env e)
eval env (Fact e)
  | isInteger (eval env e) = product [1..eval env e]
  | otherwise = error "Factorial only works on integers"
eval env (Inter p r t) = eval env p * (1 + eval env r * eval env t)
eval env (Popul p r t) = eval env p * exp (eval env r * eval env t)
eval env (Ln e) = log (eval env e)
eval e@(fds,env) (FCall f args) =     -- call-by-name evaluation
  let fd = lookupFDef f fds             :: FunDef
      env' = zip (vars fd) args         :: [(Vars,AExpr)]
      body' = substList env' (body fd)  :: AExpr
   in eval (fds,env) body'

lookupFDef :: Name -> [FunDef] -> FunDef
lookupFDef n [] = error $ "Cannot find function " ++ n
lookupFDef n (fd:fds) | (n == fname fd) = fd
                      | otherwise = lookupFDef n fds

substList :: [(Vars,AExpr)] -> AExpr -> AExpr
-- substList [] e = e
-- substList (va:vas) e = subst va (substList vas e)
substList lst e = foldr subst e lst

subst :: (Vars,AExpr) -> AExpr -> AExpr
subst (x,e) (Var y) | x == y = e
subst (x,e) (Var y) | x /= y = Var y
subst (x,e) (Const n)        = Const n
subst (x,e) (Add e1 e2)      = Add (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (Mul e1 e2)      = Mul (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (Sub e1 e2)      = Sub (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (Div e1 e2)      = Div (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (Mod e1 e2)      = Mod (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (Exp e1 e2)      = Exp (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (Sin e1)         = Sin (subst (x,e) e1)
subst (x,e) (Cos e1)         = Cos (subst (x,e) e1)
subst (x,e) (Tan e1)         = Tan (subst (x,e) e1)
subst (x,e) (Fact e1)        = Fact (subst (x,e) e1)
subst (x,e) (Inter e1 e2 e3) = Inter (subst (x,e) e1) (subst (x,e) e2) (subst (x,e) e3)
subst (x,e) (Popul e1 e2 e3) = Popul (subst (x,e) e1) (subst (x,e) e2) (subst (x,e) e3)
subst (x,e) (Ln e1)          = Ln (subst (x,e) e1)
subst (x,e) (FindHypotenuse e1 e2) = FindHypotenuse (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (FindLeg e1 e2) = FindLeg (subst (x,e) e1) (subst (x,e) e2)
subst (x,e) (FCall f args)   = FCall f (map (subst (x,e)) args)

isInteger :: Double -> Bool
isInteger x = x == fromInteger (round x)

-- ======================================= --
-- ============ PARSING STUFF ============ --
-- ======================================= --


parseAExpr :: [Token] -> AExpr
parseAExpr s = case sr [] s of
  [PA e]  -> e
  [Err e] -> error $ "Lexical error: " ++ e
  s       -> error $ "Parse error: " ++ show s

sr :: [Token] -> [Token] -> [Token]
-- reduce phase
sr (VSym x : s) i                    = sr (PA (Var x) : s)     i -- AExpr -> Var x
sr (CSym n : s) i                    = sr (PA (Const n) : s)   i -- AExpr -> Const n
sr (LPar : NSym n : s) i             = sr (PList [] : NSym n : s) i
sr (Comma : PA e : PList l : s) i    = sr (PList (e:l) : s) i
sr (RPar : PA e : PList l : s) i     = sr (RPar : PList (e:l) : s) i
sr (RPar : PList l : NSym n : s) i   = sr (PA (FCall n (reverse l)) : s) i
sr t@(PA e2 : BOp op1 : PA e1 : s) (BOp op2 : i) | alevel op2 > alevel op1
                                     = sr (BOp op2 : t) i
sr (PA e2 : PA e1 : BOp FindHop : s) i = sr (PA (FindHypotenuse e1 e2) : s) i -- AExpr -> findHypotenuse ( AExpr, AExpr )
sr (PA e2 : PA e1 : BOp FindL : s) i = sr (PA (FindLeg e1 e2) : s) i -- AExpr -> findLeg ( AExpr, AExpr )
sr (PA e2 : BOp AddOp : PA e1 : s) i = sr (PA (Add e1 e2) : s) i -- AExpr -> AExpr + AExpr
sr (PA e2 : BOp MulOp : PA e1 : s) i = sr (PA (Mul e1 e2) : s) i -- AExpr -> AExpr * AExpr
sr (PA e2 : BOp SubOp : PA e1 : s) i = sr (PA (Sub e1 e2) : s) i -- AExpr -> AExpr - AExpr
sr (PA e2 : BOp DivOp : PA e1 : s) i = sr (PA (Div e1 e2) : s) i -- AExpr -> AExpr / AExpr
sr (PA e2 : BOp ModOp : PA e1 : s) i = sr (PA (Mod e1 e2) : s) i -- AExpr -> AExpr % AExpr
sr (PA e2 : BOp ExpOp : PA e1 : s) i = sr (PA (Exp e1 e2) : s) i -- AExpr -> AExpr ^ AExpr
sr (PA e : UOp SinOp : s) i          = sr (PA (Sin e) : s)     i -- AExpr -> sin ( AExpr )
sr (PA e : UOp CosOp : s) i          = sr (PA (Cos e) : s)     i -- AExpr -> cos ( AExpr )
sr (PA e : UOp TanOp : s) i          = sr (PA (Tan e) : s)     i -- AExpr -> tan ( AExpr )
sr (PA e : UOp LnOp : s) i           = sr (PA (Ln e) : s)      i -- AExpr -> ln ( AExpr )
sr (UOp FactOp : PA e : s) i         = sr (PA (Fact e) : s)    i -- AExpr -> fact ( AExpr )
sr (RPar : PA e : LPar : s) i        = sr (PA e : s) i           -- AExpr -> ( AExpr )
sr (PA t : PA r : PA p : TOp IntOp : s) i = sr (PA (Inter p r t) : s) i -- AExpr -> interest ( AExpr, AExpr, AExpr )
sr (PA t : PA r : PA p : TOp PopOp : s) i = sr (PA (Popul p r t) : s) i -- AExpr -> population ( AExpr, AExpr, AExpr )
-- shift phase
sr s (i:is) = sr (i:s) is
-- base case
-- sr [PA e] []                         = e
sr (Err e : s) i = [Err e]
sr s [] = s

parseFunDef :: String -> FunDef
parseFunDef s =
  let lexed = lexer s
      parsed = sr [] lexed
      unvar (Var x) = x
   in case parsed of
        [PA e, Eq, PA (FCall f l)] -> FunDef f (map unvar l) e
        _ -> error "Invalid function definition"


data FunDef = FunDef { fname :: Name,
                       vars  :: [Vars],
                       body  :: AExpr }
  deriving (Show)

-- PEMDAS
alevel :: BOps -> Integer
alevel ExpOp = 100
alevel MulOp = 80
alevel DivOp = 60
alevel ModOp = 50
alevel AddOp = 40
alevel SubOp = 20


-- ======================================= --
-- ============= LEXING STUFF ============ --
-- ======================================= --


lexer :: String -> [Token]
lexer "" = []
lexer xs | isPrefixOf "\DEL" xs = lexer (drop 4 xs)
lexer xs | isPrefixOf "quit" xs = QuitK : lexer (drop 4 xs)
lexer xs | isPrefixOf "def:" xs = DefK : lexer (drop 4 xs)
lexer xs | isPrefixOf "findHypotenuse" xs = BOp FindHop : lexer (drop 14 xs)
lexer xs | isPrefixOf "findLeg" xs = BOp FindL : lexer (drop 7 xs)
lexer xs | isPrefixOf "interest" xs = TOp IntOp : lexer (drop 8 xs)
lexer xs | isPrefixOf "population" xs = TOp PopOp : lexer (drop 10 xs)
lexer ('s':'i':'n':xs) = UOp SinOp : lexer xs
lexer ('c':'o':'s':xs) = UOp CosOp : lexer xs
lexer ('t':'a':'n':xs) = UOp TanOp : lexer xs
lexer ('l':'n':xs) = UOp LnOp : lexer xs
lexer (x:xs) | isUpper x = let (hd,tl) = span isAlpha xs
                           in NSym (x:hd) : lexer tl
lexer (x:xs) | isLower x = let (hd,tl) = span (\x -> isAlphaNum x || x == '_') xs
                           in VSym  (x:hd) : lexer tl
lexer (x:xs) | isDigit x = let (hd,tl) = span (\c -> isDigit c || c == '.') (x:xs)
                           in case reads hd of
                                [(n, "")] -> CSym n : lexer tl
                                _ -> error $ "Invalid double: " ++ hd
lexer ('+':xs) = BOp AddOp : lexer xs
lexer ('*':xs) = BOp MulOp : lexer xs
lexer ('-':xs) = BOp SubOp : lexer xs
lexer ('/':xs) = BOp DivOp : lexer xs
lexer ('%':xs) = BOp ModOp : lexer xs
lexer ('(':xs) = LPar : lexer xs
lexer (')':xs) = RPar : lexer xs
lexer ('^':xs) = BOp ExpOp : lexer xs
lexer ('!':xs) = UOp FactOp : lexer xs
lexer (':':'=':xs) = AssignOp : lexer xs
lexer ('=':xs) = Eq : lexer xs
lexer (',':xs) = Comma : lexer xs
lexer (x:xs) | isSpace x = lexer xs
lexer s = [Err s]


-- ======================================= --
-- =========== I/O AND UI STUFF ========== --
-- ======================================= --

repl :: ([FunDef],Env) -> IO ()
repl e@(fd,env) = do
  input <- getLine
  let lexed = lexer input
  putStrLn "The result of running the lexer is:"
  putStrLn (show lexed)
  case lexed of
    [QuitK]                  -> return ()
    [Err s]                  -> do
      putStrLn "Invalid input, try again."
      repl e
    [DefK]                   -> do
      putStrLn "Enter your function as so: FN_NAME(x,y,z,...) = EXPR"
      input <- getLine
      let function = parseFunDef input
      repl (function:fd,env)
      
    (VSym x : AssignOp : ts) -> do
      let parsedTokens = parseAExpr ts
      let newval = eval e parsedTokens
      repl (fd,(x,newval):env)
    ts                       -> do
      let parsed = parseAExpr lexed
      putStrLn "The result of running the parser is:"
      putStrLn (show parsed)
      let evaled = eval e parsed
      putStrLn "The result of evaluation is:"
      putStrLn (show evaled)
      repl (fd,env)


main :: IO ()
main = do 
  putStrLn "===== NEW FUNCTIONS ====="
  putStrLn "findHypotenuse x y"
  putStrLn "findLeg x y"
  putStrLn "interest p r t"
  putStrLn "population p r t"
  putStrLn "sin x | cos x | tan x | ln x | x! | x^y"
  putStrLn "DEFINE YOUR FUNCTION --> Type \"def:\" Then press enter and type your function"
  putStrLn "========================"
  repl ([],[])

