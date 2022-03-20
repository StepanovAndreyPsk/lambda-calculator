{-# LANGUAGE FlexibleContexts #-}
import Text.ParserCombinators.Parsec

import Control.Monad.State
import Data.List

type Symb = String

infixl 2 :@

data Expr
  = Var Symb
  | Expr :@ Expr
  | Lam Symb Expr
  deriving Eq

freeVars :: Expr -> [Symb]
freeVars (Var x) = [x]
freeVars (s :@ t) = freeVars s `union` freeVars t
freeVars (Lam x expr) = freeVars expr \\ [x]

getFreshVar = do
  i <- get
  put (i + 1)
  return $ "a_" ++ show i

subst :: Symb -> Expr -> Expr -> Expr
subst v n m = evalState (subst' v n m) 1

subst' v n t@(Var m)
  | m == v = return n
  | otherwise = return t
subst' v n (p :@ q) = do
  s <- subst' v n p
  t <- subst' v n q
  return $ s :@ t
subst' v n l@(Lam x expr)
  | v == x = return l
  | x `notElem` freeVars n = do
    body <- subst' v n expr
    return $ Lam x body
  | otherwise = do 
      x' <- getFreshVar
      body <- subst' x (Var x') expr  
      body' <- subst' v n body
      return $ Lam x' body' 

infix 1 `alphaEq`

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var x) (Var y) = x == y 
alphaEq (m :@ n) (m' :@ n') = (m `alphaEq` m') && (n `alphaEq` n') 
alphaEq arg1@(Lam x body) arg2@(Lam x' body')
  | x == x' = body `alphaEq` body'
  | x `notElem` freeVars body' = Lam x body `alphaEq` Lam x (subst x' (Var x) body')
  | otherwise = False
alphaEq _ _ = False

reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var _) = Nothing 
reduceOnce ((Lam x body) :@ n) = Just $ subst x n body   
reduceOnce (m :@ n) = case reduceOnce m of 
  Just expr -> Just $ expr :@ n
  Nothing -> case reduceOnce n of 
    Just expr -> Just $ m :@ expr 
    Nothing -> Nothing 
reduceOnce (Lam x body) = case reduceOnce body of 
  Just expr -> Just $ Lam x expr 
  Nothing -> Nothing 

nf :: Expr -> Expr
nf e = maybe e nf (reduceOnce e)

infix 1 `betaEq`

betaEq :: Expr -> Expr -> Bool 
betaEq e1 e2 = nf e1 `alphaEq` nf e2

instance Show Expr where
    show (Var v) = v
    show (Var v1 :@ Var v2) = v1 ++ v2 
    show (Var v :@ e) = v ++ " (" ++ show e ++ ")"
    show (e1 :@ e2) = "(" ++ show e1 ++ ") (" ++ show e2 ++ ")"
    show (Lam v e) = "\\" ++ v ++ " -> " ++ show e
instance Read Expr where
    readsPrec _ s = case parseStr s of
        Left _ -> undefined
        Right v -> [(v, "")]
parseStr :: String -> Either ParseError Expr
parseStr = parse (do
    expr <- parseExpr
    eof
    return expr) ""

parseId :: Parser String
parseId = do
    l <- letter
    dig <- many alphaNum
    _ <- spaces
    return (l : dig)

parseVar :: Parser Expr
parseVar = Var <$> parseId

parseExprInBrackets :: Parser Expr
parseExprInBrackets = do
    _ <- char '('>> spaces
    expr <- parseExpr
    _ <- char ')' >> spaces
    return expr

parseExpr :: Parser Expr
parseExpr = try parseTerm <|> try parseAtom

parseAtom :: Parser Expr
parseAtom = try parseLam <|> try parseVar <|> try parseExprInBrackets

parseTerm :: Parser Expr
parseTerm = parseAtom `chainl1` return (:@)

parseLam :: Parser Expr
parseLam = do
    _ <- char '\\' >> spaces
    ids <- many1 parseId
    _ <- string "->" >> spaces
    expr <- parseExpr
    return $ foldr Lam expr ids
