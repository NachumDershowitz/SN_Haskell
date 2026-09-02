{-# OPTIONS_GHC -Wall #-}

module Main where

import Numeric.Natural (Natural)

import Data.Maybe (fromMaybe)
infixr 5 :->

-- First-order syntax, used when terms must be inspected and printed.

data Ty = O | Ty :-> Ty
  deriving (Eq, Show)

data Var = V String Ty
  deriving (Eq, Show)

data Term
  = TVar Var
  | App Term Term
  | Lam Var Term
  deriving (Eq, Show)

vname :: Var -> String
vname (V x _) = x

vty :: Var -> Ty
vty (V _ a) = a

ppTy :: Ty -> String
ppTy O = "o"
ppTy (a :-> b) = ppDom a ++ " -> " ++ ppTy b
  where
    ppDom O = "o"
    ppDom t = "(" ++ ppTy t ++ ")"

ppBinderTy :: Ty -> String
ppBinderTy O = "o"
ppBinderTy t = "(" ++ ppTy t ++ ")"

ppBinder :: Var -> String
ppBinder x = vname x ++ ":" ++ ppBinderTy (vty x)

ppTerm :: Term -> String
ppTerm = go 0
  where
    par :: Bool -> String -> String
    par True  s = "(" ++ s ++ ")"
    par False s = s

    go :: Int -> Term -> String
    go _ (TVar x) = vname x
    go p (Lam x m) =
      par (p > 0) ("\\" ++ ppBinder x ++ ". " ++ go 0 m)
    go p (App m n) =
      par (p > 1) (go 1 m ++ " " ++ go 2 n)

typeOf :: Term -> Either String Ty
typeOf (TVar x) = Right (vty x)
typeOf (Lam x m) = do
  b <- typeOf m
  Right (vty x :-> b)
typeOf (App m n) = do
  tm <- typeOf m
  tn <- typeOf n
  case tm of
    a :-> b
      | a == tn   -> Right b
      | otherwise -> Left ("type mismatch: expected " ++ show a ++
                           ", found " ++ show tn)
    O -> Left "application of a base-type term"

data Meas
  = N Natural
  | F (Meas -> Meas) Natural

star :: Meas -> Natural
star (N n)   = n
star (F _ n) = n

dot :: Meas -> Meas -> Meas
dot (F f _) a = f a
dot (N _)   _ = error "dot of a base-type measure"

add :: Natural -> Meas -> Meas
add k (N n)   = N (n + k)
add k (F f n) = F (\a -> add k (f a)) (n + k)

canon :: Ty -> Natural -> Meas
canon O n = N n
canon (_ :-> b) n = F (\a -> canon b (n + star a)) n

type Env = [(Var, Meas)]

value :: Env -> Var -> Meas
value env x = fromMaybe (canon (vty x) 0) (lookup x env)

bra :: Env -> Term -> Meas
bra env (TVar x)  = value env x
bra env (App m n) = dot (bra env m) (bra env n)
bra env (Lam x m) =
  F (\a -> add (star a + 1) (bra ((x, a) : env) m))
    (star (bra ((x, canon (vty x) 0) : env) m))

measure :: Term -> Natural
measure = star . bra []

measureChecked :: Term -> Either String Natural
measureChecked m = do
  _ <- typeOf m
  Right (measure m)

vars :: Term -> [Var]
vars (TVar x) = [x]
vars (App m n) = vars m ++ vars n
vars (Lam x m) = x : vars m

freeVars :: Term -> [Var]
freeVars (TVar x) = [x]
freeVars (App m n) = freeVars m ++ freeVars n
freeVars (Lam x m) = filter (/= x) (freeVars m)

freshLike :: Var -> [Var] -> Var
freshLike (V x a) used = go (0 :: Natural)
  where
    go i =
      let y = V (x ++ "_" ++ show i) a
       in if y `elem` used then go (i + 1) else y

renameFree :: Var -> Var -> Term -> Term
renameFree old new (TVar x)
  | x == old  = TVar new
  | otherwise = TVar x
renameFree old new (App m n) =
  App (renameFree old new m) (renameFree old new n)
renameFree old new (Lam x m)
  | x == old  = Lam x m
  | otherwise = Lam x (renameFree old new m)

subst :: Var -> Term -> Term -> Term
subst x s (TVar y)
  | x == y    = s
  | otherwise = TVar y
subst x s (App m n) = App (subst x s m) (subst x s n)
subst x s (Lam y m)
  | y == x = Lam y m
  | y `elem` freeVars s =
      let y' = freshLike y (vars m ++ vars s ++ [x])
       in Lam y' (subst x s (renameFree y y' m))
  | otherwise = Lam y (subst x s m)

oneBeta :: Term -> Maybe Term
oneBeta (TVar _) = Nothing
oneBeta (App (Lam x m) n) = Just (subst x n m)
oneBeta (App m n) =
  case oneBeta m of
    Just m' -> Just (App m' n)
    Nothing ->
      case oneBeta n of
        Just n' -> Just (App m n')
        Nothing -> Nothing
oneBeta (Lam x m) = fmap (Lam x) (oneBeta m)

oneCBN :: Term -> Maybe Term
oneCBN (App (Lam x m) n) = Just (subst x n m)
oneCBN (App m n) = fmap (\m' -> App m' n) (oneCBN m)
oneCBN _ = Nothing

steps :: (Term -> Maybe Term) -> Term -> [Term]
steps step t = t : maybe [] (steps step) (step t)

printStep :: (Int, Term) -> IO ()
printStep (i, t) =
  putStrLn (show i ++ ". " ++ ppTerm t ++ measureText)
  where
    measureText =
      case measureChecked t of
        Left err -> "    type error: " ++ err
        Right n  -> "    measure = " ++ show n

printTrace :: String -> (Term -> Maybe Term) -> Term -> IO ()
printTrace title step t = do
  putStrLn title
  mapM_ printStep (zip [0..] (steps step t))

base :: Ty
base = O

x0, x1, f1 :: Var
x0 = V "x0" base
x1 = V "x1" base
f1 = V "f" (base :-> base)

ex :: Term
ex = App (Lam f1 (Lam x0 (App (TVar f1) (TVar x0))))
         (Lam x1 (TVar x1))

main :: IO ()
main = do
  printTrace "Full leftmost-outermost beta-reduction:" oneBeta ex
  putStrLn ""
  printTrace "Weak call-by-name evaluation:" oneCBN ex
