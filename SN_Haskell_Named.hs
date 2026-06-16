{-# OPTIONS_GHC -Wall #-}

module Main where

import Data.Maybe (fromMaybe)

infixr 5 :->

-- First-order syntax: names, applications, and lambda binders.

data Ty = O | Ty :-> Ty
  deriving (Eq, Show)

data Var = V String Ty
  deriving (Eq, Show)

data Term
  = TVar Var
  | App Term Term
  | Lam Var Term
  deriving (Eq, Show)

vty :: Var -> Ty
vty (V _ a) = a

-- A small type checker keeps dot total on checked inputs.

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

-- De Vrijer measurements.

data Meas
  = N Integer
  | F (Meas -> Meas) Integer

star :: Meas -> Integer
star (N n)   = n
star (F _ n) = n

dot :: Meas -> Meas -> Meas
dot (F f _) a = f a
dot (N _)   _ = error "dot of a base-type measure"

add :: Integer -> Meas -> Meas
add k (N n)   = N (n + k)
add k (F f n) = F (\a -> add k (f a)) (n + k)

canon :: Ty -> Integer -> Meas
canon O n = N n
canon (_ :-> b) n = F (\a -> canon b (n + star a)) n

-- Explicit environments and the denotation clauses.

type Env = [(Var, Meas)]

value :: Env -> Var -> Meas
value env x = fromMaybe (canon (vty x) 0) (lookup x env)

bra :: Env -> Term -> Meas
bra env (TVar x)  = value env x
bra env (App m n) = dot (bra env m) (bra env n)
bra env (Lam x m) =
  F (\a -> add (star a + 1) (bra ((x, a) : env) m))
    (star (bra ((x, canon (vty x) 0) : env) m))

measure :: Term -> Integer
measure = star . bra []

measureChecked :: Term -> Either String Integer
measureChecked m = do
  _ <- typeOf m
  Right (measure m)

-- Same example as in the simple version.

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
main =
  case measureChecked ex of
    Left err -> putStrLn ("type error: " ++ err)
    Right n  -> print n
