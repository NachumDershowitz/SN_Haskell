{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

-- Object-language types, indexed by Haskell types.

data Base

data Ty a where
  TBase :: Ty Base
  TArr  :: Ty a -> Ty b -> Ty (a -> b)

-- Type-indexed de Vrijer measurements.

data Meas a where
  N :: Integer -> Meas Base
  F :: (Meas a -> Meas b) -> Integer -> Meas (a -> b)

star :: Meas a -> Integer
star (N n)   = n
star (F _ n) = n

dot :: Meas (a -> b) -> Meas a -> Meas b
dot (F f _) a = f a

add :: Integer -> Meas a -> Meas a
add k (N n)   = N (n + k)
add k (F f n) = F (\a -> add k (f a)) (n + k)

canon :: Ty a -> Integer -> Meas a
canon TBase n      = N n
canon (TArr _ b) n = F (\a -> canon b (n + star a)) n

-- Higher-order/final representation of terms.
-- Object binders are Haskell binders, so Haskell closures carry the
-- environment that the first-order version passes explicitly.

type Term a = Meas a

var :: Meas a -> Term a
var = id

app :: Term (a -> b) -> Term a -> Term b
app = dot

lam :: Ty a -> (Term a -> Term b) -> Term (a -> b)
lam ty body =
  F (\a -> add (star a + 1) (body a))
    (star (body (canon ty 0)))

measure :: Term a -> Integer
measure = star

-- Example: (\f^{o -> o}. \x^o. f x) (\x^o. x)

base :: Ty Base
base = TBase

baseToBase :: Ty (Base -> Base)
baseToBase = TArr base base

ex :: Term (Base -> Base)
ex = app (lam baseToBase (\f -> lam base (\x -> app f x)))
         (lam base (\x -> x))

main :: IO ()
main = print (measure ex)
