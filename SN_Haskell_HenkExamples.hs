{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

-- Checks the examples in Henk Barendregt's note using the simple
-- higher-order/final implementation.

data Base

data Ty a where
  TBase :: Ty Base
  TArr  :: Ty a -> Ty b -> Ty (a -> b)

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

type Term a = Meas a

app :: Term (a -> b) -> Term a -> Term b
app = dot

lam :: Ty a -> (Term a -> Term b) -> Term (a -> b)
lam ty body =
  F (\a -> add (star a + 1) (body a))
    (star (body (canon ty 0)))

measure :: Term a -> Integer
measure = star

base :: Ty Base
base = TBase

baseToBase :: Ty (Base -> Base)
baseToBase = TArr base base

xFree, yFree :: Term Base
xFree = canon base 0
yFree = canon base 0

i1 :: Term (Base -> Base)
i1 = lam base (\x -> x)

i1x :: Term Base
i1x = app i1 xFree

i2 :: Term ((Base -> Base) -> (Base -> Base))
i2 = lam baseToBase (\f -> f)

i2i1 :: Term (Base -> Base)
i2i1 = app i2 i1

i2i1x :: Term Base
i2i1x = app i2i1 xFree

lambdaFfx :: Term ((Base -> Base) -> Base)
lambdaFfx = lam baseToBase (\f -> app f (app f xFree))

lambdaFfxI1 :: Term Base
lambdaFfxI1 = app lambdaFfx i1

lambdaFx :: Term ((Base -> Base) -> (Base -> Base))
lambdaFx = lam baseToBase (\f -> lam base (\x -> app f x))

lambdaFxI1 :: Term (Base -> Base)
lambdaFxI1 = app lambdaFx i1

lambdaFxI1y :: Term Base
lambdaFxI1y = app lambdaFxI1 yFree

samples :: [Integer]
samples = [0, 1, 2, 3, 4]

baseSamples :: Meas (Base -> Base) -> [Integer]
baseSamples f = [star (dot f (N n)) | n <- samples]

sameBaseFunctionOnSamples :: Meas (Base -> Base) -> Meas (Base -> Base) -> Bool
sameBaseFunctionOnSamples f g =
  star f == star g && baseSamples f == baseSamples g

check :: String -> Bool -> IO Bool
check label ok = do
  putStrLn (label ++ if ok then "  OK" else "  FAIL")
  return ok

checkStar :: String -> Term a -> Integer -> IO Bool
checkStar label term expected =
  let actual = measure term
   in check (label ++ ": expected star " ++ show expected ++
             ", got " ++ show actual)
            (actual == expected)

checkBaseFunction :: String -> Term (Base -> Base) -> (Integer -> Integer) -> IO Bool
checkBaseFunction label term expected =
  let actual = baseSamples term
      wanted = [expected n | n <- samples]
   in check (label ++ ": expected samples " ++ show wanted ++
             ", got " ++ show actual)
            (actual == wanted)

checkI2Formula :: IO Bool
checkI2Formula =
  let functions = [i1, canon baseToBase 0, add 2 i1]
      holdsFor f = sameBaseFunctionOnSamples (dot i2 f) (add (star f + 1) f)
   in check "I_2 dot part agrees with f + f* + 1 on samples"
            (all holdsFor functions)

main :: IO ()
main = do
  results <- sequence
    [ checkStar "I_1" i1 0
    , checkBaseFunction "I_1 dot part: 2n+1" i1 (\n -> 2 * n + 1)
    , checkStar "I_1 x^o" i1x 1
    , checkStar "I_2" i2 0
    , checkI2Formula
    , checkStar "I_2 I_1" i2i1 1
    , checkBaseFunction "I_2 I_1 dot part: 2n+2" i2i1 (\n -> 2 * n + 2)
    , checkStar "I_2 I_1 x^o" i2i1x 2
    , checkStar "\\f. f (f x)" lambdaFfx 0
    , checkStar "(\\f. f (f x)) I_1" lambdaFfxI1 4
    , checkStar "\\f. \\x. f x" lambdaFx 0
    , checkStar "(\\f. \\x. f x) I_1" lambdaFxI1 2
    , checkBaseFunction "(\\f. \\x. f x) I_1 dot part: 3n+3"
                        lambdaFxI1 (\n -> 3 * n + 3)
    , checkStar "(\\f. \\x. f x) I_1 y^o" lambdaFxI1y 3
    ]
  if and results
    then putStrLn "All checked examples pass.  The corrected value for (\\f. \\x. f x) I_1 is star 2."
    else error "at least one Henk example failed"
