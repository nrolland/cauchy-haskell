-- | Exposition snippets: every Haskell fragment shown in the explainer
-- series is extracted from this file or from @src/@ by
-- @explainers/extract.mjs@ — GHC compiles and the oracle runs everything
-- the reader sees.
module Snippets
  ( Poly
  , fibCoefficient
  , fibStep
  , catalanCoefficient
  , catalanStep
  , truncateDeg
  , x
  , monomial
  , degrees
  , word
  , exponents
  , pSquared
  , abab
  , assocL
  , assocR
  ) where

import Data.Monoid     (Sum (..))
import Numeric.Natural (Natural)

import Data.Semiring (Semiring (..))
import Data.MonoidSemiring

-- SNIPPET:monoides
-- Trois monoïdes, un seul geste : (<>) associatif avec neutre mempty.
degrees :: Sum Natural                  -- (N, +)
degrees = Sum 2 <> Sum 3                -- Sum 5

word :: String                          -- (Sigma*, ++)
word = "ab" <> "ba"                     -- "abba"

exponents :: (Sum Natural, Sum Natural) -- (N^2, +) composante par composante
exponents = (Sum 1, Sum 4) <> (Sum 2, Sum 0)  -- (Sum 3, Sum 4)
-- END:monoides

-- SNIPPET:poly-basics
-- A polynomial is a finitely supported function (N, +) -> Integer.
type Poly = MonoidSemiring (Sum Natural) Integer

-- The indeterminate: coefficient 1 at index 1.
x :: Poly
x = dirac (Sum 1) 1

monomial :: Natural -> Integer -> Poly
monomial k c = dirac (Sum k) c
-- END:poly-basics

-- SNIPPET:duel
-- Le même `times` : produit de polynômes, concaténation de langages.
pSquared :: Poly
pSquared = p `times` p          -- 1 + 2x + x^2
  where p = one `plus` x        -- 1 + x

type Lang = MonoidSemiring String Bool

abab :: Lang
abab = ab `times` ab            -- {"aa","ab","ba","bb"}
  where ab = fromList [("a", True), ("b", True)]
-- END:duel

-- SNIPPET:assoc-micro
-- Deux parenthésages du même produit : x + 2x^2 + x^3 des deux côtés.
assocL, assocR :: Poly
assocL = (p `times` q) `times` p  where p = one `plus` x; q = x
assocR = p `times` (q `times` p)  where p = one `plus` x; q = x
-- END:assoc-micro

-- SNIPPET:truncate
-- Keep degrees <= n: the working window for series fixpoints.
truncateDeg :: Natural -> Poly -> Poly
truncateDeg n = filterIndex (\(Sum k) -> k <= n)
-- END:truncate

-- SNIPPET:fibonacci
-- 1/(1-x-x^2) as the fixpoint  F = 1 + (x + x^2) * F:
-- one step of the iteration, then the fixpoint to degree n.
-- Coefficient k is Fibonacci(k+1).
fibStep :: Natural -> Poly -> Poly
fibStep n f = truncateDeg n
                (one `plus` ((x `plus` (x `times` x)) `times` f))

fibSeries :: Natural -> Poly
fibSeries n = iterate (fibStep n) one !! (fromIntegral n + 1)

fibCoefficient :: Natural -> Integer
fibCoefficient k = coefficient (Sum k) (fibSeries k)
-- END:fibonacci

-- SNIPPET:catalan
-- Catalan: the fixpoint  C = 1 + x * C^2,  truncated to degree n.
catalanStep :: Natural -> Poly -> Poly
catalanStep n c = truncateDeg n
                    (one `plus` (x `times` (c `times` c)))

catalanSeries :: Natural -> Poly
catalanSeries n = iterate (catalanStep n) one !! (fromIntegral n + 1)

catalanCoefficient :: Natural -> Integer
catalanCoefficient k = coefficient (Sum k) (catalanSeries k)
-- END:catalan
