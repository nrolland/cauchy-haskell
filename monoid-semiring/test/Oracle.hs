-- | Phase 0 oracle.
--
-- 1. Semiring laws (QuickCheck) for @MonoidSemiring m s@ at three
--    @(M, S)@ pairs: polynomials, languages, tropical multivariate.
-- 2. Differential test: Map-based convolution vs the naive O(n^2)
--    definition on raw association lists.
-- 3. Canonical results: Fibonacci (A000045) and Catalan (A000108)
--    coefficients of generating-function fixpoints vs vendored OEIS
--    b-files.
-- 4. The Ord contract: the algebra is invariant under change of order,
--    the observations are not ("OrdContract").
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import           Control.Monad      (forM, unless)
import           Data.List          (sort)
import           Data.Monoid        (Sum (..))
import           Numeric.Natural    (Natural)
import           System.Exit        (exitFailure)
import           Test.QuickCheck

import           Data.Semiring (Semiring (..))
import           Data.MonoidSemiring
import           Tropical (Tropical (..))
import qualified OrdContract
import qualified Snippets

-- Small supports: convolution is quadratic in support size.
genMS :: (Ord m, Semiring s, Eq s)
      => Gen m -> Gen s -> Gen (MonoidSemiring m s)
genMS gm gs = do
  n  <- choose (0, 6 :: Int)
  ps <- vectorOf n ((,) <$> gm <*> gs)
  return (fromList ps)

genNat :: Gen (Sum Natural)
genNat = Sum . fromIntegral <$> choose (0, 8 :: Int)

genWord :: Gen String
genWord = do n <- choose (0, 3 :: Int)
             vectorOf n (elements "ab")

genTrop :: Gen Tropical
genTrop = Tropical <$> frequency
  [ (1, return Nothing)
  , (5, Just <$> choose (-10, 10)) ]

-- SNIPPET:laws
-- The seven semiring laws, stated once, checked at every instance.
semiringLaws :: (Semiring r, Eq r, Show r) => Gen r -> [(String, Property)]
semiringLaws g =
  [ ("plus-assoc",    p3 (\a b c -> (a `plus` b) `plus` c == a `plus` (b `plus` c)))
  , ("plus-comm",     p2 (\a b   -> a `plus` b == b `plus` a))
  , ("plus-zero",     p1 (\a     -> a `plus` zero == a))
  , ("times-assoc",   p3 (\a b c -> (a `times` b) `times` c == a `times` (b `times` c)))
  , ("times-one",     p1 (\a     -> a `times` one == a && one `times` a == a))
  , ("distrib",       p3 (\a b c -> a `times` (b `plus` c) == (a `times` b) `plus` (a `times` c)
                                 && (b `plus` c) `times` a == (b `times` a) `plus` (c `times` a)))
  , ("annihilation",  p1 (\a     -> zero `times` a == zero && a `times` zero == zero))
  ]
  where p1 f = forAll g f
        p2 f = forAll g (\a -> forAll g (f a))
        p3 f = forAll g (\a -> forAll g (\b -> forAll g (f a b)))
-- END:laws

-- SNIPPET:naive
-- Reference implementation: the definition, term by term, on raw
-- association lists, no normalization, no Map.
naiveTimes :: (Monoid m, Semiring s) => [(m, s)] -> [(m, s)] -> [(m, s)]
naiveTimes f g = [ (u <> v, a `times` b) | (u, a) <- f, (v, b) <- g ]

-- A raw list and a MonoidSemiring agree iff fromList equalizes them.
agreesWithNaive :: (Ord m, Monoid m, Semiring s, Eq s)
                => [(m, s)] -> [(m, s)] -> Bool
agreesWithNaive f g =
  fromList f `times` fromList g == fromList (naiveTimes f g)
-- END:naive

readBFile :: FilePath -> IO [(Int, Integer)]
readBFile fp = do
  s <- readFile fp
  return [ (read n, read a)
         | l <- lines s
         , not (null l), head l /= '#'
         , (n : a : _) <- [words l] ]

checkSeq :: String -> [Integer] -> [Integer] -> IO Bool
checkSeq name got want
  | got == want = putStrLn ("OK   " ++ name) >> return True
  | otherwise   = do
      putStrLn ("FAIL " ++ name)
      putStrLn ("  got:  " ++ show got)
      putStrLn ("  want: " ++ show want)
      return False

runLaws :: String -> [(String, Property)] -> IO Bool
runLaws inst lws = fmap and . forM lws $ \(name, prop) -> do
  r <- quickCheckWithResult stdArgs{chatty = False, maxSuccess = 300} prop
  let ok = isSuccess r
  putStrLn ((if ok then "OK   " else "FAIL ") ++ inst ++ " / " ++ name)
  unless ok (print r)
  return ok

main :: IO ()
main = do
  -- 1. Laws at three (M, S) pairs
  ok1 <- runLaws "poly (Sum Nat, Integer)"
           (semiringLaws (genMS genNat (arbitrary :: Gen Integer)))
  ok2 <- runLaws "lang (Sigma*, Bool)"
           (semiringLaws (genMS genWord (arbitrary :: Gen Bool)))
  ok3 <- runLaws "trop (Nat^2, Tropical)"
           (semiringLaws (genMS ((,) <$> genNat <*> genNat) genTrop))

  -- 2. Differential: optimized vs naive definition
  let diffProp :: Property
      diffProp = forAll (listOf ((,) <$> genNat <*> (arbitrary :: Gen Integer)))
        (\f -> forAll (listOf ((,) <$> genNat <*> arbitrary))
        (\g -> agreesWithNaive f g))
      diffLang :: Property
      diffLang = forAll (listOf ((,) <$> genWord <*> (arbitrary :: Gen Bool)))
        (\f -> forAll (listOf ((,) <$> genWord <*> arbitrary))
        (\g -> agreesWithNaive f g))
  ok4 <- runLaws "differential" [("naive-poly", diffProp), ("naive-lang", diffLang)]

  -- 3. Canonical sequences vs vendored OEIS b-files
  fib <- readBFile "test/data/b000045.txt"
  cat <- readBFile "test/data/b000108.txt"
  -- coefficient k of 1/(1-x-x^2) is F(k+1)
  let nFib  = 29 :: Int
      gotF  = [ Snippets.fibCoefficient (fromIntegral k) | k <- [0 .. nFib] ]
      wantF = [ a | (n, a) <- fib, n >= 1, n <= nFib + 1 ]
  ok5 <- checkSeq ("Fibonacci 1/(1-x-x^2) vs A000045, " ++ show (nFib + 1) ++ " terms")
                  gotF wantF
  let nCat  = 20 :: Int
      gotC  = [ Snippets.catalanCoefficient (fromIntegral k) | k <- [0 .. nCat] ]
      wantC = [ a | (n, a) <- cat, n <= nCat ]
  ok6 <- checkSeq ("Catalan C = 1 + x*C^2 vs A000108, " ++ show (nCat + 1) ++ " terms")
                  gotC wantC

  -- sanity: sorted support after arithmetic stays canonical
  let f = fromList [(Sum (3 :: Natural), 2 :: Integer), (Sum 0, 1), (Sum 3, -2)]
  ok7 <- checkSeq "normalization drops zeros"
                  (map (fromIntegral . getSum) (sort (support f))) [0]

  -- 4. The Ord contract, both halves
  ok8 <- runLaws "Ord contract (invariance)"
           (OrdContract.invarianceLaws (genMS genNat arbitrary) genNat)
  ok9 <- checkSeq "Ord contract (observability): support of x + x^2, both orders"
                  (map fromIntegral (OrdContract.observedSupport
                                     ++ OrdContract.observedSupportRev))
                  [1, 2, 2, 1]

  unless (and [ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9]) exitFailure
  putStrLn "PHASE 0 ORACLE: all green"
