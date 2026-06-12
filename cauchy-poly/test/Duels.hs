-- | Le rouge de la phase 1 : les neuf lignes CONTRAT des pages ①②③,
-- réalisées en duels exécutables. Chaque duel doit échouer tant que le
-- squelette dit @error "à implémenter"@ — c'est le constat recherché.
--
-- ① (+), (∗) ≡ poly ; ev_a morphisme et ev ≡ eval ; substitution.
-- ② lois de semi-anneau sur préfixes (≥3 instances de S) ;
--   (x+x²)* = A000045 et C = 1+x∗C∗C = A000108 ; Taylor exp/sin/log.
-- ③ invariant de division ; divMod/gcd ≡ poly ; recip des séries.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Control.Monad (unless)
import Data.Ratio ((%))
import System.Exit (exitFailure)

import Test.QuickCheck
import Test.Cauchy.Oracle (Duel (..), Referee (..), Verdict, pureReferee,
                           runDuel, runSuite)

import qualified Data.Euclidean as E
import           Data.Mod (Mod)
import           Data.Semiring (Semiring (..))
import           Data.Star (star)

import qualified Data.Poly as P
import qualified Data.Vector as V

import qualified Data.Cauchy.Poly as CP
import qualified Data.Cauchy.Series as CS
import qualified Showcase

-- ---------------------------------------------------------------------
-- Générateurs : des descriptions finies, jamais des porteurs.

genQ :: Gen Rational
genQ = (%) <$> choose (-9, 9) <*> choose (1, 9)

genM7 :: Gen (Mod 7)
genM7 = fromInteger <$> choose (0, 6)

genCoeffs :: Gen s -> Gen [s]
genCoeffs g = do n <- choose (0, 6); vectorOf n g

-- Pas de 'shrink' générique sur s : on rétrécit la liste (longueur),
-- pas les scalaires — suffisant pour minimiser un contre-exemple.
shrinkCoeffs :: [s] -> [[s]]
shrinkCoeffs = shrinkList (const [])

shrinkPair :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair sa sb (a, b) = [(a', b) | a' <- sa a] ++ [(a, b') | b' <- sb b]

shrinkTriple :: (a -> [a]) -> (b -> [b]) -> (c -> [c]) -> (a, b, c) -> [(a, b, c)]
shrinkTriple sa sb sc (a, b, c) =
     [(a', b, c) | a' <- sa a]
  ++ [(a, b', c) | b' <- sb b]
  ++ [(a, b, c') | c' <- sc c]

-- Une loi est un duel contre le référent constant « vrai » : même
-- mécanique (génération, rétrécissement, rapport), référent trivial.
lawDuel :: String -> Gen i -> (i -> [i]) -> (i -> Bool) -> Duel i Bool
lawDuel nm g shr p = Duel nm g shr p (pureReferee "loi" (const True))

-- ---------------------------------------------------------------------
-- Le référent poly (Bodigrim), côté Num.

toP :: (Eq s, Num s) => [s] -> P.VPoly s
toP = P.toPoly . V.fromList

fromP :: P.VPoly s -> [s]
fromP = V.toList . P.unPoly

-- ---------------------------------------------------------------------
-- ① — (+), (∗) ≡ poly ; ev ; substitution.

genPair :: Gen ([Rational], [Rational])
genPair = (,) <$> genCoeffs genQ <*> genCoeffs genQ

duelPlus :: Duel ([Rational], [Rational]) [Rational]
duelPlus = Duel
  { duelName  = "(+) sur S[x], S = Q"
  , generator = genPair
  , shrinker  = shrinkPair shrinkCoeffs shrinkCoeffs
  , candidate = \(p, q) ->
      CP.toCoeffs (CP.fromCoeffs p `plus` CP.fromCoeffs q)
  , referee   = pureReferee "poly (Bodigrim)" (\(p, q) -> fromP (toP p + toP q))
  }

duelTimes :: Duel ([Rational], [Rational]) [Rational]
duelTimes = Duel
  { duelName  = "(*) sur S[x], S = Q"
  , generator = genPair
  , shrinker  = shrinkPair shrinkCoeffs shrinkCoeffs
  , candidate = \(p, q) ->
      CP.toCoeffs (CP.fromCoeffs p `times` CP.fromCoeffs q)
  , referee   = pureReferee "poly (Bodigrim)" (\(p, q) -> fromP (toP p * toP q))
  }

-- ev_a(p∗q) = ev_a p · ev_a q, et ev ≡ eval de poly : la paire couvre
-- les deux — si elle coïncide avec celle du référent (égale par
-- construction chez poly), le morphisme tient chez le candidat.
duelEval :: Duel ([Rational], [Rational], Rational) (Rational, Rational)
duelEval = Duel
  { duelName  = "ev_a(p*q) = ev_a p . ev_a q ; ev = eval"
  , generator = (,,) <$> genCoeffs genQ <*> genCoeffs genQ <*> genQ
  , shrinker  = shrinkTriple shrinkCoeffs shrinkCoeffs (const [])
  , candidate = \(p, q, a) ->
      let pc = CP.fromCoeffs p
          qc = CP.fromCoeffs q
      in (CP.eval (pc `times` qc) a, CP.eval pc a `times` CP.eval qc a)
  , referee   = pureReferee "poly (Bodigrim)" $ \(p, q, a) ->
      let pp = toP p
          qq = toP q
      in (P.eval (pp * qq) a, P.eval pp a * P.eval qq a)
  }

duelSubst :: Duel ([Rational], [Rational], [Rational]) Bool
duelSubst = lawDuel "subst : p[x] = p ; p[q[r]] = p[q][r]"
  ((,,) <$> genCoeffs genQ <*> genCoeffs genQ <*> genCoeffs genQ)
  (shrinkTriple shrinkCoeffs shrinkCoeffs shrinkCoeffs)
  (\(p, q, r) ->
     let pc = CP.fromCoeffs p
         qc = CP.fromCoeffs q
         rc = CP.fromCoeffs r
         eq u v = CP.toCoeffs u == CP.toCoeffs v
     in eq (CP.subst pc CP.x) pc
        && eq (CP.subst pc (CP.subst qc rc)) (CP.subst (CP.subst pc qc) rc))

-- ---------------------------------------------------------------------
-- ② — lois de semi-anneau de S[[x]] sur préfixes, ≥3 instances de S.
--
-- Les séries d'entrée sont tirées comme descriptions inductives finies
-- (route des présentations) puis dépliées ; l'égalité est celle des
-- préfixes tronqués — la seule observation du type.

-- SNIPPET:duels-desc
-- Une série d'entrée est tirée comme description finie — un terme
-- inductif — puis dépliée ; le shrinker agit sur la description.
data Desc s
  = DPoly [s]
  | DPlus (Desc s) (Desc s)
  | DTimes (Desc s) (Desc s)
  | DStarX (Desc s)            -- star (x * d) : la garde par construction
  deriving Show

interp :: (Eq s, Semiring s) => Desc s -> CS.Series s
interp (DPoly cs)   = CS.fromPoly (CP.fromCoeffs cs)
interp (DPlus a b)  = interp a `plus` interp b
interp (DTimes a b) = interp a `times` interp b
interp (DStarX d)   = star (CS.fromPoly CP.x `times` interp d)
-- END:duels-desc

genDesc :: Gen s -> Gen (Desc s)
genDesc gs = go (2 :: Int)
  where
    leaf = DPoly <$> genCoeffs gs
    go 0 = leaf
    go d = frequency
      [ (3, leaf)
      , (2, DPlus  <$> go (d - 1) <*> go (d - 1))
      , (2, DTimes <$> go (d - 1) <*> go (d - 1))
      , (1, DStarX <$> go (d - 1))
      ]

shrinkDesc :: Desc s -> [Desc s]
shrinkDesc (DPoly cs)   = map DPoly (shrinkCoeffs cs)
shrinkDesc (DPlus a b)  = [a, b] ++ [DPlus a' b | a' <- shrinkDesc a]
                                 ++ [DPlus a b' | b' <- shrinkDesc b]
shrinkDesc (DTimes a b) = [a, b] ++ [DTimes a' b | a' <- shrinkDesc a]
                                 ++ [DTimes a b' | b' <- shrinkDesc b]
shrinkDesc (DStarX d)   = [d] ++ map DStarX (shrinkDesc d)

-- | Préfixe d'observation des lois.
prefixK :: Int
prefixK = 12

-- | Les sept lois, sur préfixes, pour une instance S nommée.
seriesLaws :: (Show s, Eq s, Semiring s) => String -> Gen s -> [IO Verdict]
seriesLaws inst gs =
  [ run "plus-assoc"   (\a b c -> ((a .+. b) .+. c) =~= (a .+. (b .+. c)))
  , run "plus-comm"    (\a b _ -> (a .+. b) =~= (b .+. a))
  , run "plus-zero"    (\a _ _ -> (a .+. zero) =~= a)
  , run "times-assoc"  (\a b c -> ((a .*. b) .*. c) =~= (a .*. (b .*. c)))
  , run "times-one"    (\a _ _ -> ((a .*. one) =~= a) && ((one .*. a) =~= a))
  , run "distrib"      (\a b c -> (a .*. (b .+. c)) =~= ((a .*. b) .+. (a .*. c))
                              && ((b .+. c) .*. a) =~= ((b .*. a) .+. (c .*. a)))
  , run "annihilation" (\a _ _ -> ((zero .*. a) =~= zero) && ((a .*. zero) =~= zero))
  ]
  where
    (.+.) = plus
    (.*.) = times
    u =~= v = CS.takeCoeffs prefixK u == CS.takeCoeffs prefixK v
    gen3   = (,,) <$> genDesc gs <*> genDesc gs <*> genDesc gs
    shr3   = shrinkTriple shrinkDesc shrinkDesc shrinkDesc
    run nm law = runDuel 300 $
      lawDuel ("S[[x]] " ++ inst ++ " : " ++ nm) gen3 shr3
              (\(a, b, c) -> law (interp a) (interp b) (interp c))

-- ---------------------------------------------------------------------
-- ② — OEIS : (x+x²)* = A000045, C = 1 + x∗C∗C = A000108, ≥20 termes.
--
-- Les b-files sont la source unique, vendorisée en phase 0 ; la CWD
-- d'un test cabal est la racine du paquet, d'où le chemin relatif.
-- (Dette assumée : ce lecteur réplique celui de la suite phase 0 ;
-- remboursement le jour où le harnais possédera les référents OEIS.)

readBFile :: FilePath -> IO [(Int, Integer)]
readBFile fp = do
  s <- readFile fp
  return [ (read n, read a)
         | l <- lines s
         , not (null l), head l /= '#'
         , (n : a : _) <- [words l] ]

oeisReferee :: String -> FilePath -> Int -> Referee Int [Integer]
oeisReferee nm fp fromN = Referee nm $ \k ->
  take k . map snd . filter ((>= fromN) . fst) <$> readBFile fp

genLen :: Gen Int
genLen = choose (20, 28)

shrinkLen :: Int -> [Int]
shrinkLen k = [k' | k' <- shrink k, k' >= 1]

-- Coefficient k de (x+x²)* : F(k+1) — le b-file se lit depuis n = 1.
-- Les candidats sont les définitions d'exposition (Showcase) : le code
-- que la vitrine montre est exactement celui que ces duels jugent.
duelFib :: Duel Int [Integer]
duelFib = Duel
  { duelName  = "(x+x^2)* = A000045"
  , generator = genLen
  , shrinker  = shrinkLen
  , candidate = \k -> CS.takeCoeffs k Showcase.fibonacci
  , referee   = oeisReferee "OEIS" "../monoid-semiring/test/data/b000045.txt" 1
  }

duelCatalan :: Duel Int [Integer]
duelCatalan = Duel
  { duelName  = "C = 1 + x*C*C = A000108"
  , generator = choose (20, 21)   -- le b-file vendorisé porte 21 termes
  , shrinker  = shrinkLen
  , candidate = \k -> CS.takeCoeffs k Showcase.catalan
  , referee   = oeisReferee "OEIS" "../monoid-semiring/test/data/b000108.txt" 0
  }

-- ---------------------------------------------------------------------
-- ② — Taylor : exp, sin, log(1+x) ; coefficients publiés, formes closes
-- indépendantes de l'algorithme par équations gardées.

factorial :: Int -> Rational
factorial n = fromIntegral (product [1 .. toInteger n])

expCoeff, sinCoeff, logCoeff :: Int -> Rational
expCoeff n = 1 / factorial n
sinCoeff n
  | odd n     = (-1) ^ ((n - 1) `div` 2) / factorial n
  | otherwise = 0
logCoeff 0 = 0
logCoeff n = (-1) ^ (n + 1) / fromIntegral n

taylorDuel :: String -> CS.Series Rational -> (Int -> Rational) -> Duel Int [Rational]
taylorDuel nm s coeff = Duel
  { duelName  = nm ++ " (Taylor, Q dans S)"
  , generator = choose (8, 13)
  , shrinker  = shrinkLen
  , candidate = \k -> CS.takeCoeffs k s
  , referee   = pureReferee "coefficients publies" (\k -> map coeff [0 .. k - 1])
  }

-- ---------------------------------------------------------------------
-- ③ — division : invariant du Théorème 1, duel divMod/gcd contre poly,
-- recip des séries. S = F₇ : un corps exact, l'égalité est décidable.

genF7Pair :: Gen ([Mod 7], [Mod 7])
genF7Pair = (,) <$> genCoeffs genM7
                <*> (genCoeffs genM7 `suchThat` any (/= 0))

shrinkF7Pair :: ([Mod 7], [Mod 7]) -> [([Mod 7], [Mod 7])]
shrinkF7Pair (a, b) =
  [ (a', b') | (a', b') <- shrinkPair shrinkCoeffs shrinkCoeffs (a, b)
             , any (/= 0) b' ]

-- Degré lu sur les coefficients denses sans zéros de queue.
degOf :: [s] -> Int
degOf cs = length cs - 1

duelDivInvariant :: Duel ([Mod 7], [Mod 7]) Bool
duelDivInvariant = lawDuel "divMod : a = q*b + r, deg r < deg b (F7)"
  genF7Pair shrinkF7Pair $ \(a, b) ->
    let pa = CP.fromCoeffs a
        pb = CP.fromCoeffs b
        (q, r) = E.quotRem pa pb
        rc = CP.toCoeffs r
    in CP.toCoeffs ((q `times` pb) `plus` r) == CP.toCoeffs pa
       && (null rc || degOf rc < degOf (CP.toCoeffs pb))

-- gcd n'est défini qu'à une unité près : on compare les formes moniques.
monic :: [Mod 7] -> [Mod 7]
monic [] = []
monic cs = map (/ last cs) cs

-- SNIPPET:duels-divgcd
duelDivGcd :: Duel ([Mod 7], [Mod 7]) ([Mod 7], [Mod 7], [Mod 7])
duelDivGcd = Duel
  { duelName  = "divMod, gcd sur S[x], S = F7"
  , generator = genF7Pair
  , shrinker  = shrinkF7Pair
  , candidate = \(a, b) ->
      let pa = CP.fromCoeffs a
          pb = CP.fromCoeffs b
          (q, r) = E.quotRem pa pb
      in (CP.toCoeffs q, CP.toCoeffs r, monic (CP.toCoeffs (E.gcd pa pb)))
  , referee   = pureReferee "poly (Bodigrim)" $ \(a, b) ->
      let pa = toP a
          pb = toP b
          (q, r) = P.quotRemFractional pa pb
      in (fromP q, fromP r, monic (fromP (E.gcd pa pb)))
  }
-- END:duels-divgcd

duelRecip :: Duel [Mod 7] Bool
duelRecip = lawDuel "recip : p * recip p = 1 (p(0) inversible, F7)"
  (genCoeffs genM7 `suchThat` (\cs -> not (null cs) && head cs /= 0))
  (\cs -> [cs' | cs' <- shrinkCoeffs cs, not (null cs'), head cs' /= 0])
  (\cs ->
     let s = CS.fromPoly (CP.fromCoeffs cs) :: CS.Series (Mod 7)
     in CS.takeCoeffs prefixK (s `times` CS.recipSeries s)
        == (one : replicate (prefixK - 1) zero))

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  let bitABit = 10000   -- « différentiel bit-à-bit, 10⁴ cas » (①③)
  ok <- runSuite $
    -- ①
    [ runDuel bitABit duelPlus
    , runDuel bitABit duelTimes
    , runDuel 1000    duelEval
    , runDuel 1000    duelSubst
    ]
    -- ② lois sur préfixes, trois instances de S
    ++ seriesLaws "sur Q"  genQ
    ++ seriesLaws "sur F7" genM7
    ++ seriesLaws "sur Bool" (arbitrary :: Gen Bool)
    -- ② OEIS et Taylor
    ++ [ runDuel 30 duelFib
       , runDuel 30 duelCatalan
       , runDuel 30 (taylorDuel "exp"      CS.expS expCoeff)
       , runDuel 30 (taylorDuel "sin"      CS.sinS sinCoeff)
       , runDuel 30 (taylorDuel "log(1+x)" CS.logS logCoeff)
       ]
    -- ③
    ++ [ runDuel 1000    duelDivInvariant
       , runDuel bitABit duelDivGcd
       , runDuel 1000    duelRecip
       ]
  unless ok exitFailure
  putStrLn "PHASE 1 ORACLE: all green"
