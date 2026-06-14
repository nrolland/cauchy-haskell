-- | Oracle du volet 7 — le temps /rouge/ de « une loi, des réalisations » :
-- la même loi @star x = 1 + x · star x@ confrontée, dans chaque porteur, à un
-- référent /algorithmiquement indépendant/ de la réalisation testée.
--
-- Sur 'RegExp' — la seule classe neuve, dont c'est ici la micro-boucle :
--
--   1. la loi de l'étoile (identité de Conway) par /dénotation/ : les deux
--      membres reconnaissent les mêmes mots ;
--   2. le théorème de Kleene : la fermeture matricielle (élimination de
--      Lehmann), lue sur 'RegExp', /dénote le langage des chemins/ 0 → 2.
--
--   Trois moteurs jugent la même entrée : @regex-applicative@ (simulation de
--   type NFA), la sémantique des langages à la main (coupures du mot), et —
--   pour ②, indépendamment de toute expression — la simulation directe de
--   l'automate. Un désaccord entre les deux premiers lève une /panne/ du
--   harnais (pas un contre-exemple) ; le troisième tranche. Aucun
--   constructeur n'est exposé : les référents se branchent par le
--   catamorphisme 'foldRegExp', l'invariant des constructeurs intelligents
--   reste scellé.
--
-- Sur les /séries ℚ/ (corécursion gardée), la réalisation /compte/ : ses
-- coefficients sont l'inverse formel @1\/(1−p)@. Référent : la récurrence
-- indexée @cₙ = Σ p_k·c_{n-k}@ — le même point fixe résolu par indices, pas
-- par paresse — et l'ancre externe Fibonacci (OEIS A000045) pour @p = x+x²@.
--
-- Sur le /tropical/ (même @Data.Star@), la réalisation /minimise/ : @star (w·x
-- + w·x²)@ est le coût minimal des compositions par parts {1,2}. Référent :
-- la programmation dynamique de Bellman, et la forme close @⌈n\/2⌉@ au poids
-- unité. Shrinking activé (ombres locales).
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Control.Applicative (empty, many, (<|>))
import Data.List (nub)
import Data.Maybe (isJust)
import Data.Monoid (Sum (..))
import Numeric.Natural (Natural)
import System.Exit (exitFailure)

import qualified Text.Regex.Applicative as RE
import Test.QuickCheck

import Data.Semiring (Semiring (..))
import Data.Semiring.Tropical (Extrema (..), Tropical (..))
import Data.Star (Star (..))

import Data.Cauchy.Language.Weighted (Matrix, fromRows, toRows)
import Data.Cauchy.Parametricite.RegExp (RegExp, atom, foldRegExp)
import Data.Cauchy.Poly (fromCoeffs)
import Data.Cauchy.Series (Series, fromPoly, takeCoeffs)

-- L'alphabet du duel.
alphabet :: [Char]
alphabet = "ab"

-- ---------------------------------------------------------------------------
-- Les référents, branchés par le catamorphisme (constructeurs scellés)
-- ---------------------------------------------------------------------------

-- Référent 1 : regex-applicative — simulation de type NFA, indépendante de
-- la sémantique à la main.
toRE :: RegExp -> RE.RE Char ()
toRE = foldRegExp empty (pure ()) (\c -> () <$ RE.sym c) (<|>) (*>) (\x -> () <$ many x)

matchRE :: RegExp -> String -> Bool
matchRE r w = isJust (RE.match (toRE r) w)

-- Référent 2 : la sémantique des langages, par récurrence sur la syntaxe et
-- les coupures du mot — le second juge du même duel.
inLang :: RegExp -> String -> Bool
inLang = foldRegExp
  (const False)                                          -- ∅
  null                                                   -- ε
  (\c w -> w == [c])                                     -- une lettre
  (\f g w -> f w || g w)                                 -- +
  (\f g w -> any (\(u, v) -> f u && g v) (splits w))     -- ·
  star_                                                  -- *
  where
    star_ f w = null w
             || any (\(u, v) -> not (null u) && f u && star_ f v) (splits w)

-- Toutes les coupures @(préfixe, suffixe)@ du mot.
splits :: [a] -> [([a], [a])]
splits w = [ splitAt i w | i <- [0 .. length w] ]

-- La dénotation tranchée par les deux référents : leur désaccord est une
-- panne du harnais, pas un contre-exemple.
denote :: RegExp -> String -> Bool
denote r w =
  let a = matchRE r w
      b = inLang r w
  in if a /= b
       then error ("référents en désaccord sur le mot " ++ show w)
       else a

-- ---------------------------------------------------------------------------
-- ① la loi de l'étoile, par dénotation
-- ---------------------------------------------------------------------------

-- Une /ombre/ locale de la syntaxe, pour générer et /réduire/ (shrinking)
-- sans exposer les constructeurs de 'RegExp' ; reconstruite par l'API
-- publique. Ce que la propriété teste est donc exactement la surface
-- publique (constructeurs intelligents compris).
data Sh = SZero | SOne | SSym Char | SAlt Sh Sh | SSeq Sh Sh | SRep Sh
  deriving Show

build :: Sh -> RegExp
build SZero      = zero
build SOne       = one
build (SSym c)   = atom c
build (SAlt a b) = build a `plus`  build b
build (SSeq a b) = build a `times` build b
build (SRep a)   = star (build a)

instance Arbitrary Sh where
  arbitrary = sized go
    where
      leaf = oneof [pure SZero, pure SOne, SSym <$> elements alphabet]
      go n | n <= 0    = leaf
           | otherwise = oneof
               [ leaf
               , SAlt <$> half <*> half
               , SSeq <$> half <*> half
               , SRep <$> half ]
        where half = go (n `div` 2)
  shrink SZero      = []
  shrink SOne       = [SZero]
  shrink (SSym _)   = [SZero, SOne]
  shrink (SAlt a b) = [a, b] ++ [SAlt a' b | a' <- shrink a] ++ [SAlt a b' | b' <- shrink b]
  shrink (SSeq a b) = [a, b, SOne] ++ [SSeq a' b | a' <- shrink a] ++ [SSeq a b' | b' <- shrink b]
  shrink (SRep a)   = [SOne, a] ++ [SRep a' | a' <- shrink a]

genWord :: Gen String
genWord = do
  n <- choose (0, 6)
  vectorOf n (elements alphabet)

-- @L(star r) = L(1 + r · star r)@ : la loi tient mot à mot.
prop_loi :: Sh -> Property
prop_loi sh = forAllShrink genWord shrink $ \w ->
  let r = build sh
  in denote (star r) w === denote (one `plus` (r `times` star r)) w

-- ---------------------------------------------------------------------------
-- ② Kleene : la fermeture dénote le langage des chemins 0 → 2
-- ---------------------------------------------------------------------------

-- Un automate à trois états : @adj!!i!!j = Just c@ s'il y a une arête i → j
-- étiquetée @c@, @Nothing@ sinon.
genAdj :: Gen [[Maybe Char]]
genAdj = vectorOf 3 (vectorOf 3 edge)
  where edge = frequency [(2, pure Nothing), (1, Just <$> elements alphabet)]

shrinkAdj :: [[Maybe Char]] -> [[[Maybe Char]]]
shrinkAdj adj =
  [ [ [ if (i, j) == (p, q) then Nothing else adj !! i !! j | j <- [0 .. 2] ]
      | i <- [0 .. 2] ]
  | p <- [0 .. 2], q <- [0 .. 2], isJust (adj !! p !! q) ]

-- La matrice d'adjacence lue sur 'RegExp' (lettre ou @∅@), puis sa fermeture
-- (l'élimination de Lehmann de cauchy-language, générique sur le scalaire).
closureExpr :: [[Maybe Char]] -> RegExp
closureExpr adj = (toRows (star m) !! 0) !! 2
  where
    m :: Matrix 3 RegExp
    m = fromRows (map (map (maybe zero atom)) adj)

-- Référent 3, indépendant de toute expression : la simulation directe de
-- l'automate — l'ensemble des états atteints en consommant le mot.
nfaAccepts :: [[Maybe Char]] -> String -> Bool
nfaAccepts adj w = 2 `elem` foldl step [0] w
  where step states c = nub [ j | i <- states, j <- [0 .. 2], adj !! i !! j == Just c ]

prop_kleene :: Property
prop_kleene = forAllShrink genAdj shrinkAdj $ \adj ->
  forAllShrink genWord shrink $ \w ->
    let e = closureExpr adj
    in counterexample ("automate " ++ show adj ++ " / mot " ++ show w)
         (denote e w === nfaAccepts adj w)

-- ---------------------------------------------------------------------------
-- ③ séries ℚ : la réalisation compte — coefficients = inverse formel 1/(1−p)
-- ---------------------------------------------------------------------------

-- L'ancre externe : Fibonacci à la main (OEIS A000045, décalée), définie sans
-- la moindre série.
fibs :: [Integer]
fibs = 1 : 1 : zipWith (+) fibs (tail fibs)

-- @star (x+x²)@ sur ℚ /est/ la suite de Fibonacci : aucun paramètre, un
-- référent qui ignore tout des séries.
prop_fib :: Property
prop_fib = once $
  takeCoeffs 14 (star (fromPoly (fromCoeffs (map fromInteger [0, 1, 1]))) :: Series Rational)
    === map fromInteger (take 14 fibs)

-- Un polynôme à terme constant nul (l'étoile gardée le réclame) ; sa queue de
-- coefficients entiers, petite.
newtype Queue = Queue [Integer] deriving Show

instance Arbitrary Queue where
  arbitrary = Queue <$> (choose (0, 4) >>= \k -> vectorOf k (choose (-2, 3)))
  shrink (Queue cs) = Queue <$> shrink cs

-- Référent : @c₀ = 1@, @cₙ = Σ_{k≥1} p_k · c_{n-k}@ — l'inverse formel résolu
-- par indices, indépendant de la corécursion de la bibliothèque.
serieRef :: [Integer] -> Int -> [Integer]
serieRef queue n = cs
  where
    pk k = if k >= 1 && k <= length queue then queue !! (k - 1) else 0
    cs = [ c i | i <- [0 .. n - 1] ]
    c 0 = 1
    c i = sum [ pk k * (cs !! (i - k)) | k <- [1 .. i] ]

prop_serie :: Queue -> Property
prop_serie (Queue queue) =
  let n = 12
      s = star (fromPoly (fromCoeffs (map fromInteger (0 : queue)))) :: Series Rational
  in takeCoeffs n s === map fromInteger (serieRef queue n)

-- ---------------------------------------------------------------------------
-- ④ tropical : la réalisation minimise — coût des compositions par parts {1,2}
-- ---------------------------------------------------------------------------

type Trop = Tropical 'Minima (Sum Natural)

showTrop :: Trop -> String
showTrop Infinity           = "\8734"               -- ∞
showTrop (Tropical (Sum n)) = show (toInteger n)

-- Comparaison sans dépendre de @Show Trop@ (la bibliothèque rend le tropical à
-- la main) : on confronte les rendus.
sameTrops :: [Trop] -> [Trop] -> Property
sameTrops a b = counterexample (render a ++ " \8800 " ++ render b) (a == b)
  where render = show . map showTrop

-- Un poids : @∞@ (part absente) ou un coût 0..2.
genWeight :: Gen Trop
genWeight = frequency
  [ (1, pure Infinity)
  , (3, Tropical . Sum <$> elements [0, 1, 2]) ]

-- Référent : Bellman. @t₀ = 0@ (one), @tₙ = min(w₁ + t_{n-1}, w₂ + t_{n-2})@ —
-- le plus court chemin par parts, résolu par indices, indépendant de la
-- corécursion gardée.
tropRef :: Trop -> Trop -> Int -> [Trop]
tropRef w1 w2 n = ts
  where
    ts = [ t i | i <- [0 .. n - 1] ]
    t 0 = one
    t i = (w1 `times` (ts !! (i - 1)))
            `plus` (if i >= 2 then w2 `times` (ts !! (i - 2)) else zero)

prop_tropical :: Property
prop_tropical = forAllShow genWeight showTrop $ \w1 ->
  forAllShow genWeight showTrop $ \w2 ->
    let n = 10
        s = star (fromPoly (fromCoeffs [zero, w1, w2])) :: Series Trop
    in sameTrops (takeCoeffs n s) (tropRef w1 w2 n)

-- L'ancre tropicale : parts de poids unité → @⌈n\/2⌉@, le nombre minimal de
-- parts (la lecture pondérée de la page ③).
prop_tropical_close :: Property
prop_tropical_close = once $
  let w = Tropical (Sum 1) :: Trop
      s = star (fromPoly (fromCoeffs [zero, w, w])) :: Series Trop
  in sameTrops (takeCoeffs 8 s)
       [ Tropical (Sum (fromIntegral ((i + 1) `div` 2))) | i <- [0 .. 7 :: Int] ]

-- ---------------------------------------------------------------------------

qc :: Testable p => String -> p -> IO Bool
qc nom p = do
  putStrLn ("== " ++ nom)
  isSuccess <$> quickCheckResult p

main :: IO ()
main = do
  oks <- sequence
    [ qc "loi star r = 1 + r·star r (Conway, par dénotation)" prop_loi
    , qc "Kleene : closure dénote le langage des chemins 0→2" prop_kleene
    , qc "OEIS : star(x+x²) sur ℚ = Fibonacci (ancre externe)" prop_fib
    , qc "séries ℚ : star p = inverse formel 1/(1−p) (récurrence)" prop_serie
    , qc "tropical : star(w·x+w·x²) = coût minimal (Bellman)" prop_tropical
    , qc "tropical : poids unité → ⌈n/2⌉ (forme close, ancre ③)" prop_tropical_close
    ]
  if and oks then putStrLn "duels: tous verts" else exitFailure
