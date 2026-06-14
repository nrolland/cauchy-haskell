-- | Données des widgets du volet 7, sérialisées en JSON pour les pages. La
-- partie wasm (@wasm\/Exports.hs@) n'est qu'un emballage JSFFI autour de ce
-- module — qui ne dépend de rien de wasm et se compile en GHC natif. Tout
-- ce qui est /calculé/ ici l'est par la bibliothèque elle-même (l'étoile de
-- @Data.Star@ sur 'Series', sur 'Matrix', sur le tropical), jamais par une
-- réplique : le test 'Main' de @test\/Smoke.hs@ garde ces valeurs.
--
-- Partage du travail avec la page : Haskell calcule les /valeurs/ (la
-- bibliothèque), le script de la page dessine le SVG à partir d'elles. Le
-- JSON est donc la frontière exacte « ce que la lib produit ».
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Cauchy.Parametricite.Widgets
  ( -- * ① la loi, ses deux membres calculés par instance
    etoileJson
    -- * ② puissance contre fermeture (Matrix 3, 𝔹 réel / ℕ)
  , puissanceJson
    -- * ③ valeur (porteur) contre sens (coefficient), star (x+x²) réinterprété
  , valeurSensJson
    -- * ③ la liste géométrique : kⁿ = [xⁿ] star (k·x)
  , listeJson
    -- * ④ graphe-fermeture : (closure A)₁₂ = star(a)·b·star(c), trois lectures
  , grapheJson
  ) where

import Data.List (intercalate)
import Data.Monoid (Sum (..))
import Data.Ratio (denominator, numerator)
import Numeric.Natural (Natural)

import Data.Semiring (Semiring (..))
import Data.Semiring.Tropical (Extrema (..), Tropical (..))
import Data.Star (Star (..))

import Data.Cauchy.Language.Weighted (Matrix, fromRows, toRows)
import Data.Cauchy.Parametricite.RegExp (RegExp, atom, render)
import Data.Cauchy.Poly (Poly, fromCoeffs)
import Data.Cauchy.Series (Series, fromPoly, takeCoeffs)

-- | Le tropical de la collection : @(ℕ ∪ {∞}, min, +)@ — même type que le
-- coût minimal du volet 2.
type Trop = Tropical 'Minima (Sum Natural)

-- ---------------------------------------------------------------------------
-- Sérialisation JSON (minimale, sans dépendance)
-- ---------------------------------------------------------------------------

arr :: [String] -> String
arr xs = "[" ++ intercalate "," xs ++ "]"

obj :: [(String, String)] -> String
obj kvs = "{" ++ intercalate "," (map field kvs) ++ "}"
  where field (k, v) = show k ++ ":" ++ v

-- Un coefficient, rendu en chaîne JSON (les grands entiers débordent les
-- nombres JS ; les fractions et @∞@ n'y existent pas).
qInt :: Integer -> String
qInt = show . show

qRat :: Rational -> String
qRat r
  | denominator r == 1 = show (show (numerator r))
  | otherwise          = show (show (numerator r) ++ "/" ++ show (denominator r))

qTrop :: Trop -> String
qTrop Infinity            = show ("\8734" :: String)   -- ∞
qTrop (Tropical (Sum n))  = show (show (toInteger n))

qBool :: Bool -> String
qBool b = show (if b then "1" else "0" :: String)

-- ---------------------------------------------------------------------------
-- ① la loi star x = 1 + x·star x, ses deux membres calculés par instance
-- ---------------------------------------------------------------------------

-- | Pour le porteur choisi, les deux membres de la loi, /calculés par la
-- bibliothèque/ : le membre droit @star x@ et le membre gauche
-- @one + x · star x@. Ils coïncident — c'est la loi, vérifiée à l'exécution.
--
-- Modes adossés à une instance @Star@ : 0 = 𝔹 (court-circuit), 1 = séries ℚ
-- (corécursion gardée, lue sur les 6 premiers coefficients), 2 = tropical
-- (forme close @star _ = 0@). Les cas sans instance totale (ℚ scalaire, ℕ)
-- restent illustrés par la page : ils n'ont pas d'étoile de la classe à
-- exhiber, et c'est précisément le propos.
etoileJson :: Int -> String
etoileJson m = case m of
  0 -> let x   = True
           sx  = star x                       -- Star Bool : star _ = True
           lhs = one `plus` (x `times` sx)
       in obj [ ("porteur", show "𝔹"), ("droit", qBool sx), ("gauche", qBool lhs) ]
  1 -> let xS  = fromPoly (fromCoeffs [0, 1]) :: Series Rational   -- l'indéterminée
           sx  = star xS                       -- Star (Series ℚ) : gardée
           lhs = one `plus` (xS `times` sx)
       in obj [ ("porteur", show "Series\8201\8474")
              , ("droit",  arr (map qRat (takeCoeffs 6 sx)))
              , ("gauche", arr (map qRat (takeCoeffs 6 lhs))) ]
  _ -> let x   = Tropical (Sum 3) :: Trop      -- un poids quelconque ≥ 0
           sx  = star x                        -- forme close : star _ = one = 0
           lhs = one `plus` (x `times` sx)
       in obj [ ("porteur", show "tropical"), ("droit", qTrop sx), ("gauche", qTrop lhs) ]

-- ---------------------------------------------------------------------------
-- ② puissance contre fermeture : Matrix 3 sur 𝔹 (réel) et ℕ
-- ---------------------------------------------------------------------------

-- L'automate à trois sommets : 1→2, 2→3, et la boucle de retour 3→1 si
-- @cyc@. Sans elle la matrice est nilpotente (A³ = 0) ; avec elle le cycle
-- ouvre des marches arbitrairement longues.
adjBool :: Bool -> Matrix 3 Bool
adjBool cyc = fromRows
  [ [False, True,  False]
  , [False, False, True ]
  , [cyc,   False, False] ]

adjInt :: Bool -> Matrix 3 Integer
adjInt cyc = fromRows
  [ [0, 1, 0]
  , [0, 0, 1]
  , [if cyc then 1 else 0, 0, 0] ]

-- Masses des sommes partielles S_k = 1 + A + … + A^k (somme de toutes les
-- entrées), pour k = 0..6 — la même quantité que la page trace en barres.
massesOf :: Semiring s => (Matrix 3 s -> Integer) -> Matrix 3 s -> [Integer]
massesOf mass a = map mass (take 7 (scanl1 plus powers))
  where powers = iterate (`times` a) one   -- [I, A, A², …]

massBool :: Matrix 3 Bool -> Integer
massBool = toInteger . length . filter id . concat . toRows

massInt :: Matrix 3 Integer -> Integer
massInt = sum . concat . toRows

-- | La somme partielle des puissances, et — sur 𝔹 seulement — la fermeture
-- que la bibliothèque calcule réellement (@star@ de 'Matrix', l'élimination
-- de Lehmann). Sur ℕ il n'y a pas d'instance @Star@ : on ne peut pas même
-- l'appeler (garantie de typage), et c'est le contenu — @closure = null@,
-- la masse croît sans plateau dès qu'il y a un cycle.
--
-- Sélecteur : bit 0 = cycle, bit 1 = porteur (0 = 𝔹, 1 = ℕ).
puissanceJson :: Int -> String
puissanceJson v
  | v >= 2    = let a  = adjInt (odd v)
                    ms = massesOf massInt a
                in obj [ ("sr", "1"), ("cycle", flag (odd v))
                       , ("masses", arr (map show ms)), ("closure", "null") ]
  | otherwise = let a  = adjBool (odd v)
                    ms = massesOf massBool a
                    cl = massBool (star a)         -- la fermeture, calculée
                in obj [ ("sr", "0"), ("cycle", flag (odd v))
                       , ("masses", arr (map show ms)), ("closure", show cl) ]
  where flag b = if b then "1" else "0"

-- ---------------------------------------------------------------------------
-- ③ valeur (porteur) contre sens (coefficient) : star (x+x²), réinterprété
-- ---------------------------------------------------------------------------

-- La récurrence posée à la main, soudée à Integer : la /valeur/, ce que la
-- paresse calcule sans rien savoir d'une algèbre.
fibsBare :: [Integer]
fibsBare = take 6 fibs
  where fibs = 1 : 1 : zipWith (+) fibs (tail fibs)

-- | Deux colonnes : à gauche la valeur ('fibsBare', figée à Integer) ; à
-- droite le /sens/ — les coefficients de @star (x+x²)@ relus dans le
-- semi-anneau S, la même définition algébrique, calculée par la
-- bibliothèque. 0 = ℚ (compter : Fibonacci), 1 = tropical (minimiser), 2 =
-- 𝔹 (exister).
--
-- ⚠ Le tropical ne « minimise » que sur des générateurs /pondérés/. Le
-- littéral @star (x+x²)@ a ses générateurs de poids @one = 0@ ; son
-- coefficient n'est donc que l'/existence/ d'une composition (0 partout où
-- elle existe), pas le nombre de parts. Pour lire « le minimum de parts »
-- (⌈n\/2⌉) il faut peser chaque part de 1 — @star (w·x + w·x²)@ avec
-- @w = 1ₜ_{coût}@ — exactement l'idiome @peso@ du coût minimal du volet 2.
-- C'est cette lecture pondérée qu'on renvoie ; la page le dit.
valeurSensJson :: Int -> String
valeurSensJson sr = obj [ ("bare", arr (map show fibsBare)), ("sens", sens) ]
  where
    sens = case sr of
      0 -> let s = star (fromPoly (fromCoeffs [0, 1, 1])) :: Series Rational
           in arr (map qRat (takeCoeffs 6 s))
      1 -> let w = Tropical (Sum 1) :: Trop                       -- peser chaque part
               s = star (fromPoly (fromCoeffs [zero, w, w])) :: Series Trop
           in arr (map qTrop (takeCoeffs 6 s))
      _ -> let s = star (fromPoly (fromCoeffs [zero, one, one])) :: Series Bool
           in arr (map qBool (takeCoeffs 6 s))

-- | La liste géométrique : @kⁿ = |listes de longueur n sur k symboles| =
-- [xⁿ] star (k·x)@. Calculé comme la série @star (k·x)@ sur @Series
-- Integer@ — l'objet (la liste) et le nombre (kⁿ), une même étoile.
-- @k ∈ {1, 2, 3}@ ; cinq coefficients @[1, k, k², k³, k⁴]@.
listeJson :: Int -> String
listeJson k =
  let p = fromCoeffs [0, toInteger k] :: Poly Integer   -- k·x
      s = star (fromPoly p) :: Series Integer
  in arr (map qInt (takeCoeffs 5 s))

-- ---------------------------------------------------------------------------
-- ④ graphe-fermeture : (closure A)₁₂ = star(a) · b · star(c), trois lectures
-- ---------------------------------------------------------------------------

-- | L'entrée @(1,2)@ de la fermeture de l'automate à deux états — boucle
-- @a@ (présente si @loopA@), arête @b@, boucle @c@ — décomposée en ses trois
-- facteurs @star(a)@, @b@, @star(c)@ et leur produit, /calculés par la même
-- définition/ générique en S et lus sur trois semi-anneaux. La page dessine
-- l'automate et habille le résultat ; les valeurs viennent d'ici.
--
-- Sélecteur : bit 0 = boucle @a@ présente ; bits 1+ = porteur (0 =
-- expressions rationnelles, 1 = 𝔹, 2 = tropical). Les facteurs sont rendus
-- selon le porteur ; @res@ tropical vaut @null@ pour @∞@ (inatteignable),
-- @res@ booléen est un booléen JSON (l'atteignabilité).
grapheJson :: Int -> String
grapheJson v = case v `div` 2 of
  0 -> let a   = if loopA then atom 'a' else (zero :: RegExp)
           bb  = atom 'b'
           res = star a `times` bb `times` star (atom 'c')
       in obj [ ("sr", "0"), ("fa", show (render (star a)))
              , ("fb", show (render bb)), ("fc", show (render (star (atom 'c'))))
              , ("res", show (render res)) ]
  1 -> let a   = loopA                       -- présence de la boucle = booléen
           res = star a `times` (one :: Bool) `times` star (one :: Bool)
       in obj [ ("sr", "1"), ("fa", boolTok (star a)), ("fb", "1")
              , ("fc", "1"), ("res", if res then "true" else "false") ]
  _ -> let w   = Tropical (Sum 1) :: Trop
           a   = if loopA then w else zero
           res = star a `times` w `times` star w
       in obj [ ("sr", "2"), ("fa", tropTok (star a)), ("fb", "1")
              , ("fc", tropTok (star w)), ("res", tropTok res) ]
  where
    loopA = odd v
    boolTok b = if b then "1" else "0"
    tropTok Infinity           = "null"
    tropTok (Tropical (Sum n)) = show (toInteger n)
