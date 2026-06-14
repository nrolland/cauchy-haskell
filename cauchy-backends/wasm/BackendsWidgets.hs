{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Données des widgets de la vitrine des backends rapides (volet 5) : la
-- sortie de la bibliothèque — les deux chemins de la transformée, le gold
-- de convolveZ, la base réduite de F4 — sérialisée pour les pages. Même
-- partage que GroebnerWidgets : la logique ici (compilable en natif,
-- vérifiée par @cabal repl@), l'emballage JSFFI dans
-- monoid-semiring/wasm/Exports.hs.
module BackendsWidgets
  ( convolveJson
  , convolveZJson
  , f4Json
  ) where

import Data.List (intercalate, sortBy)
import Data.Maybe (fromMaybe)
import Numeric.Natural (Natural)

import Data.Mod (Mod, invertMod, unMod)

import Data.Cauchy.Backends (Root (..), convolve, convolveZ, f4)
import Data.Cauchy.Multi (MPoly, leading, fromTerms, toTerms)
import Data.Cauchy.Order (Lex (..), MonomialOrder (..), components, expo)

arr :: [String] -> String
arr xs = "[" ++ intercalate "," xs ++ "]"

-- | ① les deux chemins sur 𝔽₁₇ : (1 + x)(1 + 2x), n = 4, ω = 13. « top »
-- la convolution du noyau, « back » le chemin transformé (convolve) — les
-- deux rendent [1, 3, 2].
root4 :: Root (Mod 17)
root4 = Root w (inv w) (inv 4) 4
  where w     = 13
        inv x = fromMaybe (error "BackendsWidgets : 𝔽₁₇ — non inversible") (invertMod x)

convolveJson :: Int -> String
convolveJson _ =
  let back = map (toInteger . unMod) (take 3 (convolve root4 [1, 1, 0, 0] [1, 2, 0, 0]))
      top  = [1, 3, 2] :: [Integer]   -- la convolution du noyau, (1+x)(1+2x)
  in "{\"top\":" ++ arr (map show top) ++ ",\"back\":" ++ arr (map show back) ++ "}"

-- | ③ le gold de convolveZ : (10⁶ + 10⁶x + 10⁶x²)², coefficient central
-- 3·10¹² par restes chinois (au-delà d'un seul premier).
convolveZJson :: Int -> String
convolveZJson _ =
  case convolveZ gros gros of
    Right cs -> "{\"result\":" ++ arr (map show cs) ++ "}"
    Left e   -> "{\"error\":" ++ show (show e) ++ "}"
  where gros = replicate 3 (10 ^ (6 :: Int))

-- | ④ l'arc Gröbner par échelonnage : f4 ⟨xy − 1, y² − 1⟩, lex — la base
-- réduite {y² − 1, x − y} rendue tête d'abord.
f4Json :: Int -> String
f4Json _ =
  let d1   = mkL2 [([1, 1], 1), ([0, 0], -1)]   -- xy − 1
      d2   = mkL2 [([0, 2], 1), ([0, 0], -1)]   -- y² − 1
      base = parTete (f4 [d1, d2])
  in "{\"base\":" ++ show ("{" ++ intercalate ", " (map renderPoly base) ++ "}") ++ "}"

mkL2 :: [([Natural], Rational)] -> MPoly (Lex 2) Rational
mkL2 = fromTerms . map (\(es, c) -> (Lex (expo es), c))

-- Tri ascendant par tête (comme la normalisation ensemble-contre-ensemble
-- du harnais) : la base affichée a le même ordre que le log.
parTete :: MonomialOrder o => [MPoly o Rational] -> [MPoly o Rational]
parTete = sortBy (\a b -> compare (lmOf a) (lmOf b))
  where lmOf q = fmap fst (leading q)

vars :: [String]
vars = ["x", "y", "z", "u", "v", "w"]

sup :: Natural -> String
sup = concatMap chiffre . show
  where
    chiffre c = case c of
      '0' -> "⁰"; '1' -> "¹"; '2' -> "²"; '3' -> "³"; '4' -> "⁴"
      '5' -> "⁵"; '6' -> "⁶"; '7' -> "⁷"; '8' -> "⁸"; '9' -> "⁹"; _ -> [c]

monoStr :: [Natural] -> String
monoStr es =
  concat [ vars !! i ++ (if e == 1 then "" else sup e)
         | (i, e) <- zip [0 ..] es, e /= 0 ]

showRat :: Rational -> String
showRat r = show (truncate r :: Integer)
  -- les coefficients de la base réduite de l'arc sont entiers (±1) ; un
  -- dénominateur non trivial n'apparaît pas ici.

-- | Le polynôme rendu lisible, tête d'abord (≺ décroissant), comme les
-- pages l'affichent : « y² − 1 », « x − y ».
renderPoly :: MonomialOrder o => MPoly o Rational -> String
renderPoly p = case reverse (toTerms p) of
  []           -> "0"
  (t0 : reste) -> terme True t0 ++ concatMap (terme False) reste
  where
    terme premier (o, c) =
      let es   = components (toExp o)
          mono = monoStr es
          neg  = c < 0
          mag  = abs c
          coef = if mag == 1 && not (null mono) then "" else showRat mag
          piece = if null (coef ++ mono) then "1" else coef ++ mono
      in if premier
           then (if neg then "−" else "") ++ piece
           else (if neg then " − " else " + ") ++ piece
