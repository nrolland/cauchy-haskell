{-# LANGUAGE DataKinds #-}
-- | Données des widgets de la vitrine des bases de Gröbner (volet 4) : la
-- sortie de la bibliothèque — la complétion de l'arc, le S-polynôme, les
-- bases réduites et leurs coupes — sérialisée pour les pages. Même partage
-- que MultiWidgets : la logique ici (compilable en natif, vérifiée par
-- @cabal repl@ avec @-iwasm@), l'emballage JSFFI dans
-- monoid-semiring/wasm/Exports.hs.
module GroebnerWidgets
  ( buchbergerJson
  , cutJson
  ) where

import Data.List (intercalate, sortBy)
import Numeric.Natural (Natural)

import Data.Cauchy.Groebner (buchberger, reduce, spol)
import Data.Cauchy.Multi (MPoly, fromTerms, leading, toTerms)
import Data.Cauchy.Order (Lex (..), MonomialOrder (..), components, expo)

-- Variables nommées, exposants en exposant unicode.
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
showRat r = show (numer r)
  where numer = truncate :: Rational -> Integer
  -- les coefficients des bases réduites de l'arc et de la cubique sont
  -- entiers (±1, ±2…) ; un dénominateur non trivial n'apparaît pas ici.

-- | Le polynôme rendu lisible, tête d'abord (≺ décroissant), comme les
-- pages l'affichent : « y² − 1 », « x − y », « y³ − z² ».
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

-- Tri ascendant par tête (comme la normalisation ensemble-contre-ensemble
-- du harnais) : la base affichée a le même ordre que le log.
parTete :: MonomialOrder o => [MPoly o Rational] -> [MPoly o Rational]
parTete = sortBy (\a b -> compare (lmOf a) (lmOf b))
  where lmOf q = fmap fst (leading q)

arr :: [String] -> String
arr xs = "[" ++ intercalate "," xs ++ "]"

headExp :: MonomialOrder o => MPoly o Rational -> [Natural]
headExp p = maybe [] (components . toExp . fst) (leading p)

mkL2 :: [([Natural], Rational)] -> MPoly (Lex 2) Rational
mkL2 = fromTerms . map (\(es, c) -> (Lex (expo es), c))

mkL3 :: [([Natural], Rational)] -> MPoly (Lex 3) Rational
mkL3 = fromTerms . map (\(es, c) -> (Lex (expo es), c))

-- | La complétion de l'arc ⟨xy − 1, y² − 1⟩, lex : têtes de départ, tête du
-- S-polynôme adjoint (x − y), têtes de la base réduite, et le S-polynôme en
-- toutes lettres — l'escalier des têtes de la page ⑤.
buchbergerJson :: Int -> String
buchbergerJson _ =
  let d1   = mkL2 [([1, 1], 1), ([0, 0], -1)]   -- xy − 1
      d2   = mkL2 [([0, 2], 1), ([0, 0], -1)]   -- y² − 1
      base = parTete (reduce (buchberger [d1, d2]))
      sp   = spol d1 d2
  in "{\"depart\":" ++ arr [expsJson (headExp d1), expsJson (headExp d2)]
       ++ ",\"spol\":" ++ expsJson (headExp sp)
       ++ ",\"reduite\":" ++ arr (map (expsJson . headExp) base)
       ++ ",\"spolTxt\":" ++ show (renderPoly sp)
       ++ "}"
  where expsJson = arr . map show

-- | Les bases réduites lex de l'arc et de la cubique ⟨x² − y, x³ − z⟩, en
-- toutes lettres et tête d'abord — la confrontation ensemble-contre-ensemble
-- de la page ⑥.
cutJson :: Int -> String
cutJson _ =
  let arcB = parTete (reduce (buchberger
               [mkL2 [([1, 1], 1), ([0, 0], -1)], mkL2 [([0, 2], 1), ([0, 0], -1)]]))
      cubB = parTete (reduce (buchberger
               [mkL3 [([2, 0, 0], 1), ([0, 1, 0], -1)], mkL3 [([3, 0, 0], 1), ([0, 0, 1], -1)]]))
  in "{\"arc\":" ++ arr (map (show . renderPoly) arcB)
       ++ ",\"cubiqueLex\":" ++ arr (map (show . renderPoly) cubB)
       ++ "}"
