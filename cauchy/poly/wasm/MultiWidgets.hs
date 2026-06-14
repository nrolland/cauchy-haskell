{-# LANGUAGE DataKinds #-}
-- | Données des widgets de la vitrine des ordres (volet 3) : la sortie
-- de la bibliothèque — énumération du support le long d'un ordre,
-- curryfication, division — sérialisée pour les pages. Même partage
-- que SeriesWidgets : la logique ici (compilable en natif),
-- l'emballage JSFFI dans monoid-semiring/wasm/Exports.hs.
module MultiWidgets
  ( balayageJson
  , iterateJson
  , divisionJson
  ) where

import Data.List (intercalate)
import Data.Ratio (denominator, numerator)
import Numeric.Natural (Natural)

import Data.Semiring (Semiring (..))

import Data.Cauchy.Multi
import Data.Cauchy.Order
import qualified Data.Cauchy.Poly as P

-- Sérialisation : coefficients en chaînes (les rationnels n'existent
-- pas en JS), exposants en listes de nombres.
showRat :: Rational -> String
showRat r
  | denominator r == 1 = show (numerator r)
  | otherwise          = show (numerator r) ++ "/" ++ show (denominator r)

arr :: [String] -> String
arr xs = "[" ++ intercalate "," xs ++ "]"

expsJson :: [Natural] -> String
expsJson = arr . map show

termsJson :: MonomialOrder o => MPoly o Rational -> String
termsJson p =
  arr [ "[" ++ expsJson (components (toExp o)) ++ ","
            ++ show (showRat c) ++ "]"
      | (o, c) <- toTerms p ]

mkL :: [([Natural], Rational)] -> MPoly (Lex 2) Rational
mkL = fromTerms . map (\(es, c) -> (Lex (expo es), c))

-- | La nuée de la page ② : supp p = {x³, xy, y², x²y²}. Le rang de
-- chaque monôme est l'énumération de 'toTerms' le long du type
-- d'indice choisi — la tête est le dernier élément.
balayageJson :: Int -> String
balayageJson n = case n of
  0 -> go (Lex . expo     :: [Natural] -> Lex 2)
  1 -> go (GrLex . expo   :: [Natural] -> GrLex 2)
  _ -> go (GrevLex . expo :: [Natural] -> GrevLex 2)
  where
    nuee :: [[Natural]]
    nuee = [[3, 0], [1, 1], [0, 2], [2, 2]]
    go :: MonomialOrder o => ([Natural] -> o) -> String
    go wrap =
      let p = fromTerms [ (wrap e, 1 :: Rational) | e <- nuee ]
      in "{\"asc\":"
           ++ arr [ expsJson (components (toExp o)) | (o, _) <- toTerms p ]
           ++ "}"

-- | Le polynôme du pli de la page ① : 3 + 2xy + 7x²y + 5y².
-- Vue 0 : les termes à plat (ℕ² → S) ; vue 1 : 'iterate2' — les lignes
-- de S[ℕ][ℕ], une liste de coefficients de S[x] par puissance de y.
iterateJson :: Int -> String
iterateJson vue =
  let p = mkL [([0, 0], 3), ([1, 1], 2), ([2, 1], 7), ([0, 2], 5)]
  in case vue of
       0 -> "{\"plat\":" ++ termsJson p ++ "}"
       _ -> "{\"lignes\":"
              ++ arr [ arr (map (show . showRat) (P.toCoeffs ligne))
                     | ligne <- P.toCoeffs (iterate2 p) ]
              ++ "}"

-- | La division de la bibliothèque sur les deux exemples de ③ —
-- l'exemple déroulé (variantes 0, 1) et le témoin de non-canonicité
-- xy² (variantes 2, 3) — chaque paire dans les deux ordres de liste.
-- @ok@ est jugé par la bibliothèque : p = Σ qᵢ ∗ dᵢ + r et r réduit.
divisionJson :: Int -> String
divisionJson v =
  let d1 = [([1, 1], 1), ([0, 0], -1)]
      d2 = [([0, 2], 1), ([0, 0], -1)]
      clo = [([2, 1], 1), ([1, 2], 1), ([0, 2], 1)]
      temoin = [([1, 2], 1)]
      (pT, dTs) = case v of
        0 -> (clo,    [d1, d2])
        1 -> (clo,    [d2, d1])
        2 -> (temoin, [d1, d2])
        _ -> (temoin, [d2, d1])
      p  = mkL pT
      ds = map mkL dTs
      (qs, r) = division p ds
      recompose = foldr plus zero (zipWith times qs ds) `plus` r
      reduced = and
        [ not (toExp e `divides` toExp f)
        | d <- ds
        , Just (e, _) <- [leading d]
        , (f, _) <- toTerms r
        ]
      ok = p == recompose && reduced
  in "{\"qs\":" ++ arr (map termsJson qs)
       ++ ",\"r\":" ++ termsJson r
       ++ ",\"ok\":" ++ (if ok then "true" else "false")
       ++ "}"
