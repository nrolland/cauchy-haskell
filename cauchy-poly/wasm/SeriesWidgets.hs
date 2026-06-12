-- | Données des widgets de la vitrine des séries : la sortie de la
-- bibliothèque, sérialisée pour les pages. La partie wasm
-- (monoid-semiring/wasm/Exports.hs, module unique de la collection)
-- n'est qu'un emballage JSFFI autour de ce module — qui ne dépend de
-- rien de wasm et se compile avec un GHC natif. Les définitions
-- exposées ('Showcase') sont celles que les duels jugent.
module SeriesWidgets
  ( fibJson
  , catalanJson
  , expJson
  , sinJson
  , logJson
  ) where

import Data.List (intercalate)
import Data.Ratio (denominator, numerator)

import Data.Cauchy.Series (Series, expS, logS, sinS, takeCoeffs)
import Showcase (catalan, fibonacci)

-- Coefficients [x^0 .. x^(k-1)] en JSON, chaque coefficient en chaîne
-- (les grands entiers débordent les nombres JS ; les rationnels n'y
-- existent pas).
jsonOf :: [String] -> String
jsonOf xs = "[" ++ intercalate "," (map show xs) ++ "]"

fibJson :: Int -> String
fibJson k = jsonOf (map show (takeCoeffs k fibonacci))

catalanJson :: Int -> String
catalanJson k = jsonOf (map show (takeCoeffs k catalan))

ratJson :: Series Rational -> Int -> String
ratJson s k = jsonOf (map showRat (takeCoeffs k s))
  where
    showRat r
      | denominator r == 1 = show (numerator r)
      | otherwise          = show (numerator r) ++ "/" ++ show (denominator r)

expJson, sinJson, logJson :: Int -> String
expJson = ratJson expS
sinJson = ratJson sinS
logJson = ratJson logS
