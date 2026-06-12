-- | Données des widgets : la sortie de la bibliothèque, sérialisée pour
-- les pages. La partie wasm (wasm/Exports.hs) n'est qu'un emballage JSFFI
-- autour de ce module — qui, lui, ne dépend de rien de wasm et se compile
-- avec un GHC natif, donc se vérifie localement contre les b-files OEIS.
module WidgetData
  ( fibPrefixJson
  , catalanPrefixJson
  ) where

import Data.List       (intercalate)
import Data.Monoid     (Sum (..))
import Numeric.Natural (Natural)

import Data.MonoidSemiring (coefficient)
import Data.Semiring (one)
import Snippets (Poly, catalanStep, fibStep)

-- Coefficients [x^0 .. x^(nmax-1)] après t itérations d'un pas de point
-- fixe, en JSON ; chaque coefficient en chaîne décimale (les grands
-- entiers débordent les nombres JS).
prefixJson :: (Poly -> Poly) -> Int -> Int -> String
prefixJson step t nmax = "[" ++ intercalate "," coeffs ++ "]"
  where
    f = iterate step one !! max 0 t
    coeffs = [ show (show (coefficient (Sum (fromIntegral k)) f))
             | k <- [0 .. nmax - 1] ]

fibPrefixJson :: Int -> Int -> String
fibPrefixJson t nmax = prefixJson (fibStep (degMax nmax)) t nmax

catalanPrefixJson :: Int -> Int -> String
catalanPrefixJson t nmax = prefixJson (catalanStep (degMax nmax)) t nmax

degMax :: Int -> Natural
degMax nmax = fromIntegral (max 1 nmax - 1)
