-- | Exports JSFFI pour les widgets des explainers : les pages appellent
-- la bibliothèque elle-même, compilée en WebAssembly — jamais une
-- réplique JS. Construit par site/build/build-wasm.sh avec le backend
-- wasm de GHC (>= 9.10) ; toute la logique vit dans WidgetData, ce
-- module n'est que la frontière JS.
module Exports () where

import GHC.Wasm.Prim

import WidgetData
import qualified SeriesWidgets

foreign export javascript "fibPrefix"
  fibPrefix :: Int -> Int -> JSString

fibPrefix :: Int -> Int -> JSString
fibPrefix t nmax = toJSString (fibPrefixJson t nmax)

foreign export javascript "catalanPrefix"
  catalanPrefix :: Int -> Int -> JSString

catalanPrefix :: Int -> Int -> JSString
catalanPrefix t nmax = toJSString (catalanPrefixJson t nmax)

-- Vitrine des séries (cauchy-poly) : préfixes calculés par la
-- bibliothèque elle-même — l'étoile, le nœud gardé, Taylor.

foreign export javascript "seriesFib"
  seriesFib :: Int -> JSString

seriesFib :: Int -> JSString
seriesFib k = toJSString (SeriesWidgets.fibJson k)

foreign export javascript "seriesCatalan"
  seriesCatalan :: Int -> JSString

seriesCatalan :: Int -> JSString
seriesCatalan k = toJSString (SeriesWidgets.catalanJson k)

foreign export javascript "seriesExp"
  seriesExp :: Int -> JSString

seriesExp :: Int -> JSString
seriesExp k = toJSString (SeriesWidgets.expJson k)

foreign export javascript "seriesSin"
  seriesSin :: Int -> JSString

seriesSin :: Int -> JSString
seriesSin k = toJSString (SeriesWidgets.sinJson k)

foreign export javascript "seriesLog"
  seriesLog :: Int -> JSString

seriesLog :: Int -> JSString
seriesLog k = toJSString (SeriesWidgets.logJson k)
