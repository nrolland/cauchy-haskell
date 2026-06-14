-- | Exports JSFFI pour les widgets des explainers : les pages appellent
-- la bibliothèque elle-même, compilée en WebAssembly — jamais une
-- réplique JS. Construit par site/build/build-wasm.sh avec le backend
-- wasm de GHC (>= 9.10) ; toute la logique vit dans WidgetData, ce
-- module n'est que la frontière JS.
module Exports () where

import GHC.Wasm.Prim

import WidgetData
import qualified BackendsWidgets
import qualified GroebnerWidgets
import qualified MultiWidgets
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

-- Vitrine des ordres (cauchy-order + multivarié de cauchy-poly) :
-- énumération du support le long d'un type d'indice, curryfication,
-- division — calculées par la bibliothèque elle-même.

foreign export javascript "multiBalayage"
  multiBalayage :: Int -> JSString

multiBalayage :: Int -> JSString
multiBalayage n = toJSString (MultiWidgets.balayageJson n)

foreign export javascript "multiIterate"
  multiIterate :: Int -> JSString

multiIterate :: Int -> JSString
multiIterate vue = toJSString (MultiWidgets.iterateJson vue)

foreign export javascript "multiDivision"
  multiDivision :: Int -> JSString

multiDivision :: Int -> JSString
multiDivision v = toJSString (MultiWidgets.divisionJson v)

-- Vitrine des bases de Gröbner (cauchy-groebner) : la complétion de l'arc
-- et les bases réduites avec leurs coupes, calculées par la bibliothèque.

foreign export javascript "groebnerBuchberger"
  groebnerBuchberger :: Int -> JSString

groebnerBuchberger :: Int -> JSString
groebnerBuchberger n = toJSString (GroebnerWidgets.buchbergerJson n)

foreign export javascript "groebnerCut"
  groebnerCut :: Int -> JSString

groebnerCut :: Int -> JSString
groebnerCut n = toJSString (GroebnerWidgets.cutJson n)

-- Vitrine des backends rapides (cauchy-backends) : les deux chemins de la
-- transformée sur 𝔽₁₇, le gold de convolveZ par restes chinois, et la base
-- réduite de F4 — calculés par la bibliothèque.

foreign export javascript "backendsConvolve"
  backendsConvolve :: Int -> JSString

backendsConvolve :: Int -> JSString
backendsConvolve n = toJSString (BackendsWidgets.convolveJson n)

foreign export javascript "backendsConvolveZ"
  backendsConvolveZ :: Int -> JSString

backendsConvolveZ :: Int -> JSString
backendsConvolveZ n = toJSString (BackendsWidgets.convolveZJson n)

foreign export javascript "backendsF4"
  backendsF4 :: Int -> JSString

backendsF4 :: Int -> JSString
backendsF4 n = toJSString (BackendsWidgets.f4Json n)
