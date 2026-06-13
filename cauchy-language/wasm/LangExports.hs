-- | Exports JSFFI de la vitrine des langages : les pages appellent la
-- bibliothèque elle-même, compilée en WebAssembly — jamais une
-- réplique JS. Module séparé du module de la collection
-- (@monoid-semiring/wasm/Exports.hs@) : son échec de compilation ne
-- dégrade pas les widgets des volets 0–1. Toute la logique vit dans
-- 'LanguageWidgets', ce module n'est que la frontière JS.
module LangExports () where

import GHC.Wasm.Prim

import qualified LanguageWidgets as W

foreign export javascript "langDecoupages"
  langDecoupages :: Int -> JSString

langDecoupages :: Int -> JSString
langDecoupages k = toJSString (W.decoupagesJson k)

foreign export javascript "langCout"
  langCout :: Int -> JSString

langCout :: Int -> JSString
langCout k = toJSString (W.coutJson k)

foreign export javascript "langFiltreRow"
  langFiltreRow :: Int -> Int -> JSString

langFiltreRow :: Int -> Int -> JSString
langFiltreRow i k = toJSString (W.filtreRowJson i k)

foreign export javascript "langTrace"
  langTrace :: Int -> JSString -> JSString

langTrace :: Int -> JSString -> JSString
langTrace i mot = toJSString (W.traceJson i (fromJSString mot))
