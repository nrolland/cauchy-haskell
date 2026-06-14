-- | Exports JSFFI de la vitrine de paramétricité (volet 7) : les pages
-- appellent la bibliothèque elle-même, compilée en WebAssembly — jamais une
-- réplique JS. Module séparé du module de la collection
-- (@monoid-semiring/wasm/Exports.hs@) et de celui des langages : il enjambe
-- 'Data.Cauchy.Series' (cauchy-poly) et 'Data.Cauchy.Language.Weighted'
-- (cauchy-language), donc sa clôture wasm diffère ; un échec ici laisse les
-- autres modules intacts, seules les pages du volet 7 retombent sur leur
-- repli JS (annoncé par la pastille de provenance). Toute la logique vit
-- dans 'Data.Cauchy.Parametricite.Widgets', ce module n'est que la
-- frontière JS.
module Exports () where

import GHC.Wasm.Prim

import qualified Data.Cauchy.Parametricite.Widgets as W

-- ① la loi, ses deux membres calculés par instance (0 = 𝔹, 1 = Series ℚ,
-- 2 = tropical).
foreign export javascript "paramEtoile"
  paramEtoile :: Int -> JSString

paramEtoile :: Int -> JSString
paramEtoile m = toJSString (W.etoileJson m)

-- ② puissance contre fermeture : masses des sommes partielles sur Matrix 3
-- et — sur 𝔹 — la fermeture réelle (star de Matrix). Sélecteur : bit 0 =
-- cycle, bit 1 = porteur (0 = 𝔹, 1 = ℕ).
foreign export javascript "paramPuissance"
  paramPuissance :: Int -> JSString

paramPuissance :: Int -> JSString
paramPuissance v = toJSString (W.puissanceJson v)

-- ③ valeur contre sens : fibsBare et les coefficients de star(x+x²) relu
-- dans S (0 = ℚ, 1 = tropical pondéré, 2 = 𝔹).
foreign export javascript "paramValeurSens"
  paramValeurSens :: Int -> JSString

paramValeurSens :: Int -> JSString
paramValeurSens sr = toJSString (W.valeurSensJson sr)

-- ③ la liste géométrique : kⁿ = [xⁿ] star(k·x) sur Series Integer (k ∈ {1,2,3}).
foreign export javascript "paramListe"
  paramListe :: Int -> JSString

paramListe :: Int -> JSString
paramListe k = toJSString (W.listeJson k)

-- ④ graphe-fermeture : (closure A)₁₂ = star(a)·b·star(c), trois lectures.
-- Sélecteur : bit 0 = boucle a, bits 1+ = porteur (0 = regex, 1 = 𝔹, 2 = tropical).
foreign export javascript "paramGraphe"
  paramGraphe :: Int -> JSString

paramGraphe :: Int -> JSString
paramGraphe v = toJSString (W.grapheJson v)
