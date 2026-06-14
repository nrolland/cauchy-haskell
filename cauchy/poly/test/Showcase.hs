-- | Définitions d'exposition : la vitrine (pages ④⑤) extrait ces
-- snippets, la suite de duels exécute ces mêmes définitions — le code
-- montré est le code jugé, jamais retapé.
module Showcase
  ( fibonacci
  , catalan
  ) where

import Data.Semiring (one, plus, times)
import Data.Star (star)

import Data.Cauchy.Poly (x)
import Data.Cauchy.Series (Series, fromPoly)

-- SNIPPET:micro-fibonacci
-- (x + x²)* : l'étoile gardée de ② — A000045 attendu.
fibonacci :: Series Integer
fibonacci = star (xS `plus` (xS `times` xS))
  where xS = fromPoly x
-- END:micro-fibonacci

-- SNIPPET:micro-catalan
-- C = 1 + x∗C∗C, écrite telle quelle : le nœud que la paresse résout,
-- coefficient par coefficient, parce que le produit est gardé.
catalan :: Series Integer
catalan = c
  where
    c  = one `plus` (xS `times` (c `times` c))
    xS = fromPoly x
-- END:micro-catalan
