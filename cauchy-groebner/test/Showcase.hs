-- | La vitrine du volet 4 : les deux calculs d'or des pages ⑤ et ⑥,
-- exécutés par la bibliothèque. Chaque définition est jugée par un duel
-- « vitrine » de la suite contre son déroulé à la main (et croisée
-- contre Singular par les duels décisifs déjà en place) — le snippet
-- affiché et le code testé sont le même texte.
{-# LANGUAGE DataKinds #-}
module Showcase (arcReduite, cubiqueCutLex, cubiqueCutGrevlex) where

import Data.Cauchy.Groebner (buchberger, cut, reduce)
import Data.Cauchy.Multi (MPoly, fromTerms)
import Data.Cauchy.Order (GrevLex (..), Lex (..), expo)

-- SNIPPET:groebner-arc
-- L'arc des ordres : ⟨xy − 1, y² − 1⟩, base réduite lex (x ≻ y). Le
-- d₃ = x − y = Spol(d₁, d₂) que la page ① exhibait à la main y entre :
-- la sortie de la bibliothèque est {y² − 1, x − y}.
arcReduite :: [MPoly (Lex 2) Rational]
arcReduite = reduce (buchberger [d1, d2])
  where
    m  = Lex . expo                         -- [a, b] ↦ x^a y^b
    d1 = fromTerms [(m [1, 1], 1), (m [0, 0], -1)]   -- xy − 1
    d2 = fromTerms [(m [0, 2], 1), (m [0, 0], -1)]   -- y² − 1
-- END:groebner-arc

-- SNIPPET:groebner-cubique
-- La cubique tordue ⟨x² − y, x³ − z⟩ : la coupe lex de la base réduite
-- projette sur ℚ[y, z] (y³ − z²), tandis que la coupe grevlex est vide
-- — la même base, mais y² − xz reste en tête et masque la projection.
cubiqueCutLex :: [MPoly (Lex 3) Rational]
cubiqueCutLex = cut 1 (reduce (buchberger [f1, f2]))
  where
    m  = Lex . expo                         -- [a, b, c] ↦ x^a y^b z^c
    f1 = fromTerms [(m [2, 0, 0], 1), (m [0, 1, 0], -1)]   -- x² − y
    f2 = fromTerms [(m [3, 0, 0], 1), (m [0, 0, 1], -1)]   -- x³ − z

cubiqueCutGrevlex :: [MPoly (GrevLex 3) Rational]
cubiqueCutGrevlex = cut 1 (reduce (buchberger [f1, f2]))
  where
    m  = GrevLex . expo
    f1 = fromTerms [(m [2, 0, 0], 1), (m [0, 1, 0], -1)]   -- x² − y
    f2 = fromTerms [(m [3, 0, 0], 1), (m [0, 0, 1], -1)]   -- x³ − z
-- END:groebner-cubique
