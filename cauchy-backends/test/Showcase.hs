-- | La vitrine du volet 5 : les quatre calculs d'or des pages ⑤ et ⑥,
-- exécutés par la bibliothèque. Chaque valeur est jugée par un duel
-- « vitrine » de la suite contre son déroulé à la main (et croisée
-- contre numpy/Singular par les duels décisifs déjà en place) — le
-- snippet affiché et le code testé sont le même texte.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Showcase
  ( transformeeOr
  , compteOr
  , arithmetiqueOr
  , f4Or
  ) where

import Data.Maybe (fromMaybe)
import Data.Mod (Mod, invertMod)

import Data.Cauchy.Backends
  (BoundError, Counts, Root (..), convolve, convolveZ, f4, nttCount)
import Data.Cauchy.Multi (MPoly, fromTerms)
import Data.Cauchy.Order (Lex (..), expo)

-- SNIPPET:backends-transformee-or
-- 𝔽₁₇, n = 4, ω = 13 = 3⁴ (3 racine primitive, ord 16 ⇒ ω principale
-- d'ordre 4). Le produit (1 + x)(1 + 2x) par le chemin transformé —
-- 'convolve' = inverse ∘ (⊙) ∘ transformée — rend [1, 3, 2], le même
-- vecteur que la convolution naïve : 1 + 3x + 2x².
root4 :: Root (Mod 17)
root4 = Root w (inv w) (inv 4) 4
  where w     = 13
        inv x = fromMaybe (error "Showcase : 𝔽₁₇ — non inversible") (invertMod x)

transformeeOr :: [Mod 17]
transformeeOr = take 3 (convolve root4 [1, 1, 0, 0] [1, 2, 0, 0])
-- END:backends-transformee-or

-- SNIPPET:backends-compte-or
-- Le compte exact de la récursion radix-2, pour n = 2, 4, 8, 16 : à
-- chaque n, (n/2)·log₂n produits et n·log₂n sommes — l'escalier des
-- doublements, à comparer aux n² produits du chemin naïf (le croisement
-- de coût).
compteOr :: [(Int, Counts)]
compteOr = [ (n, nttCount n) | n <- [2, 4, 8, 16] ]
-- END:backends-compte-or

-- SNIPPET:backends-arith-or
-- ℤ par restes chinois, au-delà d'un seul premier : le carré de
-- 10⁶ + 10⁶x + 10⁶x² a pour coefficient central 3·10¹², bien au-dessus
-- du plus grand premier retenu (ℓ_max = 998244353 ≈ 10⁹). Aucune NTT sur
-- un seul ℓ ne le représente ; deux roues de résidus le reconstruisent
-- exactement (sous la borne vérifiée).
arithmetiqueOr :: Either BoundError [Integer]
arithmetiqueOr = convolveZ gros gros
  where gros = replicate 3 (10 ^ (6 :: Int))
-- END:backends-arith-or

-- SNIPPET:backends-f4-or
-- L'arc Gröbner par échelonnage : ⟨xy − 1, y² − 1⟩, lex (x ≻ y). F4
-- assemble les S-paires en matrices de Macaulay et les échelonne ; la
-- base réduite rendue est {y² − 1, x − y} — le d₃ = x − y du fil, le
-- même ensemble que la complétion de Buchberger, parce que l'unicité de
-- la base réduite (volet 4) l'exige.
f4Or :: [MPoly (Lex 2) Rational]
f4Or = f4 [d1, d2]
  where
    m  = Lex . expo                                  -- [a, b] ↦ x^a y^b
    d1 = fromTerms [(m [1, 1], 1), (m [0, 0], -1)]   -- xy − 1
    d2 = fromTerms [(m [0, 2], 1), (m [0, 0], -1)]   -- y² − 1
-- END:backends-f4-or
