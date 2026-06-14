-- | La vitrine du volet 3 : l'exemple de ③, exécuté par la
-- bibliothèque. La définition est jugée par le duel « vitrine » de la
-- suite multi-duels contre le déroulé à la main de la page — le
-- snippet affiché et le code testé sont le même texte.
{-# LANGUAGE DataKinds #-}
module MultiShowcase (exemple) where

import Data.Cauchy.Multi
import Data.Cauchy.Order

-- SNIPPET:micro-division
-- p = x²y + xy² + y² divisé par (xy − 1, y² − 1), lex, x ≻ y :
-- les six pas de la division, joués par la bibliothèque.
exemple :: ([MPoly (Lex 2) Rational], MPoly (Lex 2) Rational)
exemple = division p [d1, d2]
  where
    m  = Lex . expo                     -- [a, b] ↦ x^a y^b
    p  = fromTerms [(m [2,1], 1), (m [1,2], 1), (m [0,2], 1)]
    d1 = fromTerms [(m [1,1], 1), (m [0,0], -1)]
    d2 = fromTerms [(m [0,2], 1), (m [0,0], -1)]
-- END:micro-division
