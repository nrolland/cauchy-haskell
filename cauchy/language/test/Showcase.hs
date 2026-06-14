-- | Les définitions d'exposition de la vitrine (page ⑤) : le tableau
-- de ④ §1 exécuté. Ce module est jugé par la suite de duels — le code
-- montré est le code jugé — et sérialisé pour les widgets par
-- @wasm/LanguageWidgets.hs@ : la même définition compte dans l'oracle
-- et dans la page.
{-# LANGUAGE DataKinds #-}
module Showcase
  ( AB (..)
  , sigma
  , Trop
  , decoupages
  , coutMinimal
  ) where

import Data.Monoid (Sum (..))
import Numeric.Natural (Natural)

import Data.Semiring (Semiring (..))
import Data.Semiring.Tropical (Extrema (..), Tropical (..))
import Data.Star (Star (..))

import qualified Data.Cauchy.Language.Poly as CP
import           Data.Cauchy.Language.Series (Series, fromPoly)

-- | L'alphabet des duels et des pages : deux lettres suffisent à la
-- non-commutativité.
data AB = A | B deriving (Eq, Ord, Show)

sigma :: [AB]
sigma = [A, B]

-- | Trop = (ℕ ∪ {∞}, min, +) : @Tropical 'Minima (Sum Natural)@ de
-- semirings (porte des bibliothèques du vert, 2026-06-12), instance
-- 'Star' comprise (@star _ = one@ — à poids ≥ 0, boucler ne diminue
-- jamais un coût).
type Trop = Tropical 'Minima (Sum Natural)

-- SNIPPET:lang-micro-pese
-- | p = (a + aa)* dans S⟨⟨Σ⟩⟩, S en paramètre : à S = ℕ, p(aⁿ) compte
-- les découpages de aⁿ en blocs a, aa — la récurrence de Fibonacci du
-- noyau, et le duel le juge contre elle, écrite à la main.
decoupages :: (Eq s, Semiring s) => Series AB s
decoupages = star (a `plus` (a `times` a))
  where a = fromPoly (CP.letter A)

-- | La même étoile, S = Trop, blocs pesés 3·a ⊕ 5·aa : p(aⁿ) est le
-- coût minimal d'un découpage — jugé contre la programmation
-- dynamique à la main.
coutMinimal :: Series AB Trop
coutMinimal = star (peso 3 a `plus` peso 5 (a `times` a))
  where
    a = fromPoly (CP.letter A)
    peso c = times (fromPoly (CP.fromTerms [([], Tropical (Sum c))]))
-- END:lang-micro-pese
