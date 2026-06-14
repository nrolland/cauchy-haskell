-- | Les expressions rationnelles : un filtre par dérivées (page ③).
--
-- Les expressions engendrées par les lettres sous +, ∗ et l'étoile
-- dénotent des séries ; la dérivée se calcule /sur la syntaxe/, en
-- miroir des lois de ② ; le filtre est w ∈ ⟦e⟧ ⇔ ν(∂_w e). Les
-- dérivées d'une expression, modulo
-- associativité-commutativité-idempotence de + (ACI), sont en nombre
-- fini (Brzozowski) — l'automate est leur graphe.
--
-- La syntaxe a ses constructeurs : elle /est/ l'énoncé de ③, pas un
-- choix de représentation.
module Data.Cauchy.Language.Rational
  ( Expr (..)
    -- * ν et ∂ sur la syntaxe (miroir des lois de ②)
  , nuE
  , deltaE
    -- * Le filtre
  , match
    -- * La dénotation : ③ rejoint ②
  , denote
    -- * Brzozowski : finitude modulo ACI
  , normACI
  , derivatives
  ) where

import           Control.Comonad.Cofree (unfold)
import qualified Data.Set as Set
import           Data.Semiring (Semiring (..))

import           Data.Cauchy.Language.Series (Series, fromCofree)

-- SNIPPET:expr-type
-- | La syntaxe finie sur l'algèbre : lettres, +, concaténation,
-- étoile.
data Expr a
  = EZero
  | EOne
  | ELetter a
  | EPlus  (Expr a) (Expr a)
  | ETimes (Expr a) (Expr a)
  | EStar  (Expr a)
  deriving (Eq, Ord, Show)
-- END:expr-type

-- SNIPPET:expr-derivee
-- | ν(e) : le mot vide appartient-il à ⟦e⟧ ?
nuE :: Expr a -> Bool
nuE EZero        = False
nuE EOne         = True
nuE (ELetter _)  = False
nuE (EPlus e f)  = nuE e || nuE f
nuE (ETimes e f) = nuE e && nuE f
nuE (EStar _)    = True

-- | ∂ₐ sur la syntaxe, en miroir des lois de ② — Leibniz (le terme
-- ν(e)·∂ₐf n'apparaît que si e est nullable) et étoile comprises.
deltaE :: Eq a => a -> Expr a -> Expr a
deltaE _ EZero       = EZero
deltaE _ EOne        = EZero
deltaE a (ELetter b) = if a == b then EOne else EZero
deltaE a (EPlus e f) = EPlus (deltaE a e) (deltaE a f)
deltaE a (ETimes e f)
  | nuE e            = EPlus (ETimes (deltaE a e) f) (deltaE a f)
  | otherwise        = ETimes (deltaE a e) f
deltaE a (EStar e)   = ETimes (deltaE a e) (EStar e)

-- | Le filtre : @match e w = ν(∂_w e)@.
match :: Eq a => Expr a -> [a] -> Bool
match e = nuE . foldl (flip deltaE) e
-- END:expr-derivee

-- SNIPPET:expr-denote
-- | La série /caractéristique/ de ⟦e⟧ — 'one' sur les mots filtrés,
-- 'zero' ailleurs : l'unique morphisme de coalgèbres de la syntaxe,
-- munie du destructeur (ν_E, ∂_E), vers la coalgèbre finale S⟨⟨Σ⟩⟩.
-- Brzozowski en une ligne : la finalité de ② appliquée à ③. Pour
-- S = Bool c'est la dénotation de ③ ; pour S non idempotent (ℕ) ce
-- n'est /pas/ le compte des analyses — le comptage de ④ passe par les
-- automates pondérés, non par cette série.
denote :: (Eq a, Semiring s) => Expr a -> Series a s
denote = fromCofree . unfold (\e -> (coeff e, \a -> deltaE a e))
  where
    coeff e = if nuE e then one else zero
-- END:expr-denote

-- | La forme canonique modulo ACI de + : les sommandes aplatis dans un
-- ensemble (associativité), trié (commutativité), sans doublon
-- (idempotence) — et rien d'autre : la finitude de Brzozowski est
-- énoncée modulo ACI seul.
normACI :: Ord a => Expr a -> Expr a
normACI e = case e of
  EPlus _ _  -> rebuild (Set.toAscList (summands e))
  ETimes f g -> ETimes (normACI f) (normACI g)
  EStar f    -> EStar (normACI f)
  _          -> e
  where
    summands (EPlus f g) = summands f `Set.union` summands g
    summands f           = Set.singleton (normACI f)
    rebuild [x]      = x
    rebuild (x : xs) = EPlus x (rebuild xs)
    rebuild []       = EZero  -- inatteignable : EPlus a deux sommandes

-- | L'ensemble — fini, Brzozowski — des dérivées de e modulo ACI,
-- atteintes depuis e sur l'alphabet donné, e compris ; les éléments
-- sont en forme 'normACI'. L'automate des dérivées est leur graphe
-- sous 'deltaE' ; la saturation de l'exploration — la frontière qui se
-- vide — est le constat de finitude.
derivatives :: (Ord a) => [a] -> Expr a -> [Expr a]
derivatives sigma e0 = go (Set.singleton q0) [q0]
  where
    q0 = normACI e0
    go seen []          = Set.toAscList seen
    go seen (q : queue) = go seen' (queue ++ fresh)
      where
        (seen', fresh) = foldl step (seen, []) sigma
        step (s, qs) a =
          let q' = normACI (deltaE a q)
          in if Set.member q' s then (s, qs) else (Set.insert q' s, q' : qs)
