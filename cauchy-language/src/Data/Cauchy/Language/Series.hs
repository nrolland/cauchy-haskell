-- | S⟨⟨Σ⟩⟩ : toutes les fonctions Σ* → S (page ②).
--
-- La finitude locale de Σ* — chaque fibre de coupure @uv = w@ est
-- finie — étend la convolution à toutes les fonctions, sans condition
-- de support. Sur S⟨⟨Σ⟩⟩ la paire (terme constant ν, dérivées ∂ₐ) est
-- le destructeur tête\/queue du volet 1 à plusieurs lettres ; toute
-- équation gardée (ν = 0) a une unique solution par récurrence sur la
-- longueur.
--
-- Le porteur est @'Cofree' ((->) a) s@ : le comonade colibre sur le
-- foncteur reader — la coalgèbre finale du foncteur @S × (−)^Σ@. Le
-- destructeur de ② est son interface native et l'unicité des solutions
-- gardées /est/ la finalité.
--
-- L'égalité de S⟨⟨Σ⟩⟩ n'est pas décidable : il n'y a pas d'instance
-- 'Eq'. L'observation est 'at' — l'égalité testée est celle des
-- sections finies par longueur (|w| ≤ n), comme l'annonce ②.
--
-- == Note de transition (phase 5, datée 2026-06-12)
--
-- Le branchement par fonction n'a pas de partage : chaque observation
-- recalcule. La représentation mémoïsante (@MemoTrie@ :
-- @Cofree ((:->:) a) s@ — même forme cofibre, foncteur de branchement
-- remplacé par son trie, @trie@\/@untrie@ = @tabulate@\/@index@)
-- s'échange derrière ce @newtype@ sans changer une signature. Pour la
-- /coexistence/ des deux représentations — exigée par les duels
-- naïf\/rapide de la phase 5 — la généralisation est additive :
-- @SeriesF f s = Cofree f s@ sous @(Representable f, Rep f ~ a)@ ;
-- les définitions ci-dessous sont les spécialisations à @(->) a@ de
-- @pureRep@\/@liftR2@\/@tabulate@\/@index@, et @adjunctions@ (le
-- propriétaire de ce vocabulaire, déjà dans la clôture de compilation
-- via @vector-sized@) n'entrera en dépendance directe qu'à ce
-- moment-là. @Series@ restera l'instanciation de référence.
module Data.Cauchy.Language.Series
  ( Series
    -- * Du polynôme à la série
  , fromPoly
    -- * Le destructeur (ν, ∂ₐ) et l'observation
  , nu
  , delta
  , at
    -- * Le porteur, exposé pour l'outillage comonadique
  , toCofree
  , fromCofree
  ) where

import           Control.Comonad.Cofree (Cofree (..))

import           Data.Semiring (Semiring (..))
import           Data.Star (Star (..))

import qualified Data.Cauchy.Language.Poly as P
import           Data.Cauchy.Language.Poly (Poly)

-- SNIPPET:lang-series-type
-- | Le porteur de S⟨⟨Σ⟩⟩ : le comonade colibre sur le foncteur reader,
-- c'est-à-dire la coalgèbre finale de @S × (−)^Σ@ — le destructeur
-- (ν, ∂ₐ) de ② est son interface native.
newtype Series a s = Series (Cofree ((->) a) s)
-- END:lang-series-type

-- | Le porteur, à coût nul.
toCofree :: Series a s -> Cofree ((->) a) s
toCofree (Series c) = c

-- | Réciproque de 'toCofree'.
fromCofree :: Cofree ((->) a) s -> Series a s
fromCofree = Series

-- | Le plongement S⟨Σ⟩ → S⟨⟨Σ⟩⟩ : tabuler la fonction coefficient.
fromPoly :: (Ord a, Semiring s) => Poly a s -> Series a s
fromPoly p = Series (go id)
  where
    go pre = P.at (pre []) p :< \a -> go (pre . (a :))

-- SNIPPET:lang-series-destructeur
-- | ν : le terme constant, coefficient du mot vide.
nu :: Semiring s => Series a s -> s
nu (Series (c :< _)) = c

-- | ∂ₐ : la queue selon @a@ — @(∂ₐ p)(w) = p(aw)@, la re-indexation
-- de ②.
delta :: (Ord a, Semiring s) => a -> Series a s -> Series a s
delta a (Series (_ :< f)) = Series (f a)

-- | Le coefficient du mot @w@ : la marche ν ∘ ∂_w — l'observation de
-- ② est ici définitionnelle ; son ancre externe est le duel contre le
-- coefficient calculé à la main.
at :: (Ord a, Semiring s) => [a] -> Series a s -> s
at w p = nu (foldl (flip delta) p w)
-- END:lang-series-destructeur

-- | La série nulle : son propre ∂ₐ pour toute lettre.
zeroC :: Semiring s => Cofree ((->) a) s
zeroC = zero :< const zeroC

-- SNIPPET:lang-series-semiring
-- | La structure additive est point à point — le module libre sur Σ* ;
-- le produit est la règle de Leibniz de ②, prise comme définition
-- corécursive : @ν(p∗q) = νp·νq@ et @∂ₐ(p∗q) = ∂ₐp ∗ q + ν(p)·∂ₐq@.
instance (Ord a, Semiring s, Eq s) => Semiring (Series a s) where
  zero = Series zeroC
  one  = Series (one :< const zeroC)
  plus (Series u0) (Series v0) = Series (plusC u0 v0)
  times (Series u0) (Series v0) = Series (go u0 v0)
    where
      go (x :< f) v@(y :< g) =
        -- NOTE:fmap: le côté de l'action scalaire — ν(p) multiplie à gauche ; S n'est pas supposé commutatif, et l'instance M₂(Bool) de l'oracle juge ce côté
        (x `times` y) :< \a -> plusC (go (f a) v) (fmap (x `times`) (g a))

plusC :: Semiring s => Cofree ((->) a) s -> Cofree ((->) a) s -> Cofree ((->) a) s
plusC (x :< f) (y :< g) = (x `plus` y) :< \a -> plusC (f a) (g a)

-- | L'étoile gardée de ② : ν(p*) = 1 et @∂ₐ(p*) = ∂ₐp ∗ p*@, prises
-- comme définition — l'équation gardée nouée sur elle-même ; terme
-- constant de p nul exigé, vérifié bruyamment.
instance (Ord a, Semiring s, Eq s) => Star (Series a s) where
  star p
    | nu p /= zero =
        -- NOTE:error: la garde du théorème d'unicité de ②, hors de portée du type : vérifiée à l'entrée — p = 1 + p échoue bruyamment au lieu de boucler
        error "cauchy-language : étoile non gardée — ν p = 0 exigé"
    | otherwise = s
    where
      s = Series (one :< \a -> toCofree (delta a p `times` s))
-- END:lang-series-semiring
