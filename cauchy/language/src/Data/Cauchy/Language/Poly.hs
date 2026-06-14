-- | S⟨Σ⟩ : l'algèbre libre sur Σ, sans hypothèse de commutation entre
-- générateurs (page ①).
--
-- Le porteur est l'énoncé même de ① : @S⟨Σ⟩ = S[Σ*]@, le semi-anneau de
-- monoïde de la phase 0 instancié au monoïde libre sur Σ. Poser
-- @M := Σ*@ ne définit rien : la convolution du noyau /est/ le produit
-- de concaténation — la fibre @uv = w@ est l'ensemble des @|w|+1@
-- coupures de @w@ — et la non-commutativité des indéterminées est celle
-- du monoïde d'indices. L'instance 'Semiring' ci-dessous n'est que la
-- coercion de celle de la phase 0.
--
-- L'ordre d'observation des termes est l'ordre longueur-lexicographique
-- (le tableau de ①) : un @newtype@ sur l'indice, comme le contrat
-- d'@Ord m@ de @monoid-semiring@ le prescrit — jamais une comparaison
-- passée aux points d'appel.
module Data.Cauchy.Language.Poly
  ( Poly
  , ShortLex (..)
    -- * Construction et observation
  , fromTerms
  , toTerms
  , letter
  , at
    -- * Liberté (page ①, Théorème 2)
  , subst
  ) where

import qualified Data.MonoidSemiring as MS
import           Data.MonoidSemiring (MonoidSemiring)
import           Data.Semiring (Semiring (..))

-- SNIPPET:lang-poly-type
-- | S⟨Σ⟩ est S[M] au monoïde M = Σ* : aucune ligne de convolution n'est
-- ajoutée. L'égalité est celle de la représentation canonique
-- (l'invariant de @monoid-semiring@ : aucun zéro explicite) —
-- décidable, support fini.
newtype Poly a s = Poly (MonoidSemiring (ShortLex a) s)
  deriving Eq

-- | L'indice : Σ* dans l'ordre longueur-lexicographique. L'ordre n'est
-- pas un détail de l'arbre : c'est l'ordre d'observation du tableau de
-- ①, déclaré par le type de l'indice.
newtype ShortLex a = ShortLex [a]
  deriving (Eq, Show)

instance Ord a => Ord (ShortLex a) where
  compare (ShortLex u) (ShortLex v) =
    compare (length u) (length v) <> compare u v

instance Semigroup (ShortLex a) where
  ShortLex u <> ShortLex v = ShortLex (u ++ v)

instance Monoid (ShortLex a) where
  mempty = ShortLex []
-- END:lang-poly-type

-- | Somme de termes (mot, coefficient) ; les mots égaux se combinent
-- par 'plus', les zéros disparaissent.
fromTerms :: (Ord a, Semiring s, Eq s) => [([a], s)] -> Poly a s
fromTerms ts = Poly (MS.fromList [ (ShortLex w, c) | (w, c) <- ts ])

-- | Les termes du support, coefficients non nuls, en ordre
-- longueur-lexicographique croissant ; le polynôme nul donne @[]@.
toTerms :: Poly a s -> [([a], s)]
toTerms (Poly f) = [ (w, c) | (ShortLex w, c) <- MS.toList f ]

-- | Le générateur @a@, vu dans S⟨Σ⟩.
letter :: (Ord a, Semiring s, Eq s) => a -> Poly a s
letter a = Poly (MS.dirac (ShortLex [a]) one)

-- | Le coefficient du mot @w@ : la vue fonction totale, 'zero' hors
-- support.
at :: (Ord a, Semiring s) => [a] -> Poly a s -> s
at w (Poly f) = MS.coefficient (ShortLex w) f

-- SNIPPET:lang-poly-subst
-- | @subst σ p = h_σ(p)@ : l'unique morphisme S⟨Σ⟩ → S⟨Γ⟩ prolongeant
-- σ — la liberté de Σ*, Théorème 2 de ①, /sous l'hypothèse du
-- théorème/ : les scalaires sont centraux (ι : S → A central). Ici,
-- h_σ est donc un morphisme pour S commutatif — ou dès que les
-- coefficients de p commutent aux coefficients des σ(a). Seules les
-- indéterminées sont affranchies de toute commutation. Terme à terme :
-- @h_σ(c·a₁…aₖ) = c · σ(a₁) ∗ … ∗ σ(aₖ)@, l'ordre des facteurs
-- préservé.
subst :: (Ord b, Semiring s, Eq s) => (a -> Poly b s) -> Poly a s -> Poly b s
subst sg (Poly f) =
  foldr plus zero
    -- NOTE:scaleP: l'hypothèse de centralité du Théorème 2 de ① : le scalaire c passe devant le produit des σ(aᵢ) — exact si S commute aux coefficients des images
    [ scaleP c (foldr (times . sg) one w) | (ShortLex w, c) <- MS.toList f ]
  where
    scaleP c (Poly g) = Poly (MS.scale c g)
-- END:lang-poly-subst

instance (Ord a, Semiring s, Eq s) => Semiring (Poly a s) where
  zero  = Poly zero
  one   = Poly one
  plus  (Poly f) (Poly g) = Poly (plus f g)
  times (Poly f) (Poly g) = Poly (times f g)
