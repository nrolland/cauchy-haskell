-- | S[[x]] : la complétion x-adique de S[x] (pages ②③).
--
-- Le type est coinductif pur — signature @S × −@, destructeur total,
-- observation par préfixes. Le porteur est 'Infinite', le flux total
-- d'@infinite-list@ : le cas « la série se termine » est
-- irreprésentable ; reste l'obligation de productivité (②), portée par
-- les définitions gardées ci-dessous. Représentation figée au premier
-- jour du vert (2026-06-11).
--
-- L'égalité de S[[x]] n'est pas décidable : il n'y a pas d'instance
-- 'Eq'. L'unique observation est 'takeCoeffs' — l'égalité testée est
-- celle des préfixes tronqués, comme l'annonce ②.
module Data.Cauchy.Series
  ( Series
    -- * Du polynôme à la série
  , fromPoly
    -- * L'observation
  , takeCoeffs
    -- * Corollaire 1 de ③ : l'inverse, tête inversible
  , recipSeries
    -- * Taylor (② — exige ℚ ⊆ S)
  , expS
  , sinS
  , logS
  ) where

import Prelude hiding (negate)
import qualified Prelude as Num

import qualified Data.Euclidean as E
import           Data.Euclidean (Field)
import           Data.List.Infinite (Infinite (..))
import qualified Data.List.Infinite as Inf
import           Data.Semiring (Ring (..), Semiring (..))
import           Data.Star (Star (..))

import           Data.Cauchy.Poly (Poly, toCoeffs)

-- SNIPPET:series-type
-- | Le porteur de S[[x]] : un coefficient, puis encore une série —
-- la coalgèbre du foncteur @S × −@, sans cas de base.
newtype Series s = Series (Infinite s)
-- END:series-type

unS :: Series s -> Infinite s
unS (Series f) = f

-- | Le plongement S[x] → S[[x]] : bourrage explicite par des zéros.
fromPoly :: Semiring s => Poly s -> Series s
fromPoly p = Series (Inf.prependList (toCoeffs p) (Inf.repeat zero))

-- | Les k premiers coefficients. La seule observation du type.
takeCoeffs :: Semiring s => Int -> Series s -> [s]
takeCoeffs k (Series f) = Inf.take k f

-- SNIPPET:series-mul
-- | Produit de Cauchy, façon McIlroy. La première équation est la loi
-- de décalage @(x·v)·g = x·(v·g)@ rendue opérationnelle : elle produit
-- un constructeur sans toucher à g — c'est la garde du Théorème de
-- productivité (②), celle qui fait que @C = 1 + x∗C∗C@ se déplie seul.
mulS :: (Eq s, Semiring s) => Infinite s -> Infinite s -> Infinite s
mulS (f0 :< ft) g
  -- NOTE:==: tester « tête nulle » est un calcul — c'est le Eq s de l'instance qui le paie.
  -- NOTE:mulS: la queue seulement : g n'est pas consulté — (x·v)∗q = x·(v∗q), la garde de ② rendue opérationnelle.
  | f0 == zero = zero :< mulS ft g
mulS (f0 :< ft) g@(g0 :< gt) =
  -- NOTE:times: la convolution du noyau en habits de flux : tête p(0)·q(0), queue p(0)·q′ + p′∗q.
  (f0 `times` g0) :< Inf.zipWith plus (Inf.map (f0 `times`) gt) (mulS ft g)
-- END:series-mul

instance (Eq s, Semiring s) => Semiring (Series s) where
  zero  = Series (Inf.repeat zero)
  one   = Series (one :< Inf.repeat zero)
  plus  (Series f) (Series g) = Series (Inf.zipWith plus f g)
  times (Series f) (Series g) = Series (mulS f g)

instance (Eq s, Ring s) => Ring (Series s) where
  negate (Series f) = Series (Inf.map negate f)

-- SNIPPET:series-star
-- | L'étoile gardée de ② : l'unique solution de @star u = 1 + u ∗ star u@,
-- terme constant de u nul exigé — le contre-exemple @p = 1 + p@ de ②
-- est précisément ce que la garde interdit.
instance (Eq s, Semiring s) => Star (Series s) where
  star u@(Series (u0 :< _))
    | u0 /= zero = error "cauchy-poly : star — terme constant non nul (garde de ②)"
    | otherwise  = s
    where s = one `plus` (u `times` s)
-- END:series-star

-- SNIPPET:series-recip
-- | Corollaire 1 de ③ : si p(0) est inversible, p a un inverse dans
-- S[[x]]. De p = p₀ + x·v et p∗r = 1 : r₀ = p₀⁻¹ et, coefficient par
-- coefficient au-delà, r_{n+1} = p₀⁻¹ · (−(v∗r)_n).
recipSeries :: (Eq s, Field s) => Series s -> Series s
recipSeries (Series (p0 :< pt)) = r
  where
    i = one `E.quot` p0
    r = Series (i :< Inf.map (times i . negate) (unS (Series pt `times` r)))
-- END:series-recip

-- | L'intégration formelle : (∫f)₀ = 0, (∫f)_{n+1} = f_n / (n+1) —
-- la division par k consomme ℚ ⊆ S ('Fractional'). C'est elle qui
-- garde les équations de Taylor : le décalage est structurel.
integralS :: (Fractional s, Semiring s) => Series s -> Series s
integralS (Series f) =
  Series (zero :< Inf.zipWith (\c k -> c / fromInteger k) f (Inf.iterate (+ 1) 1))

-- SNIPPET:series-taylor
-- | Taylor par équations gardées (②) : exp = 1 + ∫exp ;
-- sin = ∫cos avec cos = 1 − ∫sin ; log(1+x) = ∫g avec g = 1 − x·g.
expS :: (Eq s, Fractional s, Semiring s) => Series s
expS = e where e = one `plus` integralS e

sinS :: (Eq s, Fractional s, Semiring s) => Series s
sinS = s
  where
    s = integralS c
    c = one `plus` Series (Inf.map Num.negate (unS (integralS s)))

logS :: (Eq s, Fractional s, Semiring s) => Series s
logS = integralS g
  where g = Series (one :< Inf.map Num.negate (unS g))
-- END:series-taylor
