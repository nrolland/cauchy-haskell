-- | The monoid semiring @M ->_0 S@: finitely supported functions from a
-- monoid @M@ to a semiring @S@, multiplied by the generalized Cauchy
-- product (convolution)
--
-- > (f * g)(s) = sum over uv = s of f(u) . g(v)
--
-- Instantiating @(M, S)@ yields polynomials @(N, +)@, formal languages
-- @(Sigma*, .)@, multivariate polynomials @(N^k, +)@, tropical algebra...
-- The convolution code never changes.
--
-- Representation invariant: the underlying 'Map' carries no explicit
-- 'zero' coefficient. Every constructor of this module maintains it;
-- 'Eq' relies on it.
--
-- == The role of @Ord m@
--
-- @Ord m@ does not belong to the implementation — it is not merely a
-- search order for the tree, observable by accident. It decides the
-- abstraction this type incarnates: 'compare' is /the/ order in which
-- terms are observed, and choosing it is part of choosing what a value
-- means. The precise statement is a failure of representation
-- independence, in one direction: re-keying a value between two orders
-- on the same carrier commutes with the algebra ('plus', 'times',
-- 'coefficient') but not with 'toList' or 'support' — so @Ord m@ does
-- not sit under the abstract type's existential, it is a free
-- parameter of the interface. Both halves are checked by the @oracle@
-- test suite (module @OrdContract@). Three clauses:
--
-- * /Observation./ 'toList' and 'support' enumerate in ascending
--   @Ord m@ order, and maximum-based machinery (leading terms, in a
--   multivariate layer) is entitled to read the 'Map' maximum in
--   O(log n). The semiring laws themselves never depend on the order.
--
-- * /One order per type./ By class coherence a type carries a single
--   'Ord' instance, so an alternative order on the same carrier enters
--   as a @newtype@ on the index (e.g. lex vs. grevlex on @N^k@) —
--   never as a comparison function passed at call sites. A passed-in
--   comparison can disagree with the tree's order and select a term
--   that 'Map' operations then fail to find: an incoherence no type
--   error reports.
--
-- * /Laws./ This module requires only that @Ord m@ be a total order.
--   A layer that interprets 'compare' must impose its own laws on the
--   index types it admits — e.g. monomial orders must be admissible
--   (a well-order, compatible with '<>', with 'mempty' minimal).
module Data.MonoidSemiring
  ( MonoidSemiring
  , fromList
  , toList
  , dirac
  , coefficient
  , support
  , scale
  , filterIndex
  ) where

import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Semiring (Semiring (..))

-- SNIPPET:m2s-type
-- | @f :: MonoidSemiring m s@ is a function @m -> s@ that is 'zero'
-- everywhere except on a finite set, its support.
newtype MonoidSemiring m s = MS (Map m s)
  deriving (Eq, Ord, Show)
-- END:m2s-type

-- SNIPPET:m2s-constructors
-- | Discard explicit zeros: the representation invariant.
normalize :: (Semiring s, Eq s) => Map m s -> Map m s
normalize = Map.filter (/= zero)

-- | Build from index–coefficient pairs; equal indices are combined with 'plus'.
fromList :: (Ord m, Semiring s, Eq s) => [(m, s)] -> MonoidSemiring m s
fromList = MS . normalize . Map.fromListWith plus

-- | Dirac mass: @dirac m c@ is @c@ at @m@, 'zero' elsewhere.
dirac :: (Ord m, Semiring s, Eq s) => m -> s -> MonoidSemiring m s
dirac m c = MS (normalize (Map.singleton m c))
-- END:m2s-constructors

-- | The support with its coefficients, in ascending index order.
toList :: MonoidSemiring m s -> [(m, s)]
toList (MS f) = Map.toList f

-- | Total function view: 'zero' off the support.
coefficient :: (Ord m, Semiring s) => m -> MonoidSemiring m s -> s
coefficient m (MS f) = Map.findWithDefault zero m f

-- | The indices carrying a non-'zero' coefficient, ascending.
support :: MonoidSemiring m s -> [m]
support (MS f) = Map.keys f

-- SNIPPET:convolution
instance (Ord m, Monoid m, Semiring s, Eq s)
      => Semiring (MonoidSemiring m s) where
  zero = MS Map.empty
  one  = dirac mempty one
  plus (MS f) (MS g) =
    MS (normalize (Map.unionWith plus f g))
  times (MS f) (MS g) =
    MS (normalize (Map.fromListWith plus
      [ (u <> v, a `times` b)
      | (u, a) <- Map.toList f
      , (v, b) <- Map.toList g ]))
-- END:convolution

-- SNIPPET:semimodule
-- | Left semimodule action of @S@ on @M ->_0 S@, pointwise.
scale :: (Semiring s, Eq s) => s -> MonoidSemiring m s -> MonoidSemiring m s
scale c (MS f) = MS (normalize (Map.map (c `times`) f))
-- END:semimodule

-- | Keep the indices satisfying a predicate (used for truncation).
filterIndex :: (m -> Bool) -> MonoidSemiring m s -> MonoidSemiring m s
filterIndex p (MS f) = MS (Map.filterWithKey (\m _ -> p m) f)
