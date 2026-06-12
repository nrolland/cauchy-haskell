-- | The @Ord m@ contract of the core, executable (haddock of
-- "Data.MonoidSemiring", section "The role of @Ord m@"). The claim
-- splits the API in two halves, each with its own witness:
--
-- * /invariance/: re-keying a value between two orders on the same
--   carrier commutes with the algebra — QuickCheck properties;
-- * /observability/: 'toList' and 'support' reflect the order — one
--   value, two orders, two supports.
module OrdContract
  ( Rev (..)
  , reKey
  , invarianceLaws
  , witnessValue
  , observedSupport
  , observedSupportRev
  ) where

import           Data.Monoid     (Sum (..))
import           Numeric.Natural (Natural)
import           Test.QuickCheck

import           Data.MonoidSemiring
import           Data.Semiring (Semiring (..))

-- SNIPPET:rekey
-- | The same carrier under the opposite order: the monoid is unchanged,
-- only 'compare' flips.
newtype Rev = Rev { unRev :: Sum Natural }
  deriving (Eq, Show)

instance Ord Rev where compare (Rev a) (Rev b) = compare b a

instance Semigroup Rev where Rev a <> Rev b = Rev (a <> b)
instance Monoid    Rev where mempty = Rev mempty

-- | Transport along the identity of carriers, between the two orders.
reKey :: (Semiring s, Eq s)
      => MonoidSemiring (Sum Natural) s -> MonoidSemiring Rev s
reKey = fromList . map (\(m, c) -> (Rev m, c)) . toList
-- END:rekey

-- SNIPPET:ord-invariance
-- The algebra cannot tell the two orders apart: re-keying commutes
-- with every algebraic operation.
invarianceLaws :: Gen (MonoidSemiring (Sum Natural) Integer)
               -> Gen (Sum Natural)
               -> [(String, Property)]
invarianceLaws g gm =
  [ ("rekey-plus",  p2 (\f h -> reKey (f `plus` h)  == reKey f `plus` reKey h))
  , ("rekey-times", p2 (\f h -> reKey (f `times` h) == reKey f `times` reKey h))
  , ("rekey-coefficient",
      forAll g (\f -> forAll gm (\m ->
        coefficient (Rev m) (reKey f) == coefficient m f)))
  ]
  where p2 f = forAll g (\a -> forAll g (f a))
-- END:ord-invariance

-- SNIPPET:ord-observable
-- The observations can: the same value, x + x^2, enumerates its
-- support ascending — which list that is depends on the order.
witnessValue :: MonoidSemiring (Sum Natural) Integer
witnessValue = fromList [(Sum 1, 1), (Sum 2, 1)]

observedSupport :: [Natural]                  -- [1, 2]
observedSupport = map getSum (support witnessValue)

observedSupportRev :: [Natural]               -- [2, 1]
observedSupportRev = map (getSum . unRev) (support (reKey witnessValue))
-- END:ord-observable
