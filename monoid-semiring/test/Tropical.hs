-- | Min-plus semiring. 'Nothing' is @+oo@ (the 'zero' of the semiring).
-- Coefficient type for the oracle's third instance and the explainer.
module Tropical
  ( Tropical(..)
  ) where

import Data.Semiring (Semiring (..))

-- SNIPPET:tropical
newtype Tropical = Tropical (Maybe Integer)
  deriving (Eq, Ord, Show)

instance Semiring Tropical where
  zero = Tropical Nothing
  one  = Tropical (Just 0)
  plus (Tropical a) (Tropical b) = Tropical (minMaybe a b)
    where minMaybe Nothing y = y
          minMaybe x Nothing = x
          minMaybe (Just x) (Just y) = Just (min x y)
  times (Tropical a) (Tropical b) = Tropical ((+) <$> a <*> b)
-- END:tropical
