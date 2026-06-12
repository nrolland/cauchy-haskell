-- | Exposition only: a verbatim reproduction of the 'Semiring' class from
-- the @semirings@ package, which the library depends on ('fromNatural',
-- which has a default, is omitted). The explainer series extracts the
-- snippets below; compiling this module keeps them honest. No other
-- module imports this one.
module SemiringClass
  ( Semiring(..)
  ) where

-- SNIPPET:semiring-class
class Semiring r where
  zero  :: r
  one   :: r
  plus  :: r -> r -> r
  times :: r -> r -> r
-- END:semiring-class

-- SNIPPET:semiring-instances
instance Semiring Integer where
  zero = 0; one = 1; plus = (+); times = (*)

instance Semiring Bool where
  zero = False; one = True; plus = (||); times = (&&)
-- END:semiring-instances
