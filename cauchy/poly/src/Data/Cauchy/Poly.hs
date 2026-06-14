-- | S[x] : l'algèbre libre sur un générateur (page ①).
--
-- Le porteur est l'énoncé même de ① : @S[x] = S[(ℕ,+)]@, le semi-anneau
-- de monoïde de la phase 0 instancié au monoïde libre sur un
-- générateur. La convolution n'est pas réécrite ici — elle vit dans
-- @monoid-semiring@, source unique.
--
-- Le vocabulaire de division (page ③) est celui de @semirings@ —
-- 'GcdDomain', 'Euclidean' — précisément parce que le référent @poly@
-- instancie les mêmes classes : le duel est « même classe, deux
-- instances ».
module Data.Cauchy.Poly
  ( Poly
    -- * Construction et observation
  , fromCoeffs
  , toCoeffs
  , x
  , leading
    -- * Évaluation et substitution (page ①)
  , eval
  , subst
  ) where

import Prelude hiding (negate, quotRem)

import Data.Monoid (Sum (..))
import Numeric.Natural (Natural)

import Data.Euclidean (Euclidean (..), Field, GcdDomain (..))
import qualified Data.Euclidean as E
import qualified Data.MonoidSemiring as MS
import Data.MonoidSemiring (MonoidSemiring)
import Data.Semiring (Ring (..), Semiring (..))

-- SNIPPET:poly-type
-- | S[x] est S[M] au monoïde M = (ℕ, +) : la composée des deux
-- adjonctions de ①. L'égalité est celle de la représentation canonique
-- (l'invariant de @monoid-semiring@ : aucun zéro explicite).
newtype Poly s = Poly (MonoidSemiring (Sum Natural) s)
  deriving Eq
-- END:poly-type

unPoly :: Poly s -> MonoidSemiring (Sum Natural) s
unPoly (Poly f) = f

-- | Coefficients denses, a₀ en tête ; les zéros de queue sont ignorés.
fromCoeffs :: (Eq s, Semiring s) => [s] -> Poly s
fromCoeffs cs = Poly (MS.fromList (zip (map Sum [0 ..]) cs))

-- | Coefficients denses, a₀ en tête, sans zéros de queue ;
-- le polynôme nul donne @[]@.
toCoeffs :: Semiring s => Poly s -> [s]
toCoeffs (Poly f) = case MS.toList f of
  [] -> []
  ts -> let Sum d = fst (last ts)
        in [ MS.coefficient (Sum k) f | k <- [0 .. d] ]

-- | Le générateur.
x :: (Eq s, Semiring s) => Poly s
x = Poly (MS.dirac (Sum 1) one)

-- | Degré et coefficient de tête ; 'Nothing' pour le polynôme nul.
-- Le terme de tête est le sujet de ③ — l'ordre total de ℕ le fournit
-- (la lecture du maximum, autorisée par le contrat de @Ord m@).
leading :: Poly s -> Maybe (Natural, s)
leading (Poly f) = (\(Sum d, c) -> (d, c)) <$> MS.lookupMax f

-- | @eval p a@ : l'unique morphisme S[x] → S envoyant x sur a (①),
-- par schéma de Horner sur les coefficients denses.
eval :: Semiring s => Poly s -> s -> s
eval p a = foldr (\c acc -> c `plus` (a `times` acc)) zero (toCoeffs p)

-- | @subst p q = p[q]@ : l'unique morphisme S[x] → S[x] envoyant x
-- sur q (① — la liberté, encore) ; somme des c·qᵏ sur le support.
subst :: (Eq s, Semiring s) => Poly s -> Poly s -> Poly s
subst (Poly f) q =
  foldr plus zero [ scaleP c (powP k) | (Sum k, c) <- MS.toList f ]
  where
    scaleP c r = Poly (MS.scale c (unPoly r))
    powP k = foldr times one (replicate (fromIntegral k) q)

instance (Eq s, Semiring s) => Semiring (Poly s) where
  zero  = Poly zero
  one   = Poly one
  plus  (Poly f) (Poly g) = Poly (f `plus` g)
  times (Poly f) (Poly g) = Poly (f `times` g)

instance (Eq s, Ring s) => Ring (Poly s) where
  negate (Poly f) = Poly (MS.scale (negate one) f)

instance (Eq s, Field s) => GcdDomain (Poly s) where
  divide a b
    | b == zero = Nothing
    | otherwise = case quotRem a b of
        (q, r) | r == zero -> Just q
               | otherwise -> Nothing
  gcd a b
    | b == zero = a
    | otherwise = E.gcd b (snd (quotRem a b))

-- SNIPPET:poly-division
-- | Théorème 1 de ③ : division par le terme de tête, @lc b@ inversible
-- (ici S est un corps : 'E.quot' scalaire est cette inversion). Chaque
-- pas annule exactement le terme de tête du reste — le degré décroît,
-- l'algorithme termine : la preuve est l'algorithme.
instance (Eq s, Field s) => Euclidean (Poly s) where
  -- NOTE:leading: le terme de tête : max du support — la lecture en O(log n) que le contrat de Ord m du noyau autorise.
  quotRem a b = case leading b of
    Nothing       -> error "cauchy-poly : quotRem — division par zéro"
    -- NOTE:go: la récurrence bien fondée du théorème de division : deg r décroît strictement, l'ordre de ℕ force l'arrêt.
    Just (db, lb) -> go zero a
      where
        go q r = case leading r of
          Just (dr, lr) | dr >= db ->
            -- NOTE:E.quot: hypothèse 2 du théorème : lc(b) inversible — sur un corps, le quot scalaire est cette inversion.
            -- NOTE:negate: hypothèse 1 : la soustraction — « annuler la tête » exige l'anneau.
            let m = Poly (MS.dirac (Sum (dr - db)) (lr `E.quot` lb))
            in go (q `plus` m) (r `plus` negate (m `times` b))
          _ -> (q, r)
  degree = maybe 0 fst . leading
-- END:poly-division
