-- | Le pesé : Mₙ(S), où l'étoile résout Bellman (page ④).
--
-- La décision n'était qu'un choix de S ; ici S varie, M est fixé.
-- Mₙ(S) est un semi-anneau — le noyau n'a jamais demandé que S soit
-- commutatif — et l'étoile y résout les équations de Bellman : le plus
-- court chemin est l'étoile de Kleene dans Mₙ(Trop), le comptage de
-- chemins celle de Mₙ(ℕ), sous une frontière d'hypothèses sur S
-- déclarée comme la division des polynômes a déclaré la sienne.
--
-- Le porteur est @Vector n (Vector n s)@ (@vector-sized@) : la
-- dimension est dans le type — une somme de matrices de tailles
-- distinctes ne se construit pas — et l'indexation par 'Finite' n est
-- totale, aucune vérification de borne n'apparaît dans l'algèbre.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Data.Cauchy.Language.Weighted
  ( Matrix
  , fromRows
  , toRows
  ) where

import           Data.Finite (finites)
import           Data.Foldable (foldl')
import           Data.Maybe (fromMaybe)
import qualified Data.Vector.Sized as V
import           GHC.TypeNats (KnownNat, Nat)

import           Data.Semiring (Semiring (..))
import           Data.Star (Star (..))

-- SNIPPET:matrix-type
-- | Le porteur de Mₙ(S) : n lignes de n entrées, la dimension dans le
-- type.
newtype Matrix (n :: Nat) s = Matrix (V.Vector n (V.Vector n s))
-- END:matrix-type

-- | Construction par lignes : n lignes de n entrées exigées, vérifié
-- bruyamment.
fromRows :: KnownNat n => [[s]] -> Matrix n s
fromRows rss =
  fromMaybe (error "cauchy-language : fromRows — n lignes de n entrées exigées") $
    do rows <- traverse V.fromList rss
       Matrix <$> V.fromList rows

-- | Observation par lignes.
toRows :: Matrix n s -> [[s]]
toRows (Matrix m) = map V.toList (V.toList m)

-- SNIPPET:matrix-semiring
-- | La structure additive est celle du module libre, point à point
-- (l''Applicative' zip des vecteurs dimensionnés) ; le produit est la
-- composition — la convolution sur l'indice @(i, j)@, somme sur les
-- 'finites' intermédiaires.
instance (KnownNat n, Semiring s) => Semiring (Matrix n s) where
  zero = Matrix (pure (pure zero))
  one  = Matrix (V.generate (\i -> V.generate (\j ->
           if i == j then one else zero)))
  plus (Matrix x) (Matrix y) = Matrix (V.zipWith (V.zipWith plus) x y)
  times (Matrix x) (Matrix y) =
    Matrix (V.generate (\i -> V.generate (\j ->
      foldl' plus zero
        [ (x ! i ! k) `times` (y ! k ! j) | k <- finites ])))
    where (!) = V.index

-- | @(star M)ᵢⱼ@ pèse l'ensemble des chemins i → j : l'élimination de
-- Kleene (Lehmann) — pour chaque pivot k,
-- @mᵢⱼ ⊕= mᵢₖ · (mₖₖ)* · mₖⱼ@, puis la clôture réflexive. L'étoile de
-- S sur le pivot est la frontière d'hypothèses de ④.
instance (KnownNat n, Star s) => Star (Matrix n s) where
  star m0 = one `plus` foldl' pivot m0 finites
    where
      pivot (Matrix x) k =
        Matrix (V.generate (\i -> V.generate (\j ->
          (x ! i ! j) `plus`
            ((x ! i ! k) `times` (sk `times` (x ! k ! j))))))
        where
          (!) = V.index
          -- NOTE:star: l'étoile de S sur le pivot : la frontière d'hypothèses de ④ — Trop la paie par « boucler ne diminue jamais », ℕ la refuse hors d'une diagonale nulle
          sk  = star (x ! k ! k)   -- une fois par pivot, pas n² fois
-- END:matrix-semiring
