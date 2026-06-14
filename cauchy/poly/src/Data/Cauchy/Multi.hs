{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- | S[x₁,…,xₖ] : l'algèbre commutative libre (pages ①③ du volet 3).
--
-- Le porteur est l'énoncé même de ① : @S[x₁,…,xₖ] = S[ℕᵏ]@, le
-- semi-anneau de monoïde de la phase 0 instancié au monoïde commutatif
-- libre — le quotient @ab = ba@ que les langages annonçaient. La
-- convolution n'est pas réécrite ici ; la fibre β + γ = α est une
-- boîte, produit des anti-diagonales de l'univarié.
--
-- L'ordre d'observation est le paramètre du type d'indice @o@
-- (@cauchy-order@) : @MPoly (Lex 2) s@ et @MPoly (GrevLex 2) s@ sont
-- deux types — le contrat d'@Ord m@ du noyau, consommé. Le terme de
-- tête ('leading') et la division ('division') sont des fonctions de
-- ce choix ; le théorème de ③ : l'équation rendue est un certificat,
-- le reste n'est pas canonique (il dépend de la liste des diviseurs).
--
module Data.Cauchy.Multi
  ( MPoly
    -- * Construction et observation
  , fromTerms
  , toTerms
  , coefficient
  , leading
    -- * Liberté (page ①, Théorème 2)
  , evalAt
    -- * Itération (page ①, Théorème 3)
  , iterate2
    -- * Division (page ③, Théorème 1)
  , division
  ) where

import Prelude hiding (negate)

import Data.Maybe (listToMaybe)
import Numeric.Natural (Natural)

import Data.Euclidean (Field)
import qualified Data.Euclidean as E
import qualified Data.MonoidSemiring as MS
import Data.MonoidSemiring (MonoidSemiring)
import Data.Semiring (Ring (..), Semiring (..))

import Data.Cauchy.Order (MonomialOrder (..), components, expo, minus)
import qualified Data.Cauchy.Poly as P
import Data.Cauchy.Poly (Poly)

-- SNIPPET:multi-type
-- | S[x₁,…,xₖ] est S[M] au monoïde M = ℕᵏ, observé le long de l'ordre
-- du type d'indice @o@. L'égalité est celle de la représentation
-- canonique (l'invariant de @monoid-semiring@ : aucun zéro explicite).
newtype MPoly o s = MPoly (MonoidSemiring o s)
  deriving Eq
-- END:multi-type

-- | Somme de termes (indice, coefficient) ; les indices égaux se
-- combinent par 'plus', les zéros disparaissent.
fromTerms :: (MonomialOrder o, Semiring s, Eq s) => [(o, s)] -> MPoly o s
fromTerms = MPoly . MS.fromList

-- | Les termes du support, coefficients non nuls, en ordre ≺
-- croissant ; le polynôme nul donne @[]@.
toTerms :: MPoly o s -> [(o, s)]
toTerms (MPoly f) = MS.toList f

-- | La vue fonction totale : 'zero' hors support.
coefficient :: (MonomialOrder o, Semiring s) => o -> MPoly o s -> s
coefficient o (MPoly f) = MS.coefficient o f

-- SNIPPET:multi-leading
-- | Le terme de tête le long de l'ordre du type d'indice — le maximum
-- du support, la lecture que le contrat d'@Ord m@ du noyau autorise ;
-- 'Nothing' pour le polynôme nul. Sujet de ② : la tête est une
-- propriété du couple (p, ≺).
-- NOTE:MS.lookupMax: le maximum du porteur Map — l'habilitation O(log n) que le contrat d'Ord m du noyau déclarait, réifiée en export.
leading :: MPoly o s -> Maybe (o, s)
leading (MPoly f) = MS.lookupMax f
-- END:multi-leading

-- | @evalAt as p@ : l'unique morphisme S[x₁,…,xₖ] → S envoyant xᵢ sur
-- @as !! i@ (① Théorème 2 — la liberté commutative ; la commutation
-- des images est ici donnée par celle de S). Précondition : @as@ a
-- l'arité du type d'indice.
evalAt :: (MonomialOrder o, Semiring s) => [s] -> MPoly o s -> s
evalAt as p =
  foldr plus zero
    [ c `times` monome (components (toExp o)) | (o, c) <- toTerms p ]
  where
    -- La précondition d'arité est gardée, pas supposée : un zipWith
    -- nu tronquerait en silence — les variables manquantes vaudraient 1.
    monome es
      | length as /= length es =
          error "cauchy-poly : evalAt — arité étrangère au type"
      | otherwise = foldr times one (zipWith pw as es)
    -- Carrés itérés sur Natural : aucun passage par Int (un
    -- fromIntegral déborderait en silence au-delà de maxBound).
    pw _ 0 = one
    pw a e =
      let h  = pw a (e `div` 2)
          h2 = h `times` h
      in if even e then h2 else a `times` h2

-- | L'isomorphisme de curryfication S[ℕ²] ≅ S[ℕ][ℕ] (① Théorème 3),
-- lu vers l'univarié itéré : l'extérieur est la seconde indéterminée.
-- Le différentiel du contrat le confronte au produit de l'univarié —
-- un référent déjà vert.
iterate2 :: (MonomialOrder o, Arity o ~ 2, Semiring s, Eq s)
         => MPoly o s -> Poly (Poly s)
iterate2 p =
  P.fromCoeffs
    [ P.fromCoeffs [ coefficient (fromExp (expo [i, j])) p | i <- [0 .. mx] ]
    | j <- [0 .. my] ]
  where
    es = [ components (toExp o) | (o, _) <- toTerms p ]
    mx = maximum (0 : [ i | [i, _] <- es ]) :: Natural
    my = maximum (0 : [ j | [_, j] <- es ]) :: Natural

-- SNIPPET:multi-division
-- | Théorème 1 de ③ : pour tout ordre admissible et toute liste de
-- diviseurs non nuls, @division p ds@ rend @(qs, r)@ avec
-- @p = Σ qᵢ ∗ dᵢ + r@, @r@ réduit modulo la liste (aucun terme
-- divisible par un lm(dᵢ)) et lm(qᵢ ∗ dᵢ) ⪯ lm(p). La terminaison est
-- le bon ordre de ② ; les hypothèses sur S : corps (annuler la tête),
-- donc intègre (la tête est multiplicative). Le reste dépend de la
-- liste — l'équation rendue est le certificat, pas une forme normale.
division :: (MonomialOrder o, Field s, Ring s, Eq s)
         => MPoly o s -> [MPoly o s] -> ([MPoly o s], MPoly o s)
division p ds = go p (map (const zero) ds) zero
  where
    -- NOTE:go: la récurrence bien fondée du théorème : lm(f) décroît strictement à chaque pas — le bon ordre de ② force l'arrêt.
    go f qs r = case leading f of
      Nothing -> (qs, r)
      Just (m, c) -> case etape m c of
        Just (i, t) -> go (f `sub` (t `times` (ds !! i))) (chez i t qs) r
        Nothing ->
          let lt = fromTerms [(m, c)]
          in go (f `sub` lt) qs (r `plus` lt)
    -- Le premier dᵢ dont la tête divise lm(f) ; le terme quotient
    -- annule exactement la tête (E.quot scalaire : lc dᵢ inversible,
    -- S est un corps).
    -- NOTE:E.quot: S corps : lc(dᵢ) s'inverse — l'hypothèse du théorème qui paie l'annulation exacte de la tête.
    -- NOTE:minus: la soustraction partielle d'Exp : définie exactement quand lm(dᵢ) divise m — la divisibilité est un motif, pas un test séparé.
    etape m c = listToMaybe
      [ (i, fromTerms [(fromExp g, c `E.quot` lc)])
      | (i, d) <- zip [0 :: Int ..] ds
      , Just (lm, lc) <- [leading d]
      , Just g <- [toExp m `minus` toExp lm]
      ]
    chez i t qs = [ if j == i then q `plus` t else q
                  | (j, q) <- zip [0 ..] qs ]
    sub a b = a `plus` negate b
-- END:multi-division

-- SNIPPET:multi-semiring
instance (MonomialOrder o, Semiring s, Eq s) => Semiring (MPoly o s) where
  zero  = MPoly zero
  one   = MPoly one
  plus  (MPoly f) (MPoly g) = MPoly (f `plus` g)
  times (MPoly f) (MPoly g) = MPoly (f `times` g)

instance (MonomialOrder o, Ring s, Eq s) => Ring (MPoly o s) where
  negate (MPoly f) = MPoly (MS.scale (negate one) f)
-- END:multi-semiring
