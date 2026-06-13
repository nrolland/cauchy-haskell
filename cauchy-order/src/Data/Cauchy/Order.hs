{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-- | Ordres monomiaux sur ℕᵏ (page ②).
--
-- Le porteur est l'énoncé même de ② : un ordre admissible — total,
-- compatible avec l'addition, zéro minimal, donc un bon ordre par le
-- lemme de Dickson — entre comme /newtype d'indice/, jamais comme une
-- fonction de comparaison passée aux points d'appel : c'est le
-- paramètre libre que le contrat d'@Ord m@ de @monoid-semiring@
-- déclare, consommé ici. Un type d'indice = un ordre ; @S[ℕᵏ]@ sous
-- lex et sous grevlex sont deux types.
--
-- L'arithmétique de 'Exp' (le monoïde, la divisibilité) est le
-- vocabulaire des duels ; les trois 'compare' sont jugés par les
-- lignes d'admissibilité du contrat — totalité, compatibilité avec
-- l'addition, zéro minimal, coïncidence à k = 1, témoins de
-- séparation.
module Data.Cauchy.Order
  ( -- * Multi-exposants
    Exp
  , expo
  , components
  , totalDegree
  , divides
  , minus
  , sup
    -- * Les trois ordres, en newtypes d'indice
  , Lex (..)
  , GrLex (..)
  , GrevLex (..)
    -- * Le pont indice ↔ exposant
  , MonomialOrder (..)
  ) where

import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, Nat, natVal)
import Numeric.Natural (Natural)

-- SNIPPET:order-exp
-- | Multi-exposant : un élément de ℕᵏ, le @k@ au niveau des types —
-- deux arités distinctes sont deux types, aucun mélange ne compile.
-- Invariant : la liste interne a exactement @k@ composantes ('expo'
-- est l'unique constructeur).
newtype Exp (k :: Nat) = Exp [Natural]
  deriving (Eq, Show)

-- | L'unique constructeur : refuse toute liste d'arité étrangère.
expo :: forall k. KnownNat k => [Natural] -> Exp k
expo ns
  | fromIntegral (length ns) == natVal (Proxy :: Proxy k) = Exp ns
  | otherwise = error "cauchy-order : expo — arité étrangère au type"

-- | Le monoïde produit : l'addition composante par composante.
-- NOTE:zipWith: licite : les deux listes ont k composantes — l'invariant d'expo, partagé via le type.
instance Semigroup (Exp k) where
  Exp u <> Exp v = Exp (zipWith (+) u v)

instance KnownNat k => Monoid (Exp k) where
  mempty = Exp (replicate (fromIntegral (natVal (Proxy :: Proxy k))) 0)
-- END:order-exp

-- | Les composantes, dans l'ordre des indéterminées.
components :: Exp k -> [Natural]
components (Exp ns) = ns

-- | Le degré total @|α|@.
totalDegree :: Exp k -> Natural
totalDegree (Exp ns) = sum ns

-- | La divisibilité des monômes : l'ordre produit, partiel —
-- @x^β | x^α@ si et seulement si chaque composante de β est ≤ à celle
-- de α. C'est l'ordre que ① déclare insuffisant : il ne compare pas
-- tout.
divides :: Exp k -> Exp k -> Bool
divides (Exp u) (Exp v) = and (zipWith (<=) u v)

-- | La soustraction partielle : @α `minus` β@ existe exactement quand
-- @β `divides` α@ — c'est l'exposant du quotient de monômes.
minus :: Exp k -> Exp k -> Maybe (Exp k)
minus a@(Exp u) b@(Exp v)
  | divides b a = Just (Exp (zipWith (-) u v))
  | otherwise   = Nothing

-- | Le supremum composante par composante : α∨β, l'exposant du ppcm
-- des monômes — la borne du treillis de 'divides' (α et β le divisent,
-- et il divise tout multiple commun). C'est le coin commun où la
-- série 4 hisse deux têtes pour les annuler (② Définition 1).
-- NOTE:zipWith: licite : les deux listes ont k composantes — l'invariant d'expo, partagé via le type.
sup :: Exp k -> Exp k -> Exp k
sup (Exp u) (Exp v) = Exp (zipWith max u v)

-- SNIPPET:order-newtypes
-- | L'ordre lexicographique : la première composante non nulle de
-- α − β décide.
newtype Lex (k :: Nat) = Lex (Exp k)
  deriving (Eq, Show)

-- | Le degré total d'abord, lex en départage.
newtype GrLex (k :: Nat) = GrLex (Exp k)
  deriving (Eq, Show)

-- | Le degré total d'abord ; à degré égal, la dernière composante non
-- nulle de α − β, négative, l'emporte.
newtype GrevLex (k :: Nat) = GrevLex (Exp k)
  deriving (Eq, Show)

-- À arité égale, l'ordre lexicographique des listes EST lex.
instance Ord (Lex k) where
  compare (Lex u) (Lex v) = compare (components u) (components v)

-- NOTE:totalDegree: le degré total d'abord — la graduation que « gr » annonce ; à degré égal, le départage est lex.
instance Ord (GrLex k) where
  compare (GrLex u) (GrLex v) =
    compare (totalDegree u) (totalDegree v)
      <> compare (components u) (components v)

-- À degré égal, la dernière composante où α et β diffèrent — première
-- des listes renversées — décide, en sens inverse.
-- NOTE:reverse: le renversement : la dernière composante non nulle de α − β, négative, l'emporte — v et u échangés font le sens inverse.
instance Ord (GrevLex k) where
  compare (GrevLex u) (GrevLex v) =
    compare (totalDegree u) (totalDegree v)
      <> compare (reverse (components v)) (reverse (components u))
-- END:order-newtypes

instance Semigroup (Lex k) where
  Lex a <> Lex b = Lex (a <> b)
instance KnownNat k => Monoid (Lex k) where
  mempty = Lex mempty

instance Semigroup (GrLex k) where
  GrLex a <> GrLex b = GrLex (a <> b)
instance KnownNat k => Monoid (GrLex k) where
  mempty = GrLex mempty

instance Semigroup (GrevLex k) where
  GrevLex a <> GrevLex b = GrevLex (a <> b)
instance KnownNat k => Monoid (GrevLex k) where
  mempty = GrevLex mempty

-- SNIPPET:order-class
-- | Le pont entre un type d'indice ordonné et son exposant : la couche
-- polynomiale (division, évaluation) lit les composantes à travers
-- lui, sans jamais savoir quel ordre la trie.
class (Ord o, Monoid o) => MonomialOrder o where
  type Arity o :: Nat
  toExp   :: o -> Exp (Arity o)
  fromExp :: Exp (Arity o) -> o

instance KnownNat k => MonomialOrder (Lex k) where
  type Arity (Lex k) = k
  toExp (Lex e) = e
  fromExp = Lex

instance KnownNat k => MonomialOrder (GrLex k) where
  type Arity (GrLex k) = k
  toExp (GrLex e) = e
  fromExp = GrLex

instance KnownNat k => MonomialOrder (GrevLex k) where
  type Arity (GrevLex k) = k
  toExp (GrevLex e) = e
  fromExp = GrevLex
-- END:order-class
