-- | Les lignes d'admissibilité du contrat de ②, en duels exécutables.
--
-- ② admissibilité de lex, grlex, grevlex : totalité (cohérence avec
--   l'égalité), compatibilité avec +, zéro minimal — QuickCheck sur
--   ℕ³ ; à k = 1 les trois coïncident avec ≤ (l'unicité du Théorème 1,
--   témoignée) ; témoins de séparation (lex ≠ gradués à k = 2,
--   grlex ≠ grevlex à k = 3).
--
-- S'y ajoute la couche « contrat Haskell » des instances —
-- transitivité, antisymétrie et totalité d'Ord, lois de
-- Semigroup\/Monoid — déléguée aux batteries de
-- @quickcheck-classes-base@ ('runProperty' du harnais) : ces lois ne
-- sont pas la Définition 1, elles n'impliquent pas la totalité au sens
-- de ② et ne la remplacent pas.
--
-- Les référents sont à la main ou constants ; le bon fondement ne se
-- teste pas par tirage — la division de cauchy-poly le consomme.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main (main) where

import Control.Monad (unless)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, natVal)
import Numeric.Natural (Natural)
import System.Exit (exitFailure)

import Test.Cauchy.Oracle (Duel (..), Verdict, lawDuel, pureReferee,
                           runDuel, runProperty, runSuite)
import Test.QuickCheck
import Test.QuickCheck.Classes.Base (Laws (..), commutativeMonoidLaws,
                                     eqLaws, monoidLaws, ordLaws,
                                     semigroupLaws)

import Data.Cauchy.Order

-- ---------------------------------------------------------------------
-- Générateurs : des composantes petites — les contre-exemples d'ordre
-- vivent près de l'origine.

genComp :: Gen Natural
genComp = fromIntegral <$> chooseInt (0, 4)

genComps :: Int -> Gen [Natural]
genComps k = vectorOf k genComp

shrinkComps :: [Natural] -> [[Natural]]
shrinkComps ns =
  [ take i ns ++ [n'] ++ drop (i + 1) ns
  | (i, n) <- zip [0 :: Int ..] ns
  , n' <- shrink n
  ]

shrinkPair :: (a -> [a]) -> (a, a) -> [(a, a)]
shrinkPair s (a, b) = [(a', b) | a' <- s a] ++ [(a, b') | b' <- s b]

shrinkTriple :: (a -> [a]) -> (a, a, a) -> [(a, a, a)]
shrinkTriple s (a, b, c) =
     [(a', b, c) | a' <- s a]
  ++ [(a, b', c) | b' <- s b]
  ++ [(a, b, c') | c' <- s c]

-- ---------------------------------------------------------------------
-- Le contrat Haskell des instances, délégué aux batteries de
-- quickcheck-classes-base. Les orphelines sont du test, pas de la
-- bibliothèque : un utilisateur de cauchy-order choisit ses tirages.

instance KnownNat k => Arbitrary (Exp k) where
  arbitrary = expo <$> genComps (fromIntegral (natVal (Proxy :: Proxy k)))
  shrink = map expo . shrinkComps . components

instance KnownNat k => Arbitrary (Lex k) where
  arbitrary = Lex <$> arbitrary
  shrink (Lex e) = map Lex (shrink e)

instance KnownNat k => Arbitrary (GrLex k) where
  arbitrary = GrLex <$> arbitrary
  shrink (GrLex e) = map GrLex (shrink e)

instance KnownNat k => Arbitrary (GrevLex k) where
  arbitrary = GrevLex <$> arbitrary
  shrink (GrevLex e) = map GrevLex (shrink e)

contrat
  :: forall o. (MonomialOrder o, Arbitrary o, Show o)
  => String -> Proxy o -> [IO Verdict]
contrat nom p =
  [ runProperty 1000 (nom ++ " : " ++ lawsTypeclass ls ++ " — " ++ ln) lp
  | ls <- [ eqLaws p, ordLaws p, semigroupLaws p, monoidLaws p
          , commutativeMonoidLaws p ]
  , (ln, lp) <- lawsProperties ls
  ]

-- ---------------------------------------------------------------------
-- Les trois clauses de l'admissibilité (Définition 1 de ②), par ordre.
-- Le paramètre est l'habillage [Natural] → o : un ordre, un type.

admissibility
  :: (Ord o, Show o)
  => String -> ([Natural] -> o) -> [IO Verdict]
admissibility nom wrap =
  [ runDuel 1000 $ lawDuel (nom ++ " : totalité — compare cohérent avec l'égalité")
      (genPair3) (shrinkPair shrinkComps) $
      \(a, b) -> (compare (wrap a) (wrap b) == EQ) == (a == b)
  , runDuel 1000 $ lawDuel (nom ++ " : compatibilité — α ≺ β ⟹ α+γ ≺ β+γ")
      (genTriple3) (shrinkTriple shrinkComps) $
      \(a, b, c) ->
        compare (wrap a) (wrap b)
          == compare (wrap (zipWith (+) a c)) (wrap (zipWith (+) b c))
  , runDuel 1000 $ lawDuel (nom ++ " : zéro minimal — 0 ⪯ α")
      (genComps 3) shrinkComps $
      \a -> wrap (replicate 3 0) <= wrap a
  ]
  where
    genPair3   = (,)  <$> genComps 3 <*> genComps 3
    genTriple3 = (,,) <$> genComps 3 <*> genComps 3 <*> genComps 3

-- À k = 1 : l'unicité du Théorème 1, témoignée — les trois ordres
-- coïncident avec l'ordre usuel de ℕ.
unicityK1
  :: (Ord o, Show o)
  => String -> ([Natural] -> o) -> IO Verdict
unicityK1 nom wrap =
  runDuel 1000 $ Duel
    { duelName  = nom ++ " : k = 1 — coïncide avec ≤"
    , generator = (,) <$> genComp <*> genComp
    , shrinker  = shrinkPair shrink
    , candidate = \(a, b) -> compare (wrap [a]) (wrap [b])
    , referee   = pureReferee "ordre usuel de ℕ (à la main)"
                    (\(a, b) -> compare a b)
    }

-- L'arithmétique de 'sup' (export additif du vert de la série 4 : le
-- coin commun de Spol). Jugé comme borne du treillis de 'divides' :
-- majorant, minimal parmi les multiples communs — et la
-- caractérisation qui le pince : α∨β = β ⟺ α | β.
supDuels :: [IO Verdict]
supDuels =
  [ runDuel 1000 $ lawDuel "sup : majorant — α | α∨β et β | α∨β"
      genPairE (shrinkPair shrink) $
      \(a, b) -> a `divides` sup a b && b `divides` sup a b
  , runDuel 1000 $ lawDuel
      "sup : minimal — α | δ et β | δ ⟹ α∨β | δ"
      genTripleE (shrinkTriple shrink) $
      \(a, b, d) ->
        not (a `divides` d && b `divides` d) || sup a b `divides` d
  , runDuel 1000 $ lawDuel "sup : absorption — α∨β = β ⟺ α | β"
      genPairE (shrinkPair shrink) $
      \(a, b) -> (sup a b == b) == (a `divides` b)
  ]
  where
    genPairE   = (,) <$> arbitrary <*> arbitrary
                   :: Gen (Exp 3, Exp 3)
    genTripleE = (,,) <$> arbitrary <*> arbitrary <*> arbitrary
                   :: Gen (Exp 3, Exp 3, Exp 3)

-- Les témoins de séparation du tableau de ② — des cas exhibés, pas des
-- tirages : la séparation est une existence.
temoin
  :: (Ord o, Show o)
  => String -> ([Natural] -> o) -> [Natural] -> [Natural] -> Ordering
  -> IO Verdict
temoin nom wrap a b attendu =
  runDuel 1 $ Duel
    { duelName  = nom
    , generator = pure ()
    , shrinker  = const []
    , candidate = \() -> compare (wrap a) (wrap b)
    , referee   = pureReferee "témoin de ② (à la main)" (const attendu)
    }

-- ---------------------------------------------------------------------

lex3 :: [Natural] -> Lex 3
lex3 = Lex . expo

grlex3 :: [Natural] -> GrLex 3
grlex3 = GrLex . expo

grevlex3 :: [Natural] -> GrevLex 3
grevlex3 = GrevLex . expo

main :: IO ()
main = do
  ok <- runSuite $
    -- ② admissibilité, trois clauses × trois ordres
       admissibility "lex"     lex3
    ++ admissibility "grlex"   grlex3
    ++ admissibility "grevlex" grevlex3
    -- ② unicité sur ℕ, témoignée par coïncidence
    ++ [ unicityK1 "lex"     (Lex     . expo :: [Natural] -> Lex 1)
       , unicityK1 "grlex"   (GrLex   . expo :: [Natural] -> GrLex 1)
       , unicityK1 "grevlex" (GrevLex . expo :: [Natural] -> GrevLex 1)
       ]
    -- contrat Haskell des instances (batteries quickcheck-classes-base)
    ++ contrat "lex"     (Proxy :: Proxy (Lex 3))
    ++ contrat "grlex"   (Proxy :: Proxy (GrLex 3))
    ++ contrat "grevlex" (Proxy :: Proxy (GrevLex 3))
    -- l'arithmétique de sup (export additif du vert de la série 4)
    ++ supDuels
    -- ② témoins de séparation (les couples du tableau)
    ++ [ temoin "lex : x ≻ y² à k = 2"
           (Lex . expo :: [Natural] -> Lex 2) [1,0] [0,2] GT
       , temoin "grlex : y² ≻ x à k = 2 — sépare lex des gradués"
           (GrLex . expo :: [Natural] -> GrLex 2) [1,0] [0,2] LT
       , temoin "grlex : x²yz ≻ xy³ à k = 3"
           grlex3 [2,1,1] [1,3,0] GT
       , temoin "grevlex : xy³ ≻ x²yz à k = 3 — sépare grlex de grevlex"
           grevlex3 [2,1,1] [1,3,0] LT
       ]
  unless ok exitFailure
  putStrLn "ORDRES (②) : all green"
