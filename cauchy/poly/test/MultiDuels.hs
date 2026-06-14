-- | Le rouge de la phase 3, côté algèbre : les lignes CONTRAT de ①③
-- (et la tête de ②) en duels exécutables. Chaque duel doit échouer
-- tant que le squelette de Data.Cauchy.Multi dit @error "à
-- implémenter"@ — c'est le constat recherché.
--
-- ① lois de S[x₁,x₂,x₃] ×3 (ℚ, 𝔽₇, Trop) ; produit plat ≡ produit
--   itéré via S[ℕ²] ≅ S[ℕ][ℕ] (référent : l'univarié du volet 1,
--   vert) ; évaluation morphisme ; évaluation partielle ≡ itération.
-- ② lm et lc multiplicatifs sur ℚ ; contre-exemple constaté ℤ/6ℤ.
-- ③ invariant de division (×3 ordres, QuickCheck pur) ;
--   non-canonicité constatée (témoin xy², transposer la liste) ;
--   certificats croisés contre Singular division (duel certifiant —
--   le verdict réifié de cauchy-oracle) ; défaut des restes jugé par
--   le référent seul (reduce(r − r′, std(G)) = 0) ; égalité stricte
--   là où elle est bien posée : singleton, fixture cyclic-3 (base
--   calculée par le référent, jamais par nous).
--
-- Les duels Singular sont gardés par CAUCHY_ORACLE_SINGULAR (sinon SKIP
-- explicite) ; les cas sont groupés par script — un processus pour N
-- cas, le duel par lots de cauchy-oracle (la note datée 2026-06-12
-- « grouper pour 10⁴ » est remboursée). Trop est répliqué du rouge de
-- la phase 2 (propriétaire Hackage à trancher, note datée
-- 2026-06-12) ; katsura-3 attend une source vérifiée (id.).
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Control.Monad (unless)
import Data.Ratio ((%))
import Numeric.Natural (Natural)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)

import Test.Cauchy.Oracle (BatchDuel (..), Duel (..), Referee (..),
                           Verdict (..), chunked, lawDuel, pureReferee,
                           runBatchDuel, runDuel, runSuite)
import Test.QuickCheck

import Data.Mod (Mod)
import Data.Monoid (Sum (..))
import Data.Semiring (Semiring (..))
import Data.Semiring.Tropical (Extrema (..), Tropical (..))

import qualified Data.Cauchy.Poly as P
import Data.Cauchy.Multi
import Data.Cauchy.Order

import MultiShowcase (exemple)
import SingularRef

-- ---------------------------------------------------------------------
-- Générateurs : des descriptions finies, jamais des porteurs.

genQ :: Gen Rational
genQ = (%) <$> choose (-6, 6) <*> choose (1, 4)

genM7 :: Gen (Mod 7)
genM7 = fromInteger <$> choose (0, 6)

-- Trop = (ℕ ∪ {∞}, min, +) : c'est @Tropical 'Minima (Sum Natural)@
-- de semirings — la porte tranchée au vert du volet 2
-- (2026-06-12) ; la réplique du rouge, remboursée.
genT :: Gen (Tropical 'Minima (Sum Natural))
genT = frequency
  [ (1, pure Infinity)
  , (4, Tropical . Sum . fromIntegral <$> chooseInt (0, 9))
  ]

genExps :: Int -> Gen [Natural]
genExps k = vectorOf k (fromIntegral <$> chooseInt (0, 3))

genDesc :: Int -> Gen s -> Gen [([Natural], s)]
genDesc k g = do
  n <- chooseInt (0, 5)
  vectorOf n ((,) <$> genExps k <*> g)

-- Une description ℚ non nulle après normalisation (diviseurs, têtes).
genDescQ1 :: Int -> Gen TermL
genDescQ1 k =
  (normalizeT <$> genDesc k (genQ `suchThat` (/= 0)))
    `suchThat` (not . null)

shrinkDesc :: [([Natural], s)] -> [[([Natural], s)]]
shrinkDesc = shrinkList (const [])

-- Rétrécissement en valeur, pour les descriptions ℚ : supprimer des
-- termes, mais aussi réduire chaque exposant composante par composante
-- et chaque coefficient — le contre-exemple converge vers le monôme
-- frontière au lieu de garder des degrés et des rationnels arbitraires.
shrinkTermQ :: ([Natural], Rational) -> [([Natural], Rational)]
shrinkTermQ (es, c) =
     [ (es', c) | es' <- shrinkComps es ]
  ++ [ (es, c') | c' <- shrink c, c' /= 0 ]
  where
    shrinkComps ns =
      [ take i ns ++ [n'] ++ drop (i + 1) ns
      | (i, n) <- zip [0 :: Int ..] ns
      , n' <- shrink n
      ]

shrinkDescQ :: TermL -> [TermL]
shrinkDescQ = shrinkList shrinkTermQ

-- Variante gardée pour les positions de diviseur : jamais nulle après
-- normalisation — la tête doit exister.
shrinkDescQ1 :: TermL -> [TermL]
shrinkDescQ1 = filter (not . null . normalizeT) . shrinkDescQ

shrinkPair :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair sa sb (a, b) = [(a', b) | a' <- sa a] ++ [(a, b') | b' <- sb b]

shrinkTriple :: (a -> [a]) -> (b -> [b]) -> (c -> [c]) -> (a, b, c)
             -> [(a, b, c)]
shrinkTriple sa sb sc (a, b, c) =
     [(a', b, c) | a' <- sa a]
  ++ [(a, b', c) | b' <- sb b]
  ++ [(a, b, c') | c' <- sc c]

-- ---------------------------------------------------------------------
-- Des descriptions aux porteurs (candidat) et aux observations.

mk :: (MonomialOrder o, Semiring s, Eq s)
   => ([Natural] -> o) -> [([Natural], s)] -> MPoly o s
mk wrap = fromTerms . map (\(es, c) -> (wrap es, c))

obsTerms :: MonomialOrder o => MPoly o s -> [([Natural], s)]
obsTerms = map (\(o, c) -> (components (toExp o), c)) . toTerms

obsLead :: MonomialOrder o => MPoly o s -> Maybe ([Natural], s)
obsLead = fmap (\(o, c) -> (components (toExp o), c)) . leading

lex2 :: [Natural] -> Lex 2
lex2 = Lex . expo

lex3 :: [Natural] -> Lex 3
lex3 = Lex . expo

-- ---------------------------------------------------------------------
-- Référents à la main, depuis les descriptions.

handEval :: TermL -> [Rational] -> Rational
handEval ts pt =
  sum [ c * product (zipWith pw pt es) | (es, c) <- ts ]
  where
    pw a e = a ^ e

handLex :: [Natural] -> [Natural] -> Ordering
handLex a b = compare a b   -- l'ordre des listes EST lex à arité égale

handLead :: TermL -> ([Natural], Rational)
handLead ts = last (sortOnFst (normalizeT ts))
  where
    sortOnFst = foldr ins []
    ins t [] = [t]
    ins t@(e, _) (u@(f, _) : us)
      | handLex e f == GT = u : ins t us
      | otherwise         = t : u : us

handDivisible :: [Natural] -> [Natural] -> Bool
handDivisible d e = and (zipWith (<=) d e)

handReduced :: [TermL] -> TermL -> Bool
handReduced ds r =
  and [ not (handDivisible (fst (handLead d)) e) | (e, _) <- r, d <- ds ]

-- L'univarié itéré, construit à la main depuis une description k = 2
-- (x intérieur, y extérieur) — le référent vert du volet 1.
handIter :: TermL -> P.Poly (P.Poly Rational)
handIter ts = P.fromCoeffs
  [ P.fromCoeffs [ coefAt i j | i <- [0 .. maxX] ] | j <- [0 .. maxY] ]
  where
    nts = normalizeT ts
    maxX = maximum (0 : [ i | ([i, _], _) <- nts ])
    maxY = maximum (0 : [ j | ([_, j], _) <- nts ])
    coefAt i j = sum [ c | ([i', j'], c) <- nts, i' == i, j' == j ]

obsIter :: P.Poly (P.Poly Rational) -> [[Rational]]
obsIter = map P.toCoeffs . P.toCoeffs

-- ---------------------------------------------------------------------
-- ① les lois (huit : les sept du noyau, plus la commutativité de ∗ —
-- la cellule fusionnée du micro-cas de ①).

mpolyLaws :: forall s. (Semiring s, Eq s, Show s)
          => String -> Gen s -> [IO Verdict]
mpolyLaws nom g =
  [ law2 "plus-assoc" (\p q r -> (p `plus` q) `plus` r == p `plus` (q `plus` r))
  , law1 "plus-comm"  (\p q -> p `plus` q == q `plus` p)
  , law0 "plus-zero"  (\p -> p `plus` zero == p)
  , law2 "times-assoc" (\p q r -> (p `times` q) `times` r == p `times` (q `times` r))
  , law0 "times-one"  (\p -> p `times` one == p && one `times` p == p)
  , law1 "times-comm" (\p q -> p `times` q == q `times` p)
  , law2 "distrib"    (\p q r -> p `times` (q `plus` r) == (p `times` q) `plus` (p `times` r))
  , law0 "times-zero" (\p -> p `times` zero == zero)
  ]
  where
    build :: [([Natural], s)] -> MPoly (Lex 3) s
    build = mk lex3
    gD = genDesc 3 g
    law0 n prop = runDuel 300 $ lawDuel ("S[x₁,x₂,x₃] " ++ nom ++ " : " ++ n)
      gD shrinkDesc (prop . build)
    law1 n prop = runDuel 300 $ lawDuel ("S[x₁,x₂,x₃] " ++ nom ++ " : " ++ n)
      ((,) <$> gD <*> gD) (shrinkPair shrinkDesc shrinkDesc)
      (\(a, b) -> prop (build a) (build b))
    law2 n prop = runDuel 200 $ lawDuel ("S[x₁,x₂,x₃] " ++ nom ++ " : " ++ n)
      ((,,) <$> gD <*> gD <*> gD)
      (shrinkTriple shrinkDesc shrinkDesc shrinkDesc)
      (\(a, b, c) -> prop (build a) (build b) (build c))

-- ---------------------------------------------------------------------
-- ① plat ≡ itéré, évaluation.

duelIter :: Duel (TermL, TermL) [[Rational]]
duelIter = Duel
  { duelName  = "produit plat ≡ produit itéré (S[ℕ²] ≅ S[ℕ][ℕ])"
  , generator = (,) <$> genDesc 2 genQ <*> genDesc 2 genQ
  , shrinker  = shrinkPair shrinkDescQ shrinkDescQ
  , candidate = \(ts, us) ->
      obsIter (iterate2 (mk lex2 ts `times` mk lex2 us
                           :: MPoly (Lex 2) Rational))
  , referee   = pureReferee "univarié itéré (volet 1, vert)"
      (\(ts, us) -> obsIter (handIter ts `times` handIter us))
  }

duelEvalMorphism :: Duel (TermL, TermL, [Rational]) Rational
duelEvalMorphism = Duel
  { duelName  = "évaluation : ev (p ∗ q) = ev p · ev q (morphisme)"
  , generator = (,,) <$> genDesc 3 genQ <*> genDesc 3 genQ
                     <*> vectorOf 3 genQ
  , shrinker  = shrinkTriple shrinkDescQ shrinkDescQ (const [])
  , candidate = \(ts, us, pt) ->
      evalAt pt (mk lex3 ts `times` mk lex3 us :: MPoly (Lex 3) Rational)
  , referee   = pureReferee "somme directe (à la main)"
      (\(ts, us, pt) -> handEval ts pt * handEval us pt)
  }

duelEvalIter :: Duel (TermL, Rational, Rational) Rational
duelEvalIter = Duel
  { duelName  = "évaluation partielle ≡ itération (y, puis x)"
  , generator = (,,) <$> genDesc 2 genQ <*> genQ <*> genQ
  , shrinker  = \(ts, a, b) -> [ (ts', a, b) | ts' <- shrinkDescQ ts ]
  , candidate = \(ts, a, b) ->
      evalAt [a, b] (mk lex2 ts :: MPoly (Lex 2) Rational)
  , referee   = pureReferee "univarié itéré, évalué en deux temps (volet 1, vert)"
      (\(ts, a, b) ->
         P.eval (P.eval (handIter ts) (P.fromCoeffs [b])) a)
  }

-- ---------------------------------------------------------------------
-- ② la tête multiplicative, et son contre-exemple.

duelLead :: Duel (TermL, TermL) (Maybe ([Natural], Rational))
duelLead = Duel
  { duelName  = "lm(p∗q) = lm(p)+lm(q), lc(p∗q) = lc(p)·lc(q) — S = ℚ, intègre"
  , generator = (,) <$> genDescQ1 2 <*> genDescQ1 2
  , shrinker  = shrinkPair shrinkDescQ1 shrinkDescQ1
  , candidate = \(ts, us) ->
      obsLead (mk lex2 ts `times` mk lex2 us :: MPoly (Lex 2) Rational)
  , referee   = pureReferee "têtes à la main"
      (\(ts, us) ->
         let (e, c) = handLead ts
             (f, d) = handLead us
         in Just (zipWith (+) e f, c * d))
  }

duelLeadZ6 :: Duel () (Maybe ([Natural], Mod 6))
duelLeadZ6 = Duel
  { duelName  = "contre-exemple ℤ/6ℤ : (2x+1)(3y+1) — la tête prédite s'évanouit"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() ->
      obsLead ((mk lex2 [([1, 0], 2), ([0, 0], 1)]
                  `times` mk lex2 [([0, 1], 3), ([0, 0], 1)])
                 :: MPoly (Lex 2) (Mod 6))
  , referee   = pureReferee "produit développé à la main"
      (const (Just ([1, 0], 2)))
  }

-- ---------------------------------------------------------------------
-- ③ l'invariant (pur), la non-canonicité (témoin).

-- SNIPPET:multi-invariant
checkInvariant
  :: forall o. (MonomialOrder o)
  => ([Natural] -> o) -> (TermL, [TermL]) -> Bool
checkInvariant wrap (pT, dTs) =
  let p  = mk wrap pT  :: MPoly o Rational
      ds = map (mk wrap) dTs
      (qs, r) = division p ds
      recompose = foldr plus zero (zipWith times qs ds) `plus` r
      -- La réduction se juge le long de l'ordre du duel : lm(dᵢ) est
      -- la tête DANS cet ordre (pas handReduced, dont la tête est
      -- lex) ; la divisibilité, elle, ne dépend pas de l'ordre.
      reduced = and
        [ not (toExp e `divides` toExp f)
        | d <- ds
        , Just (e, _) <- [leading d]
        , (f, _) <- toTerms r
        ]
      headBound = and
        [ maybe True (\(e, _) -> maybe False (\(f, _) -> e <= f)
            (leading p)) (leading (q `times` d))
        | (q, d) <- zip qs ds
        ]
  in p == recompose
       && reduced
       && headBound
-- END:multi-invariant

genDivInput :: Gen (TermL, [TermL])
genDivInput = do
  p  <- normalizeT <$> genDesc 3 genQ
  n  <- chooseInt (1, 3)
  ds <- vectorOf n (genDescQ1 3)
  pure (p, ds)

invariantDuel
  :: (MonomialOrder o)
  => String -> ([Natural] -> o) -> IO Verdict
invariantDuel nom wrap =
  runDuel 300 $ lawDuel
    ("invariant de division (" ++ nom ++ ") : p = Σ qᵢ∗dᵢ + r, r réduit, têtes bornées")
    genDivInput
    (shrinkPair shrinkDescQ (shrinkList shrinkDescQ1))
    (checkInvariant wrap)

-- La vitrine (④ §1) : l'exemple déroulé à la main dans ③, exécuté par
-- la bibliothèque — le snippet affiché est jugé ici.
duelShowcase :: Duel () ([TermL], TermL)
duelShowcase = Duel
  { duelName  = "vitrine : l'exemple de ③ — (q₁, q₂, r) = (x + y, 1, x + y + 1)"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() ->
      let (qs, r) = exemple
      in (map (normalizeT . obsTerms) qs, normalizeT (obsTerms r))
  , referee   = pureReferee "déroulé à la main de ③"
      (const ( [ [([0, 1], 1), ([1, 0], 1)], [([0, 0], 1)] ]
             , [([0, 0], 1), ([0, 1], 1), ([1, 0], 1)] ))
  }

duelTwoRemainders :: Duel () (TermL, TermL)
duelTwoRemainders = Duel
  { duelName  = "non-canonicité : xy² par (xy−1, y²−1) puis (y²−1, xy−1) — deux restes"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() ->
      let p  = mk lex2 [([1, 2], 1)] :: MPoly (Lex 2) Rational
          d1 = mk lex2 [([1, 1], 1), ([0, 0], -1)]
          d2 = mk lex2 [([0, 2], 1), ([0, 0], -1)]
          remBy ds = normalizeT (obsTerms (snd (division p ds)))
      in (remBy [d1, d2], remBy [d2, d1])
  , referee   = pureReferee "témoin de ③ (à la main)"
      (const ([([0, 1], 1)], [([1, 0], 1)]))
  }

-- ---------------------------------------------------------------------
-- ③ les duels Singular (gardés par CAUCHY_ORACLE_SINGULAR).

-- Le système des diviseurs est tiré, pas figé : têtes non moniques et
-- coefficients fractionnaires atteignent le référent. Licite parce que
-- le duel certifiant et le défaut jugé par reduce·std sont bien posés
-- pour TOUT G — seule l'égalité stricte des restes ne l'est pas.
genCross :: Gen (TermL, [TermL])
genCross = do
  p  <- normalizeT <$> genDesc 2 genQ
  n  <- chooseInt (2, 3)
  ds <- vectorOf n (genDescQ1 2)
  pure (p, ds)

-- SNIPPET:multi-cert-cross
-- Certificats croisés, en lot : la question au référent est réifiée
-- (l'entrée elle-même), le juge est pur — il vérifie le certificat du
-- référent par NOTRE arithmétique, puis le nôtre symétriquement. Les
-- N cas partent vers Singular en un seul script.
duelCertCross :: BatchDuel (TermL, [TermL]) ([TermL], TermL)
                           (TermL, [TermL]) ([TermL], TermL, TermL)
duelCertCross = BatchDuel
  { batchName      = "certificats croisés : division(p, G) de Singular, vérifiée par notre arithmétique"
  , batchGenerator = genCross
  , batchShrinker  = \(p, ds) ->
         [ (p', ds) | p' <- shrinkDescQ p ]
      ++ [ (p, ds') | ds' <- shrinkList shrinkDescQ1 ds, not (null ds') ]
  , batchCandidate = \(pT, dTs) ->
      let (qs, r) = division (mk lex2 pT :: MPoly (Lex 2) Rational)
                             (map (mk lex2) dTs)
      in (map (normalizeT . obsTerms) qs, normalizeT (obsTerms r))
  , batchQueries   = \i _ -> [i]
  , batchJudge     = \(pT, dTs) ours certs -> do
      (qsRef, rRef, u) <- seul certs
      let rebuild qs r =
            foldr plus zero
              (zipWith times (map (mk lex2) qs)
                             (map (mk lex2) dTs))
              `plus` mk lex2 r
              :: MPoly (Lex 2) Rational
          pC = mk lex2 pT
      unless' (u == [(replicate 2 0, 1)] || u == [([0, 0], 1)])
        ("unité inattendue du référent : " ++ show u)
      unless' (pC == rebuild qsRef rRef)
        "l'équation du référent ne se vérifie pas par notre arithmétique"
      unless' (handReduced dTs rRef)
        "le reste du référent n'est pas réduit"
      let (qsC, rC) = ours
      unless' (pC == rebuild qsC rC)
        "notre équation ne se vérifie pas"
      unless' (handReduced dTs rC)
        "notre reste n'est pas réduit"
  }
-- END:multi-cert-cross

unless' :: Bool -> String -> Either String ()
unless' True  _   = Right ()
unless' False why = Left why

-- | L'unique réponse d'un cas à une question — tout autre compte est
-- une panne du transport, dite telle quelle.
seul :: [c] -> Either String c
seul [c] = Right c
seul cs  = Left (show (length cs) ++ " réponses pour une question")

-- Le défaut des restes, jugé par le référent seul : pré-vol sain
-- (reduce(0) = 0), puis reduce(r − r′, std(G)) = 0. Deux questions
-- par cas — la seconde dépend de la sortie du candidat.
duelDefect :: BatchDuel (TermL, [TermL]) (TermL, TermL) (TermL, [TermL]) TermL
duelDefect = BatchDuel
  { batchName      = "défaut des restes : reduce(r − r′, std(G)) = 0 chez le référent"
  , batchGenerator = genCross
  , batchShrinker  = \(p, ds) ->
         [ (p', ds) | p' <- shrinkDescQ p ]
      ++ [ (p, ds') | ds' <- shrinkList shrinkDescQ1 ds, not (null ds') ]
  , batchCandidate = \(pT, dTs) ->
      let p = mk lex2 pT :: MPoly (Lex 2) Rational
          ds = map (mk lex2) dTs
          remBy l = normalizeT (obsTerms (snd (division p l)))
      in (remBy ds, remBy (reverse ds))
  , batchQueries   = \(_, dTs) (r1, r2) -> [([], dTs), (subT r1 r2, dTs)]
  , batchJudge     = \_ _ rs -> case rs of
      [preflight, z]
        | preflight /= [] ->
            Left "pré-vol : reduce(0, std(G)) ≠ 0 — référent malade"
        | null z    -> Right ()
        | otherwise -> Left ("le défaut ne réduit pas à zéro : " ++ show z)
      _ -> Left (show (length rs) ++ " réponses pour deux questions")
  }

-- SNIPPET:multi-singleton
-- L'égalité stricte, là où elle est bien posée — le cas dégénéré du
-- duel par lots : une question, le juge est l'égalité.
duelSingleton :: BatchDuel (TermL, TermL) TermL (TermL, [TermL]) TermL
duelSingleton = BatchDuel
  { batchName      = "singular reduce·std / singleton : notre reste ≡ reduce(p, std(⟨d⟩)) — canonique (Proposition 2)"
  , batchGenerator = (,) <$> (normalizeT <$> genDesc 2 genQ) <*> genDescQ1 2
  , batchShrinker  = shrinkPair shrinkDescQ shrinkDescQ1
  , batchCandidate = \(pT, dT) ->
      normalizeT (obsTerms (snd (division
        (mk lex2 pT :: MPoly (Lex 2) Rational) [mk lex2 dT])))
  , batchQueries   = \(pT, dT) _ -> [(pT, [dT])]
  , batchJudge     = \_ mine rs -> do
      attendu <- seul rs
      unless' (mine == attendu)
        ("referent : " ++ show attendu ++ " — candidat : " ++ show mine)
  }
-- END:multi-singleton

cyclic3 :: [TermL]
cyclic3 =
  [ [([1, 0, 0], 1), ([0, 1, 0], 1), ([0, 0, 1], 1)]
  , [([1, 1, 0], 1), ([0, 1, 1], 1), ([1, 0, 1], 1)]
  , [([1, 1, 1], 1), ([0, 0, 0], -1)]
  ]

duelFixture :: [TermL] -> BatchDuel TermL TermL (TermL, [TermL]) TermL
duelFixture gb = BatchDuel
  { batchName      = "singular reduce·std (cyclic-3) / fixture cyclic-3 : division par la base du référent ≡ reduce"
  , batchGenerator = normalizeT <$> genDesc 3 genQ
  , batchShrinker  = shrinkDescQ
  , batchCandidate = \pT ->
      normalizeT (obsTerms (snd (division
        (mk lex3 pT :: MPoly (Lex 3) Rational) (map (mk lex3) gb))))
  , batchQueries   = \pT _ -> [(pT, cyclic3)]
  , batchJudge     = \_ mine rs -> do
      attendu <- seul rs
      unless' (mine == attendu)
        ("referent : " ++ show attendu ++ " — candidat : " ++ show mine)
  }

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  gate <- lookupEnv "CAUCHY_ORACLE_SINGULAR"
  singularDuels <- case gate of
    Nothing -> pure
      [ pure (Verdict True
          "SKIP singular / certificats, défaut, singleton, fixture (CAUCHY_ORACLE_SINGULAR non défini)"
          Nothing)
      ]
    Just _ -> do
      -- La fixture : la base est calculée par le référent, jamais par
      -- nous (anti-hallucination — katsura-3 attend une source
      -- vérifiée, note datée 2026-06-12).
      gb <- refCall (stdRef 3) cyclic3
      pure
        [ runBatchDuel nSingular (parLots (divisionRefN 2))  duelCertCross
        , runBatchDuel nSingular (parLots (reduceStdRefN 2)) duelDefect
        , runBatchDuel nSingular (parLots (reduceStdRefN 2)) duelSingleton
        , runBatchDuel nSingular (parLots (reduceStdRefN 3)) (duelFixture gb)
        ]
  ok <- runSuite $
    -- ① lois ×3 instances
       mpolyLaws "ℚ" genQ
    ++ mpolyLaws "𝔽₇" genM7
    ++ mpolyLaws "Trop" genT
    -- ① plat ≡ itéré, évaluation
    ++ [ runDuel 1000 duelIter
       , runDuel 1000 duelEvalMorphism
       , runDuel 1000 duelEvalIter
       ]
    -- ② tête multiplicative, contre-exemple
    ++ [ runDuel 1000 duelLead
       , runDuel 1    duelLeadZ6
       ]
    -- ③ invariant ×3 ordres, non-canonicité
    ++ [ invariantDuel "lex"     (Lex     . expo :: [Natural] -> Lex 3)
       , invariantDuel "grlex"   (GrLex   . expo :: [Natural] -> GrLex 3)
       , invariantDuel "grevlex" (GrevLex . expo :: [Natural] -> GrevLex 3)
       , runDuel 1 duelTwoRemainders
       , runDuel 1 duelShowcase
       ]
    -- ③ le référent Singular
    ++ singularDuels
  unless ok exitFailure
  putStrLn "MULTIVARIÉ (①③) : all green"
  where
    -- Les cas groupés par script : un processus Singular pour 500 cas
    -- (~11 ms le lancement contre ~0,3 ms le cas groupé, mesure du
    -- 2026-06-12) — le volume des différentiels antérieurs devient
    -- praticable, la note datée « grouper pour 10⁴ » est remboursée.
    parLots = chunked 500
    nSingular = 1000
