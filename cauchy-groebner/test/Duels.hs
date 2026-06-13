-- | Le rouge de la phase 4 : les quatorze lignes CONTRAT de
-- plan-groebner.md (§oracle) en duels exécutables. Chaque duel doit
-- échouer tant que le squelette de Data.Cauchy.Groebner dit @error "à
-- implémenter"@ — c'est le constat recherché.
--
-- ① reste invariant par permutation sur les bases réduites du
--   référent et cohérence singleton avec la division de la série 3 ;
--   appartenance dans les deux sens, croisée ; le défaut localisé du
--   témoin xy² (r′ − r ∈ I, réduit, tête hors ⟨lm G⟩).
-- ② S-paires des bases réduites du référent → 0 ; le contre-exemple
--   de ① (une S-paire à reste non nul, la tête manquante exhibée) ;
--   lois du S-polynôme ×3 ordres (annulation, antisymétrie, premier
--   critère).
-- ③ la sortie de buchberger passe le critère ; l'idéal inchangé (sens
--   pur et sens croisé) ; le duel décisif — base réduite contre
--   std·redSB, ensemble contre ensemble, familles aléatoires et
--   cyclic-4..6\/katsura-3..5 générées par le référent ; idempotence.
-- ④ coupe lex ≡ eliminate ; appartenance à la projection dans les
--   deux sens ; témoin de séparation grevlex ; remontée close par
--   notre arithmétique.
--
-- Les duels Singular sont gardés par CAUCHY_ORACLE_SINGULAR (sinon SKIP
-- explicite) et passent d'emblée par l'oracle par lots (PR #64 :
-- 'BatchDuel' — la question au référent réifiée, le juge pur, les N
-- cas en un script via @chunked 500@) : le volume du duel décisif est
-- praticable dès le rouge. Générateurs et rétrécisseurs répliqués de
-- MultiDuels (dette connue des phases 1–3, datée 2026-06-12 —
-- remboursement quand le harnais les possédera).
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Control.Monad (unless)
import Data.List (sortOn, tails)
import Data.Proxy (Proxy (..))
import Data.Ratio ((%))
import GHC.TypeLits (KnownNat, natVal)
import Numeric.Natural (Natural)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)

import Test.Cauchy.Oracle (BatchDuel (..), CertDuel (..), Duel (..),
                           Referee (..), Verdict (..), chunked, lawDuel,
                           onSingleton, pureReferee, runBatchDuel,
                           runCertDuel, runDuel, runSuite)
import Test.QuickCheck

import Data.Semiring (Semiring (..))

import Data.Cauchy.Groebner
import Data.Cauchy.Multi (MPoly, division, evalAt, fromTerms, leading,
                          toTerms)
import Data.Cauchy.Order (GrLex (..), GrevLex (..), Lex (..),
                          MonomialOrder (..), components, divides, expo)

import SingularGroebner
import Showcase (arcReduite, cubiqueCutGrevlex, cubiqueCutLex)

-- ---------------------------------------------------------------------
-- Générateurs : des descriptions finies, jamais des porteurs.

genQ :: Gen Rational
genQ = (%) <$> choose (-6, 6) <*> choose (1, 4)

genExps :: Int -> Gen [Natural]
genExps k = vectorOf k (fromIntegral <$> chooseInt (0, 3))

genDesc :: Int -> Gen TermL
genDesc k = do
  n <- chooseInt (0, 5)
  vectorOf n ((,) <$> genExps k <*> genQ)

genDescQ1 :: Int -> Gen TermL
genDescQ1 k =
  (normalizeT <$> genDesc k) `suchThat` (not . null)

-- Familles de générateurs petites (degrés ≤ 2, 1 à 3 générateurs) :
-- l'entrée de buchberger — chaque cas coûte une complétion entière au
-- vert, et chez le référent une base standard.
genTermS :: Int -> Gen ([Natural], Rational)
genTermS k = (,) <$> vectorOf k (fromIntegral <$> chooseInt (0, 2))
                 <*> (genQ `suchThat` (/= 0))

genDescS :: Int -> Gen TermL
genDescS k =
  (normalizeT <$> (chooseInt (1, 3) >>= \n -> vectorOf n (genTermS k)))
    `suchThat` (not . null)

genF :: Int -> Gen [TermL]
genF k = chooseInt (1, 3) >>= \m -> vectorOf m (genDescS k)

-- Familles bornées aux exposants multilinéaires (0..1) pour le ④ lex à
-- 3 indéterminées — NON parce que le degré 2 serait invalide, mais
-- parce que les bases de Gröbner lex de systèmes aléatoires de degré 2
-- ont une queue rare (mesuré <1/1000, tirée par les 1000 cas réels) à
-- coefficients géants, dont le coût bottom-out dans des @ccall unsafe@
-- vers gmp — non interruptibles même sous -threaded, donc
-- CAUCHY_ORACLE_DUEL_TIMEOUT ne peut pas la borner (cf. Oracle.hs, 3ᵉ angle
-- mort). Le bord vit côté entrée, pas côté garde. Mesuré le 2026-06-13 :
-- 40 000 cas multilinéaires, pire cas 2 ms — la queue disparaît. Le
-- degré ≥ 2 reste couvert : déterministiquement par 'cutGoldDuel'
-- (cubique tordue, degré 3) et 'sepDuel', et en largeur aléatoire par
-- 'cutRandom2Duel' (degré 2, 2 indéterminées, où le lex est tractable).
genElimFamille :: Gen [TermL]
genElimFamille = vectorOf 2 desc
  where
    desc = (normalizeT <$> (chooseInt (1, 3) >>= \n -> vectorOf n terme))
             `suchThat` (not . null)
    terme = (,) <$> vectorOf 3 (fromIntegral <$> chooseInt (0, 1))
                <*> (genQ `suchThat` (/= 0))

-- Rétrécissement en valeur (réplique de MultiDuels, dette datée).
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

shrinkDescQ1 :: TermL -> [TermL]
shrinkDescQ1 = filter (not . null . normalizeT) . shrinkDescQ

shrinkF :: [TermL] -> [[TermL]]
shrinkF = filter (not . null) . shrinkList shrinkDescQ1

shrinkPair :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair sa sb (a, b) = [(a', b) | a' <- sa a] ++ [(a, b') | b' <- sb b]

unless' :: Bool -> String -> Either String ()
unless' True  _   = Right ()
unless' False why = Left why

-- | L'unique réponse d'un cas à une question — tout autre compte est
-- une panne du transport, dite telle quelle.
seul :: [c] -> Either String c
seul [c] = Right c
seul cs  = Left (show (length cs) ++ " réponses pour une question")

-- ---------------------------------------------------------------------
-- Des descriptions aux porteurs (candidat) et aux observations.

mk :: MonomialOrder o => ([Natural] -> o) -> TermL -> MPoly o Rational
mk wrap = fromTerms . map (\(es, c) -> (wrap es, c))

obsP :: MonomialOrder o => MPoly o Rational -> TermL
obsP = normalizeT . map (\(o, c) -> (components (toExp o), c)) . toTerms

-- | Tête nue d'un polynôme non nul.
headExp :: MonomialOrder o => MPoly o Rational -> [Natural]
headExp = maybe [] (components . toExp . fst) . leading

-- | lm(p) ∈ ⟨lm G⟩ : un des coins divise — la lecture de l'escalier.
inLmIdeal :: MonomialOrder o => [MPoly o Rational] -> o -> Bool
inLmIdeal gs m =
  or [ toExp e `divides` toExp m | g <- gs, Just (e, _) <- [leading g] ]

-- | Normalisation ensemble contre ensemble du duel décisif : lc = 1
-- (l'arithmétique verte de la série 3), tri par têtes — le
-- @normalizeT@ du niveau des bases.
normalSet :: MonomialOrder o => [MPoly o Rational] -> [TermL]
normalSet =
  map obsP . sortOn (fmap fst . leading) . map monic . filter (/= zero)
  where
    monic p = case leading p of
      Nothing      -> p
      Just (_, lc) -> fromTerms [ (m, c / lc) | (m, c) <- toTerms p ]

lex2 :: [Natural] -> Lex 2
lex2 = Lex . expo

grl2 :: [Natural] -> GrLex 2
grl2 = GrLex . expo

grv2 :: [Natural] -> GrevLex 2
grv2 = GrevLex . expo

lex3 :: [Natural] -> Lex 3
lex3 = Lex . expo

grl3 :: [Natural] -> GrLex 3
grl3 = GrLex . expo

grv3 :: [Natural] -> GrevLex 3
grv3 = GrevLex . expo

-- ---------------------------------------------------------------------
-- Les témoins d'or (vérifiés contre Singular, notes du 2026-06-12 ;
-- ce sont ceux des pages ①–④).

-- xy − 1, y² − 1, et d₃ = x − y = Spol(d₁, d₂) — le fil des pages.
d1T, d2T, d3T, pXY2 :: TermL
d1T  = [([1, 1], 1), ([0, 0], -1)]
d2T  = [([0, 2], 1), ([0, 0], -1)]
d3T  = [([1, 0], 1), ([0, 1], -1)]
pXY2 = [([1, 2], 1)]

-- La cubique tordue de ④ : x² − y, x³ − z ; le témoin y³ − z².
goldF3 :: [TermL]
goldF3 = [ [([2, 0, 0], 1), ([0, 1, 0], -1)]
         , [([3, 0, 0], 1), ([0, 0, 1], -1)] ]

wT :: TermL
wT = [([0, 3, 0], 1), ([0, 0, 2], -1)]

-- ---------------------------------------------------------------------
-- ① la canonicité retrouvée.

-- Ligne 1 (part pure) : sur un singleton — toujours une base de
-- Gröbner (série 3, Proposition 2) — nf coïncide avec le reste de la
-- division de la série 3, verte.
singletonDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
singletonDuel nom wrap = runDuel 300 $ Duel
  { duelName  = "① singleton (" ++ nom
                  ++ ") : nf p [d] ≡ le reste de la division de la série 3"
  , generator = (,) <$> (normalizeT <$> genDesc 2) <*> genDescQ1 2
  , shrinker  = shrinkPair shrinkDescQ shrinkDescQ1
  , candidate = \(pT, dT) -> obsP (nf (mk wrap pT) [mk wrap dT])
  , referee   = pureReferee "division de la série 3 (verte)"
      (\(pT, dT) -> obsP (snd (division (mk wrap pT) [mk wrap dT])))
  }

-- Ligne 1 (fixture référent) : sur la base réduite de katsura-3 —
-- calculée par le référent, jamais par nous — le reste est invariant
-- par permutation de la liste : la non-canonicité des ordres, éteinte.
permDuel :: MonomialOrder o
         => String -> ([Natural] -> o) -> [TermL] -> IO Verdict
permDuel nom wrap gT =
  runDuel 200 $ lawDuel
    ("① reste invariant par permutation (" ++ nom
       ++ ", katsura-3 redSB du référent)")
    ((,) <$> (normalizeT <$> genDesc 3) <*> shuffle [0 .. length gT - 1])
    (\(p, pm) -> [ (p', pm) | p' <- shrinkDescQ p ])
    (\(pT, pm) ->
       let g = map (mk wrap) gT
           p = mk wrap pT
       in obsP (nf p (map (g !!) pm)) == obsP (nf p g))

-- Ligne 2, sens direct : p = Σ aᵢ gᵢ tiré au hasard ⇒ NF(p, G) = 0.
memberConstructDuel :: [TermL] -> IO Verdict
memberConstructDuel gT =
  runDuel 100 $ lawDuel
    "① appartenance, sens direct : p = Σ aᵢ gᵢ ⇒ NF(p, G) = 0 (katsura-3, lex)"
    (vectorOf (length gT) (genDesc 3))
    (shrinkList shrinkDescQ)
    (\aTs ->
       let g = map (mk lex3) gT
           p = foldr plus zero (zipWith times (map (mk lex3) aTs) g)
       in member p g)

-- Ligne 2, croisée : NF(p, G) = 0 ⟺ reduce(p, std(G)) = 0 chez le
-- référent — le protocole certifiant de la série 3, la question
-- réifiée pour partir en lot.
memberIffDuel :: [TermL] -> BatchDuel TermL Bool (TermL, [TermL]) TermL
memberIffDuel gT = BatchDuel
  { batchName      = "① appartenance croisée : member ⟺ reduce(p, std(G)) = 0 (katsura-3, lex)"
  , batchGenerator = normalizeT <$> genDesc 3
  , batchShrinker  = shrinkDescQ
  , batchCandidate = \pT -> member (mk lex3 pT) (map (mk lex3) gT)
  , batchQueries   = \pT _ -> [(pT, gT)]
  , batchJudge     = \_ ours rs -> do
      r <- seul rs
      unless' (ours == null r)
        ("désaccord : member = " ++ show ours
           ++ ", référent reduce = " ++ show r)
  }

-- Ligne 3 : le défaut localisé. Sur le témoin xy² et la liste
-- transposée, le défaut r′ − r est non nul, réduit modulo G, sa tête
-- est hors ⟨lm G⟩ (constats purs), et il appartient à I — jugé par le
-- référent (reduce(r′ − r, std(G)) = 0, pré-vol sain d'abord ; la
-- seconde question dépend de la sortie du candidat).
defectDuel :: BatchDuel () (TermL, Bool) (TermL, [TermL]) TermL
defectDuel = BatchDuel
  { batchName      = "① défaut localisé : r′ − r ∈ I, réduit modulo G, tête hors ⟨lm G⟩ (témoin xy²)"
  , batchGenerator = pure ()
  , batchShrinker  = const []
  , batchCandidate = \() ->
      let g1 = mk lex2 d1T
          g2 = mk lex2 d2T
          p  = mk lex2 pXY2
          rD = nf p [g1, g2]
          rT = nf p [g2, g1]
          dT = normalizeT (obsP rT ++ map (fmap negate) (obsP rD))
          dP = mk lex2 dT
          ok = obsP rT /= []
                 && dT /= []
                 && obsP (nf dP [g1, g2]) == dT
                 && maybe False (not . inLmIdeal [g1, g2] . fst) (leading dP)
      in (dT, ok)
  , batchQueries   = \() (dT, _) -> [([], [d1T, d2T]), (dT, [d1T, d2T])]
  , batchJudge     = \() (_, ok) rs -> case rs of
      [preflight, z]
        | preflight /= [] ->
            Left "pré-vol : reduce(0, std(G)) ≠ 0 — référent malade"
        | not ok ->
            Left "les constats purs échouent (défaut nul, non réduit, ou tête couverte)"
        | null z    -> Right ()
        | otherwise ->
            Left ("le défaut ne réduit pas à 0 chez le référent : " ++ show z)
      _ -> Left (show (length rs) ++ " réponses pour deux questions")
  }

-- ---------------------------------------------------------------------
-- ② le S-polynôme.

-- Lignes 4 et 5 sur le témoin (pur) : la liste nue échoue au critère
-- — la S-paire laisse le reste x − y, dont la tête exhibe le trou —,
-- la liste complétée par d₃ le passe.
witnessCritDuel :: Duel () (TermL, Bool, Bool, Bool)
witnessCritDuel = Duel
  { duelName  = "② critère sur le témoin : (d₁,d₂) échoue — reste x − y, tête hors ⟨lm G⟩ —, (d₁,d₂,d₃) passe"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() ->
      let g1 = mk lex2 d1T
          g2 = mk lex2 d2T
          g3 = mk lex2 d3T
          r  = nf (spol g1 g2) [g1, g2]
          trou = maybe False (not . inLmIdeal [g1, g2] . fst) (leading r)
      in (obsP r, trou, isGroebner [g1, g2], isGroebner [g1, g2, g3])
  , referee   = pureReferee
      "déroulé à la main de ② (Spol(d₁,d₂) = x − y, vérifié contre Singular)"
      (const (normalizeT d3T, True, False, True))
  }

-- Ligne 4 (fixture référent) : sur la base réduite du référent,
-- toutes les S-paires réduisent à 0 — le critère, sens base ⇒ paires.
spairsDuel :: MonomialOrder o
           => String -> ([Natural] -> o) -> [TermL] -> IO Verdict
spairsDuel nom wrap gT =
  runDuel 1 $ lawDuel
    ("② S-paires de la base réduite du référent → 0 (" ++ nom
       ++ ", katsura-3)")
    (pure ()) (const [])
    (\() ->
       let g = map (mk wrap) gT
       in length g >= 2
            && and [ nf (spol a b) g == zero
                   | (a : bs) <- tails g, b <- bs ])

-- Ligne 6, lois pures ×3 ordres.
cancelDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
cancelDuel nom wrap =
  runDuel 300 $ lawDuel
    ("② annulation (" ++ nom ++ ") : Spol(p, q) = 0 ou lm(Spol) ≺ α∨β")
    ((,) <$> genDescQ1 2 <*> genDescQ1 2)
    (shrinkPair shrinkDescQ1 shrinkDescQ1)
    (\(pT, qT) ->
       let p = mk wrap pT
           q = mk wrap qT
           s = spol p q
           gamma = wrap (zipWith max (headExp p) (headExp q))
       in s == zero || maybe False ((< gamma) . fst) (leading s))

antisymDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
antisymDuel nom wrap =
  runDuel 300 $ lawDuel
    ("② antisymétrie (" ++ nom ++ ") : Spol(p, q) + Spol(q, p) = 0")
    ((,) <$> genDescQ1 2 <*> genDescQ1 2)
    (shrinkPair shrinkDescQ1 shrinkDescQ1)
    (\(pT, qT) ->
       let p = mk wrap pT
           q = mk wrap qT
       in spol p q `plus` spol q p == zero)

firstCritDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
firstCritDuel nom wrap =
  runDuel 200 $ lawDuel
    ("② premier critère (" ++ nom
       ++ ") : têtes premières entre elles ⇒ Spol(p, q) →{p,q} 0")
    (((,) <$> genDescQ1 2 <*> genDescQ1 2) `suchThat` coprime)
    (filter coprime . shrinkPair shrinkDescQ1 shrinkDescQ1)
    (\(pT, qT) ->
       let p = mk wrap pT
           q = mk wrap qT
       in nf (spol p q) [p, q] == zero)
  where
    coprime (pT, qT) =
      and (zipWith (\a b -> a == 0 || b == 0)
             (headExp (mk wrap pT)) (headExp (mk wrap qT)))

-- Témoin à têtes égales (γ = α = β) : le coin trivial, jamais tiré par
-- les générateurs aléatoires. Spol(x² + 1, x² + y) hisse chaque tête
-- par le monôme constant 1 et annule x² ; le reste − y + 1 a sa tête
-- en y ≺ x² = γ.
spolTetesEgalesDuel :: Duel () (TermL, Bool)
spolTetesEgalesDuel = Duel
  { duelName  = "② têtes égales : Spol(x² + 1, x² + y) = − y + 1, tête ≺ α∨β = x²"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() ->
      let p = mk lex2 [([2, 0], 1), ([0, 0], 1)]
          q = mk lex2 [([2, 0], 1), ([0, 1], 1)]
          s = spol p q
      in (obsP s, maybe False ((< lex2 [2, 0]) . fst) (leading s))
  , referee   = pureReferee "constat d'or (coin trivial γ = α = β)"
      (const (normalizeT [([0, 1], -1), ([0, 0], 1)], True))
  }

-- ---------------------------------------------------------------------
-- ③ la complétion.

-- Ligne 7 : auto-jugement — la sortie passe le critère de ②.
autoDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
autoDuel nom wrap =
  runDuel 100 $ lawDuel
    ("③ auto-jugement (" ++ nom ++ ") : buchberger F passe le critère de ②")
    (genF 2) shrinkF
    (isGroebner . buchberger . map (mk wrap))

-- Ligne 8, sens pur : l'idéal n'a pas perdu de générateur.
unchangedPureDuel :: MonomialOrder o
                  => String -> ([Natural] -> o) -> IO Verdict
unchangedPureDuel nom wrap =
  runDuel 100 $ lawDuel
    ("③ idéal inchangé, sens pur (" ++ nom
       ++ ") : tout f ∈ F réduit à 0 modulo buchberger F")
    (genF 2) shrinkF
    (\fT ->
       let fs = map (mk wrap) fT
           b  = buchberger fs
       in all (\f -> nf f b == zero) fs)

-- Ligne 8, sens croisé : l'idéal n'a pas gagné de générateur — tout g
-- de buchberger F réduit à 0 modulo std(F) chez le référent. Les
-- questions dépendent de la sortie du candidat (une par générateur
-- produit), précédées du pré-vol.
crossDuel :: BatchDuel [TermL] [TermL] (TermL, [TermL]) TermL
crossDuel = BatchDuel
  { batchName      = "③ idéal inchangé, sens croisé : tout g de buchberger F réduit à 0 modulo std(F) du référent (lex)"
  , batchGenerator = genF 2
  , batchShrinker  = shrinkF
  , batchCandidate = map obsP . buchberger . map (mk lex2)
  , batchQueries   = \fT bT -> ([], fT) : [ (g, fT) | g <- bT ]
  , batchJudge     = \_ _ rs -> case rs of
      (preflight : zs)
        | preflight /= [] ->
            Left "pré-vol : reduce(0, std(F)) ≠ 0 — référent malade"
        | all null zs -> Right ()
        | otherwise ->
            Left ("un générateur de buchberger F ne réduit pas à 0 : "
                    ++ show (filter (not . null) zs))
      [] -> Left "aucune réponse du référent"
  }

-- Ligne 9, familles aléatoires : le duel décisif — LA base réduite,
-- ensemble contre ensemble après normalisation (lc = 1, tri par
-- têtes). Le cas dégénéré du duel par lots : une question, le juge
-- est l'égalité des ensembles normalisés.
decisiveDuel :: MonomialOrder o
             => String -> ([Natural] -> o)
             -> BatchDuel [TermL] [TermL] [TermL] [TermL]
decisiveDuel nom wrap = BatchDuel
  { batchName      = "③ duel décisif (" ++ nom
                       ++ ") : reduce (buchberger F) ≡ std·redSB du référent, ensemble contre ensemble"
  , batchGenerator = genF 2
  , batchShrinker  = shrinkF
  , batchCandidate = normalSet . reduce . buchberger . map (mk wrap)
  , batchQueries   = \fT _ -> [fT]
  , batchJudge     = \_ mine rs -> do
      sT <- seul rs
      let attendu = normalSet (map (mk wrap) sT)
      unless' (mine == attendu)
        ("referent : " ++ show attendu ++ " — candidat : " ++ show mine)
  }

-- Ligne 9, familles nommées : cyclic-4..6 et katsura-3..5, générées
-- et résolues par le référent (jamais retranscrites), grevlex.
-- Le refCall vit dans le juge — donc sous 'borne' (via runCertDuel →
-- runProperty), comme tout appel référent d'un duel nommé : la garde
-- CAUCHY_ORACLE_DUEL_TIMEOUT (avec -threaded) le couvre. La famille étant
-- générée ET résolue par le référent, le candidat dépend de sa sortie
-- (fT) ; le juge fait tout le travail, le candidat est trivial.
-- SNIPPET:groebner-famille
-- NOTE:familyRef: la famille est générée ET résolue par le référent à l'exécution, jamais retranscrite — une base écrite à la main serait une erreur partagée entre le test et son juge
-- NOTE:normalSet: ensemble contre ensemble — la base réduite est canonique à ordre fixé, donc la coïncidence des deux ensembles est, elle, bien posée (là où le reste ne l'était pas)
familleDuel :: forall k. KnownNat k => Proxy k -> String -> IO Verdict
familleDuel pk name =
  runCertDuel 1 $ CertDuel
    { certName      = "③ duel décisif : " ++ name ++ "-" ++ show n
                        ++ " (grevlex), ensemble contre ensemble"
    , certGenerator = pure ()
    , certShrinker  = const []
    , certCandidate = const ()
    , certJudge     = \() () -> do
        (fT, sT) <- refCall (familyRef name n "dp") ()
        let mine    = normalSet (reduce (buchberger (map (mk wrap) fT)))
            attendu = normalSet (map (mk wrap) sT)
        pure $ unless' (mine == attendu)
          ("référent : " ++ show attendu ++ " — candidat : " ++ show mine)
    }
  where
    n = fromIntegral (natVal pk) :: Int
    wrap = GrevLex . expo :: [Natural] -> GrevLex k
-- END:groebner-famille

-- Ligne 10 : la base réduite est un point fixe de buchberger ∘ reduce
-- — l'unicité de ③, témoignée par l'exécutable.
idemDuel :: IO Verdict
idemDuel =
  runDuel 100 $ lawDuel
    "③ idempotence : la base réduite est un point fixe de buchberger ∘ reduce (lex)"
    (genF 2) shrinkF
    (\fT ->
       let b = reduce (buchberger (map (mk lex2) fT))
       in normalSet (buchberger (reduce b)) == normalSet b)

-- La forme RÉDUITE, sans référent : aucun terme d'un générateur n'est
-- divisible par la tête d'un autre (minimalité des têtes + queues
-- réduites — Théorème 3 de ③). Le duel décisif gardé épingle l'égalité
-- à std·redSB, mais hors CAUCHY_ORACLE_SINGULAR autoDuel ne contrôle
-- qu'isGroebner, satisfait par toute base de Gröbner même non réduite :
-- ce duel pur ferme le trou.
reduiteDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
reduiteDuel nom wrap =
  runDuel 100 $ lawDuel
    ("③ forme réduite (" ++ nom
       ++ ") : aucun terme d'un générateur divisible par la tête d'un autre")
    (genF 2) shrinkF
    (\fT ->
       let b   = reduce (buchberger (map (mk wrap) fT))
           idx = zip [0 :: Int ..] b
       in and [ not (inLmIdeal autres m)
              | (i, g) <- idx
              , let autres = [ h | (j, h) <- idx, j /= i ]
              , (m, _) <- toTerms g ])

-- ---------------------------------------------------------------------
-- ④ l'élimination.

-- Ligne 11, aléatoire : la coupe de la base lex contre eliminate du
-- référent, ensemble réduit contre ensemble réduit.
cutRandomDuel :: BatchDuel [TermL] [TermL] [TermL] [TermL]
cutRandomDuel = BatchDuel
  { batchName      = "④ coupe lex ≡ eliminate du référent (familles aléatoires multilinéaires, 3 indéterminées)"
  , batchGenerator = genElimFamille
  , batchShrinker  = shrinkF
  , batchCandidate = normalSet . cut 1 . reduce . buchberger . map (mk lex3)
  , batchQueries   = \fT _ -> [fT]
  , batchJudge     = \_ mine rs -> do
      eT <- seul rs
      let attendu = normalSet (map (mk lex3) eT)
      unless' (mine == attendu)
        ("referent : " ++ show attendu ++ " — candidat : " ++ show mine)
  }

-- Ligne 11, largeur de degré 2 : le bord multilinéaire du ④ à 3
-- indéterminées retire la largeur aléatoire de degré ≥ 2 ; on la
-- regagne ici où le lex est tractable — degré 2 plein (exposants 0..2),
-- 2 indéterminées (le lex à 2 variables borne l'explosion : 'decisiveDuel'
-- tourne 'reduce . buchberger' lex-2 à 1000 cas sans queue). cut 1
-- élimine x, garde ℚ[y] ; comparé à eliminate du référent.
cutRandom2Duel :: BatchDuel [TermL] [TermL] [TermL] [TermL]
cutRandom2Duel = BatchDuel
  { batchName      = "④ coupe lex ≡ eliminate du référent (familles aléatoires de degré 2, 2 indéterminées)"
  , batchGenerator = genF 2
  , batchShrinker  = shrinkF
  , batchCandidate = normalSet . cut 1 . reduce . buchberger . map (mk lex2)
  , batchQueries   = \fT _ -> [fT]
  , batchJudge     = \_ mine rs -> do
      eT <- seul rs
      let attendu = normalSet (map (mk lex2) eT)
      unless' (mine == attendu)
        ("referent : " ++ show attendu ++ " — candidat : " ++ show mine)
  }

-- Ligne 11, témoin d'or : la cubique tordue — la coupe vaut ⟨y³ − z²⟩
-- des deux côtés.
cutGoldDuel :: [TermL] -> Duel () [TermL]
cutGoldDuel eT = Duel
  { duelName  = "④ coupe d'or : ⟨x² − y, x³ − z⟩ ∩ ℚ[y,z] = ⟨y³ − z²⟩, des deux côtés"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> normalSet (cut 1 (reduce (buchberger (map (mk lex3) goldF3))))
  , referee   = pureReferee "singular eliminate (préchargé)"
      (const (normalSet (map (mk lex3) eT)))
  }

-- Ligne 12 : appartenance à la projection, dans les deux sens — pour
-- q sans x, NF(q, coupe) = 0 ⟺ reduce(q, std(I₁)) = 0 chez le
-- référent (I₁ préchargé chez lui).
projMemberDuel :: [TermL] -> BatchDuel TermL Bool (TermL, [TermL]) TermL
projMemberDuel eT = BatchDuel
  { batchName      = "④ appartenance à la projection : NF(q, coupe) = 0 ⟺ reduce(q, std(I₁)) = 0 (q sans x)"
  , batchGenerator = normalizeT . map (\(es, c) -> (0 : es, c)) <$> genDesc 2
  , batchShrinker  = shrinkDescQ
  , batchCandidate = \qT ->
      member (mk lex3 qT) (cut 1 (reduce (buchberger (map (mk lex3) goldF3))))
  , batchQueries   = \qT _ -> [(qT, eT)]
  , batchJudge     = \_ ours rs -> do
      r <- seul rs
      unless' (ours == null r)
        ("désaccord : member = " ++ show ours
           ++ ", référent reduce = " ++ show r)
  }

-- Ligne 13 : le témoin de séparation — la coupe grevlex de la cubique
-- tordue est vide alors que I₁ ne l'est pas (y³ − z² ∈ I, sans x) :
-- couper une base grevlex ne projette pas.
sepDuel :: Duel () ([TermL], Bool)
sepDuel = Duel
  { duelName  = "④ témoin de séparation : la coupe grevlex de ⟨x² − y, x³ − z⟩ est vide, mais y³ − z² ∈ I₁"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() ->
      let b = reduce (buchberger (map (mk grv3) goldF3))
      in (map obsP (cut 1 b), member (mk grv3 wT) b)
  , referee   = pureReferee
      "constat d'or (base grevlex vérifiée contre Singular, note du 2026-06-12)"
      (const ([], True))
  }

-- Ligne 14 : la remontée — les racines lues sur la base lex
-- triangulée de ⟨xy − 1, y² − 1⟩, substituées par l'évaluation du
-- multivarié (①, verte), annulent les générateurs : vérification
-- close par notre seule arithmétique.
remonteeDuel :: Duel () (Bool, Bool, Bool)
remonteeDuel = Duel
  { duelName  = "④ remontée : les racines de la base lex triangulée de ⟨xy − 1, y² − 1⟩ annulent F"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() ->
      let f1 = mk lex2 d1T
          f2 = mk lex2 d2T
          b  = reduce (buchberger [f1, f2])
          -- La triangulation attendue : x − y (le lien), y² − 1
          -- (l'univarié de la coupe) — vérifiée avant de lire les
          -- racines y = ±1, x = y.
          lien = normalizeT d3T `elem` map obsP b
          quad = map obsP (cut 1 b) == [normalizeT d2T]
          racines = [(1, 1), (-1, -1)] :: [(Rational, Rational)]
          annule = and [ evalAt [a, c] g == 0
                       | (a, c) <- racines, g <- [f1, f2] ]
      in (lien, quad, annule)
  , referee   = pureReferee "constat d'or (la remontée close par notre arithmétique)"
      (const (True, True, True))
  }

-- Les bords de la coupe, jamais joués (l'oracle gardé ne coupe qu'à
-- j = 1) : cut 0 garde tout (identité — @take 0@ ne contraint aucune
-- composante) ; cut k à k = arité ne retient que les constantes (tête
-- d'exposant nul), car un terme ne survit que si ses k composantes sont
-- nulles.
cutBordsDuel :: IO Verdict
cutBordsDuel =
  runDuel 100 $ lawDuel
    "④ coupe aux bords : cut 0 = identité ; cut (arité) ne garde que des constantes"
    (genF 2) shrinkF
    (\fT ->
       let b = reduce (buchberger (map (mk lex2) fT))
       in normalSet (cut 0 b) == normalSet b
            && all ((== [0, 0]) . headExp) (cut (2 :: Int) b))

-- ---------------------------------------------------------------------
-- Vitrine : les deux calculs d'or des pages ⑤⑥, jugés purs contre leur
-- déroulé à la main — les valeurs affichées sont celles que GHC produit,
-- pas des littéraux. (Les croisements contre Singular — base réduite
-- contre std·redSB, coupe contre eliminate — sont déjà tenus par les
-- duels décisifs et 'cutGoldDuel'.)

-- L'arc des ordres : reduce(buchberger ⟨xy−1, y²−1⟩) = {y²−1, x−y}, le
-- d₃ = x − y = Spol(d₁,d₂) du fil.
vitrineArcDuel :: Duel () [TermL]
vitrineArcDuel = Duel
  { duelName  = "vitrine : reduce(buchberger ⟨xy − 1, y² − 1⟩) = {y² − 1, x − y} (le fil de l'arc, x ≻ y)"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> normalSet arcReduite
  , referee   = pureReferee "déroulé à la main : d₃ = x − y = Spol(d₁, d₂)"
      (const (normalSet (map (mk lex2) [d2T, d3T])))
  }

-- La cubique tordue : coupe lex = {y³ − z²}, coupe grevlex = ∅ (la fuite
-- y² − xz). Le témoin de séparation de ④, exécuté.
vitrineCutDuel :: Duel () ([TermL], [TermL])
vitrineCutDuel = Duel
  { duelName  = "vitrine : coupe lex ⟨x² − y, x³ − z⟩ ∩ ℚ[y,z] = {y³ − z²}, coupe grevlex vide"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> (normalSet cubiqueCutLex, normalSet cubiqueCutGrevlex)
  , referee   = pureReferee "déroulé à la main : y³ − z² (lex), ∅ (grevlex)"
      (const (normalSet [mk lex3 wT], []))
  }

-- ---------------------------------------------------------------------
-- Plomberie : témoin de -threaded.

-- -threaded n'est exercé par aucun duel mathématique (tous ont un
-- référent rapide, la garde n'a jamais à mordre) ; un retrait silencieux
-- du flag (refactor du .cabal) ne ferait rougir personne, et la
-- régression serait un blocage muet — le mode d'échec qu'on prétend
-- clore. Ce témoin vise le seul cas que -threaded ferme : 'timeout' doit
-- interrompre un appel étranger /sûr/ bloqué (un sous-processus). Sous
-- -threaded l'exception est livrée et @sleep@ est coupé à ~2 s (vert) ;
-- sans le flag, 'timeout' ne mord pas, @sleep@ rend la main à 10 s et le
-- témoin rougit. (Un sous-processus, pas un 'threadDelay' — qui serait
-- interruptible même non fileté : on testerait le mauvais angle mort.)
threadedTemoin :: IO Verdict
threadedTemoin = do
  r <- timeout (2 * 1000000) (readProcessWithExitCode "sleep" ["10"] "")
  pure $ case r of
    Nothing -> Verdict True
      "OK   plomberie : -threaded — timeout interrompt un sous-processus FFI bloqué (sleep coupé à 2 s)"
      Nothing
    Just _  -> Verdict False
      "FAIL plomberie : timeout n'a pas coupé sleep — RTS non fileté (-threaded retiré ?)"
      Nothing

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  gate <- lookupEnv "CAUCHY_ORACLE_SINGULAR"
  gated <- case gate of
    Nothing -> pure
      [ pure (Verdict True
          "SKIP singular / fixtures ①②, appartenances croisées, défaut, duels décisifs, familles, élimination (CAUCHY_ORACLE_SINGULAR non défini)"
          Nothing)
      ]
    Just _ -> do
      -- Les fixtures ①② : katsura-3 en base réduite, un ordre = un
      -- ring — la base est calculée par le référent, jamais par nous
      -- (anti-hallucination, précédent de la phase 3).
      (_, kLp) <- refCall (familyRef "katsura" 3 "lp") ()
      (_, kDp) <- refCall (familyRef "katsura" 3 "Dp") ()
      (_, kdp) <- refCall (familyRef "katsura" 3 "dp") ()
      -- La base de I₁ du témoin de ④, chez le référent — l'unitaire
      -- est le lot à un élément.
      eGold <- refCall (onSingleton (eliminateRefN 3 "lp" 1)) goldF3
      pure $
        -- ① fixtures et appartenances
        [ permDuel "lex"     lex3 kLp
        , permDuel "grlex"   grl3 kDp
        , permDuel "grevlex" grv3 kdp
        , memberConstructDuel kLp
        , runBatchDuel nSingular (parLots (reduceStdRefN 3 "lp"))
            (memberIffDuel kLp)
        , runBatchDuel 1 (parLots (reduceStdRefN 2 "lp")) defectDuel
        -- ② fixtures
        , spairsDuel "lex"     lex3 kLp
        , spairsDuel "grlex"   grl3 kDp
        , spairsDuel "grevlex" grv3 kdp
        -- ③ croisé et duels décisifs
        , runBatchDuel nSingular (parLots (reduceStdRefN 2 "lp")) crossDuel
        , runBatchDuel nSingular (parLots (stdRedSBRefN 2 "lp"))
            (decisiveDuel "lex" lex2)
        , runBatchDuel nSingular (parLots (stdRedSBRefN 2 "dp"))
            (decisiveDuel "grevlex" grv2)
        , familleDuel (Proxy :: Proxy 4) "cyclic"
        , familleDuel (Proxy :: Proxy 5) "cyclic"
        , familleDuel (Proxy :: Proxy 6) "cyclic"
        , familleDuel (Proxy :: Proxy 3) "katsura"
        , familleDuel (Proxy :: Proxy 4) "katsura"
        , familleDuel (Proxy :: Proxy 5) "katsura"
        -- ④ élimination
        , runBatchDuel nSingular (parLots (eliminateRefN 3 "lp" 1))
            cutRandomDuel
        , runBatchDuel nSingular (parLots (eliminateRefN 2 "lp" 1))
            cutRandom2Duel
        , runDuel 1 (cutGoldDuel eGold)
        , runBatchDuel nSingular (parLots (reduceStdRefN 3 "lp"))
            (projMemberDuel eGold)
        ]
  ok <- runSuite $
    -- ⓪ plomberie (pur) : le flag RTS qu'aucun duel n'exerce
       [ threadedTemoin ]
    -- ① la canonicité retrouvée (pur)
    ++ [ singletonDuel "lex" lex2
       , singletonDuel "grlex" grl2
       , singletonDuel "grevlex" grv2
       ]
    -- ② le S-polynôme (pur)
    ++ [ runDuel 1 witnessCritDuel ]
    ++ [ cancelDuel "lex" lex2, cancelDuel "grlex" grl2
       , cancelDuel "grevlex" grv2
       ]
    ++ [ antisymDuel "lex" lex2, antisymDuel "grlex" grl2
       , antisymDuel "grevlex" grv2
       ]
    ++ [ firstCritDuel "lex" lex2, firstCritDuel "grlex" grl2
       , firstCritDuel "grevlex" grv2
       ]
    ++ [ runDuel 1 spolTetesEgalesDuel ]
    -- ③ la complétion (pur)
    ++ [ autoDuel "lex" lex2, autoDuel "grlex" grl2
       , autoDuel "grevlex" grv2
       ]
    ++ [ unchangedPureDuel "lex" lex2, unchangedPureDuel "grlex" grl2
       , unchangedPureDuel "grevlex" grv2
       ]
    ++ [ reduiteDuel "lex" lex2, reduiteDuel "grlex" grl2
       , reduiteDuel "grevlex" grv2
       ]
    ++ [ idemDuel ]
    -- ④ l'élimination (pur)
    ++ [ runDuel 1 sepDuel, runDuel 1 remonteeDuel, cutBordsDuel ]
    -- ⑤⑥ vitrine : les calculs d'or des pages, jugés purs (pur)
    ++ [ runDuel 1 vitrineArcDuel, runDuel 1 vitrineCutDuel ]
    -- les duels Singular (gardés)
    ++ gated
  unless ok exitFailure
  putStrLn "GROEBNER (①–④) : all green"
  where
    -- Les cas groupés par script : un processus Singular pour 500 cas
    -- (mesure de la phase 3, 2026-06-12 : ~11 ms le lancement contre
    -- ~0,3 ms le cas groupé) — le volume exigé par le duel décisif est
    -- praticable dès le rouge.
    parLots = chunked 500
    nSingular = 1000
