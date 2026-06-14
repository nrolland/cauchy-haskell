-- | Auto-test du harnais, et fumée Singular.
--
-- 1. Un duel honnête doit passer.
-- 2. Un duel saboté doit échouer, et rétrécir jusqu'au plus petit
--    contre-exemple — un harnais qui ne sait pas échouer ne prouve rien.
-- 3. Le lot : mêmes preuves pour le duel par lots — honnête, saboté et
--    rétréci, candidat qui lève (le rouge ne doit pas emporter la
--    suite) ; le redécoupage sur marqueurs exercé contre un vrai
--    processus (@cat@) ; 'chunked' et 'onSingleton' recollent sans
--    perte.
-- 4. Fumée Singular (le chemin critique de la phase 4, dérisqué sans une
--    ligne de Gröbner) : un reduce trivial, activé par CAUCHY_ORACLE_SINGULAR=1 ;
--    sinon SKIP explicite — jamais silencieux.
-- 5. Le vocabulaire Singular ('Test.Cauchy.Singular', export additif
--    du remboursement de la réplique render\/parse) : analyse et anneau
--    en pur, aller-retour d'un lot à travers l'outil sous le même
--    portail CAUCHY_ORACLE_SINGULAR.
module Main (main) where

import Data.Char (isSpace)
import Data.List (isInfixOf)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.Exit (exitFailure, exitSuccess)
import Test.Cauchy.Oracle
import Test.Cauchy.Singular
import Test.QuickCheck (Gen, arbitrary, shrink)

main :: IO ()
main = do
  honest <- runDuel 200 Duel
    { duelName  = "x + x = 2x"
    , generator = arbitrary :: Gen Int
    , shrinker  = shrink
    , candidate = \i -> i * 2
    , referee   = pureReferee "harnais" (\i -> i + i)
    }
  putStrLn (vLine honest)

  sabotage <- runDuel 200 Duel
    { duelName  = "sabotage"
    , generator = arbitrary :: Gen Int
    , shrinker  = shrink
    , candidate = (+ 1)
    , referee   = pureReferee "harnais" id
    }
  let detected = not (vPassed sabotage)
      -- failingTestCase porte l'entrée rétrécie puis le texte de l'écart ;
      -- seule la première nous intéresse ici.
      shrunk   = (take 1 <$> vMinimal sabotage) == Just ["0"]
  putStrLn $ (if detected then "OK   " else "FAIL ")
          ++ "harnais / le sabotage est détecté"
  putStrLn $ (if shrunk then "OK   " else "FAIL ")
          ++ "harnais / le contre-exemple rétrécit jusqu'à 0"

  lot <- batchSmoke
  garde <- gardeFouSmoke
  absent <- absentRefSmoke
  vocab <- vocabSmoke
  singular <- singularSmoke
  putStrLn (vLine singular)
  retour <- singularVocabSmoke
  putStrLn (vLine retour)

  if vPassed honest && detected && shrunk && lot && garde && absent && vocab
       && vPassed singular && vPassed retour
    then exitSuccess
    else exitFailure

-- ---------------------------------------------------------------------
-- Le garde-fou CAUCHY_ORACLE_DUEL_TIMEOUT : un duel qui boucle doit revenir
-- rouge « dépassement » — nommé — au lieu d'emporter la suite.

gardeFouSmoke :: IO Bool
gardeFouSmoke = do
  setEnv "CAUCHY_ORACLE_DUEL_TIMEOUT" "1"
  -- La victime doit ALLOUER : une exception asynchrone n'est délivrée
  -- qu'aux points d'allocation — « length (repeat ()) » noue un cycle
  -- d'une cellule et tourne sans allouer, inarrêtable. La somme sur
  -- [Integer] alloue à chaque pas, donc s'interrompt.
  v <- runDuel 1 Duel
    { duelName  = "boucle sans fin"
    , generator = pure ()
    , shrinker  = const []
    , candidate = \() -> fromInteger (sum [1 ..]) :: Int
    , referee   = pureReferee "harnais" (const 0)
    }
  unsetEnv "CAUCHY_ORACLE_DUEL_TIMEOUT"
  let coupe = not (vPassed v) && "dépassement" `isInfixOf` vLine v
  putStrLn $ (if coupe then "OK   " else "FAIL ")
          ++ "harnais / garde-fou : le duel qui boucle revient rouge, nommé"

  -- Le filtre CAUCHY_ORACLE_MATCH : hors motif, un duel saboté n'est même pas
  -- exécuté — SKIP vert ; la boucle de travail peut lancer UN duel.
  setEnv "CAUCHY_ORACLE_MATCH" "motif-introuvable"
  s <- runDuel 1 Duel
    { duelName  = "sabotage hors motif"
    , generator = pure ()
    , shrinker  = const []
    , candidate = \() -> 1 :: Int
    , referee   = pureReferee "harnais" (const 0)
    }
  unsetEnv "CAUCHY_ORACLE_MATCH"
  let saute = vPassed s && "SKIP" `isInfixOf` vLine s
  putStrLn $ (if saute then "OK   " else "FAIL ")
          ++ "harnais / CAUCHY_ORACLE_MATCH : hors motif, le duel est sauté sans tourner"
  pure (coupe && saute)

-- ---------------------------------------------------------------------
-- Le référent absent : binaire introuvable ⇒ SKIP vert, pas échec dur.
-- Le pré-vol 'skipIfAbsent' saute le duel AVANT de lancer l'outil
-- fantôme ; un référent présent en désaccord reste rouge (le sabotage
-- ci-dessus en témoigne — la garde ne porte que sur l'absence).

absentRefSmoke :: IO Bool
absentRefSmoke = do
  v <- runDuel 1 Duel
    { duelName  = "référent absent"
    , generator = pure ()
    , shrinker  = const []
    , candidate = const ("0" :: String)
    , referee   = processReferee "outil fantôme"
                    ["cauchy-aucun-tel-binaire-xyz"] [] (const "") Right
    }
  let saute = vPassed v && "SKIP" `isInfixOf` vLine v
              && "référent absent" `isInfixOf` vLine v
  putStrLn $ (if saute then "OK   " else "FAIL ")
          ++ "harnais / référent absent : binaire introuvable ⇒ SKIP vert nommé"
  pure saute

-- ---------------------------------------------------------------------
-- Le duel par lots.

-- | Le duel d'égalité, en lot : une question (l'entrée), le juge est
-- l'égalité.
eqBatch :: (Show r, Eq r) => String -> (Int -> r) -> BatchDuel Int r Int r
eqBatch nom cand = BatchDuel
  { batchName      = nom
  , batchGenerator = arbitrary
  , batchShrinker  = shrink
  , batchCandidate = cand
  , batchQueries   = \i _ -> [i]
  , batchJudge     = \_ a cs -> case cs of
      [c] | c == a  -> Right ()
          | otherwise -> Left ("référent " ++ show c ++ " ≠ candidat " ++ show a)
      _ -> Left "nombre de réponses inattendu"
  }

doubleur :: Referee [Int] [Int]
doubleur = pureReferee "harnais (lot)" (map (\i -> i + i))

batchSmoke :: IO Bool
batchSmoke = do
  honest <- runBatchDuel 200 doubleur (eqBatch "lot : x + x = 2x" (* 2))
  putStrLn (vLine honest)

  sabotage <- runBatchDuel 200 doubleur (eqBatch "lot : sabotage" (\i -> i + i + 1))
  let detected = not (vPassed sabotage)
      shrunk   = (take 1 <$> vMinimal sabotage) == Just ["0"]
  putStrLn $ (if detected then "OK   " else "FAIL ")
          ++ "harnais / lot : le sabotage est détecté"
  putStrLn $ (if shrunk then "OK   " else "FAIL ")
          ++ "harnais / lot : le contre-exemple rétrécit jusqu'à 0"

  -- Le candidat d'un rouge : error. Le cas tombe, le lot survit.
  leve <- runBatchDuel 20 doubleur
            (eqBatch "lot : squelette" (\_ -> error "todo (rouge)"))
  let poisoned = not (vPassed leve)
  putStrLn $ (if poisoned then "OK   " else "FAIL ")
          ++ "harnais / lot : un candidat qui lève est un échec, pas une panne"

  -- chunked recolle dans l'ordre, onSingleton retrouve le cas seul.
  recolle <- refCall (chunked 3 doubleur) [1 .. 10]
  seul    <- refCall (onSingleton doubleur) 21
  let okChunk  = recolle == map (* 2) [1 .. 10 :: Int]
      okSingle = seul == (42 :: Int)
  putStrLn $ (if okChunk then "OK   " else "FAIL ")
          ++ "harnais / chunked ≡ le lot d'un coup"
  putStrLn $ (if okSingle then "OK   " else "FAIL ")
          ++ "harnais / onSingleton : le cas seul depuis le lot"

  -- Le redécoupage sur marqueurs, contre un vrai processus : cat
  -- renvoie le script tel quel, chaque tranche doit rendre son cas.
  echo <- refCall (processBatchReferee "cat" ["cat"] []
                     "" (++ "\n") (++ "\n") "" (Right . trim))
                  ["alpha", "beta", "gamma"]
  let okEcho = echo == ["alpha", "beta", "gamma"]
  putStrLn $ (if okEcho then "OK   " else "FAIL ")
          ++ "harnais / marqueurs : trois cas redécoupés à travers cat"

  pure (vPassed honest && detected && shrunk && poisoned
        && okChunk && okSingle && okEcho)
  where
    trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- | reduce(x² + x, std⟨x⟩) = 0 — le plus petit calcul que Singular sache
-- faire, suffisant pour prouver que le conteneur CI parle à l'outil.
singularSmoke :: IO Verdict
singularSmoke = do
  gate <- lookupEnv "CAUCHY_ORACLE_SINGULAR"
  case gate of
    Nothing -> pure (Verdict True
      "SKIP singular / fumée reduce (CAUCHY_ORACLE_SINGULAR non défini)" Nothing)
    Just _ -> runDuel 1 Duel
      { duelName  = "fumée reduce"
      , generator = pure ()
      , shrinker  = const []
      , candidate = const "0"
      , referee   = processReferee "singular" ["Singular", "singular"] ["-q"]
                      render parse
      }
  where
    render () = "ring r=0,(x,y),dp; poly p=x2+x; ideal I=x; reduce(p,std(I));exit;\n"
    parse out = case lines (trim out) of
      [v] -> Right (trim v)
      _   -> Left ("sortie inattendue : " ++ show out)
    trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- ---------------------------------------------------------------------
-- Le vocabulaire Singular (export additif ⇒ duel de fumée).

-- | La part pure du vocabulaire : notation courte, fraction, garde
-- d'arité à l'analyse, protocole d'idéaux, déclaration d'anneau.
vocabSmoke :: IO Bool
vocabSmoke = do
  let okCourt = parsePoly 2 "x2y-1" == Right [([0, 0], -1), ([2, 1], 1)]
      okFrac  = parsePoly 2 "-1/2x" == Right [([1, 0], -1 / 2)]
      okHors  = case parsePoly 2 "z" of
        Left m  -> "hors arité" `isInfixOf` m
        Right _ -> False
      okIdeal = parseIdealOnly 2 "2\nx+y\nxy2\n"
                  == Right [[([0, 1], 1), ([1, 0], 1)], [([1, 2], 1)]]
      okRing3 = ringOf 3 "lp" == "ring r=0,(x,y,z),lp;\n"
      okRing2 = ringOf 2 "dp" == "ring r=0,(x,y),dp;\n"
  dit okCourt "vocabulaire / parsePoly : notation courte x2y-1"
  dit okFrac  "vocabulaire / parsePoly : coefficient fractionnaire"
  dit okHors  "vocabulaire / parsePoly : indéterminée hors arité refusée"
  dit okIdeal "vocabulaire / parseIdealOnly : taille puis éléments"
  dit okRing3 "vocabulaire / ringOf 3 lp"
  dit okRing2 "vocabulaire / ringOf 2 dp"
  pure (okCourt && okFrac && okHors && okIdeal && okRing3 && okRing2)
  where
    dit ok nom = putStrLn ((if ok then "OK   " else "FAIL ") ++ nom)

-- | L'aller-retour du vocabulaire à travers l'outil : trois
-- descriptions rendues, imprimées, réanalysées en un seul lot — chaque
-- retour doit être la forme canonique de l'entrée. Même portail que la
-- fumée reduce, même SKIP explicite.
singularVocabSmoke :: IO Verdict
singularVocabSmoke = do
  gate <- lookupEnv "CAUCHY_ORACLE_SINGULAR"
  case gate of
    Nothing -> pure (Verdict True
      "SKIP singular / aller-retour du vocabulaire (CAUCHY_ORACLE_SINGULAR non défini)"
      Nothing)
    Just _ -> do
      retours <- refCall allerRetour entrees
      let ok = retours == map normalizeT entrees
      pure (Verdict ok
        ((if ok then "OK   " else "FAIL ")
           ++ "singular / aller-retour du vocabulaire ("
           ++ show (length entrees) ++ " cas)")
        Nothing)
  where
    entrees :: [TermL]
    entrees =
      [ [([1, 0], 1), ([0, 2], -1 / 2)]   -- une fraction
      , []                                -- la description vide → « 0 »
      , [([2, 1], 3), ([0, 0], 7)]
      ]
    allerRetour =
      singularBatch "singular vocabulaire" (ringOf 2 "dp") render1 parse1
    render1 q = "poly p=" ++ renderPoly 2 q ++ ";\np;\n"
    parse1 out = case cleanLines out of
      [l] -> parsePoly 2 l
      ls  -> Left ("tranche inattendue : " ++ show ls)
