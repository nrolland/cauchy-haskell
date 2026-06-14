-- | Harnais différentiel de la famille cauchy : un /candidat/ (la
-- bibliothèque jugée) contre un /référent/ extérieur, sur les mêmes
-- entrées aléatoires, égalité exigée.
--
-- Le mécanisme est unique pour toutes les phases — @poly@ (phase 1),
-- un moteur regex (phase 2), Singular\/Sage (phases 3–4) : génération,
-- appel du référent, comparaison, rétrécissement, rapport. Seule la
-- valeur 'Referee' change ; c'est le paramètre, pas un détail enfoui
-- dans un test monolithique.
module Test.Cauchy.Oracle
  ( -- * Le référent, réifié
    Referee(..)
  , pureReferee
  , processReferee
    -- * Le référent par lots (un processus pour N cas)
  , processBatchReferee
  , chunked
  , onSingleton
    -- * Le duel
  , Duel(..)
  , duelProperty
  , lawDuel
    -- * Le duel certifiant (le verdict, réifié)
  , CertDuel(..)
  , certProperty
  , runCertDuel
  , runCertDuelWith
    -- * Le duel par lots (la question au référent, réifiée)
  , BatchDuel(..)
  , runBatchDuel
    -- * Exécution et rapport
  , Verdict(..)
  , runDuel
  , runProperty
  , runSuite
  ) where

import Control.Concurrent (forkIO, killThread, threadDelay)
import Control.Exception (SomeException, evaluate, finally, try)
import Data.List (intercalate, isInfixOf)
import GHC.Clock (getMonotonicTime)
import System.Directory (findExecutable)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.IO (hFlush, hPutStrLn, stderr, stdout)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Test.QuickCheck
import Text.Printf (printf)
import Text.Read (readMaybe)

-- SNIPPET:oracle-referee
-- | Le référent : un nom (celui du rapport), les exécutables externes
-- qu'il requiert, et un appel. Un référent en bibliothèque (@poly@) est
-- pur — @refExes@ vide ; un outil externe (Singular) passe par un
-- processus — le type ne distingue pas l'appel, mais @refExes@ rend la
-- dépendance externe /inspectable/ : un coureur peut sauter en vert un
-- duel dont le binaire est absent, au lieu d'échouer en profondeur.
data Referee i r = Referee
  { refName :: String
  , refExes :: [String]   -- ^ exécutables candidats requis ; @[]@ = référent pur
  , refCall :: i -> IO r
  }

-- | Référent en bibliothèque : pur, aucun exécutable requis.
pureReferee :: String -> (i -> r) -> Referee i r
pureReferee n f = Referee n [] (pure . f)
-- END:oracle-referee

-- | Référent hors processus : rendre l'entrée en script, appeler l'outil,
-- analyser sa sortie. Le premier exécutable trouvé sert. Un code de
-- sortie non nul ou un échec d'analyse est une panne du harnais, pas un
-- contre-exemple : on échoue bruyamment au lieu de comparer du bruit.
processReferee
  :: String                       -- ^ nom du rapport
  -> [String]                     -- ^ noms d'exécutable candidats
  -> [String]                     -- ^ arguments
  -> (i -> String)                -- ^ entrée → stdin
  -> (String -> Either String r)  -- ^ stdout → résultat
  -> Referee i r
processReferee n exes args render parse = Referee n exes call
  where
    call i = do
      exe <- firstExecutable exes
      (code, out, err) <- readProcessWithExitCode exe args (render i)
      case code of
        ExitFailure c ->
          fail (n ++ " : code de sortie " ++ show c ++ " — " ++ err)
        ExitSuccess ->
          either (\m -> fail (n ++ " : analyse — " ++ m)) pure (parse out)

-- | Le premier des candidats présent sur le @PATH@, s'il y en a un.
firstAvailable :: [String] -> IO (Maybe FilePath)
firstAvailable []       = pure Nothing
firstAvailable (e : es) = findExecutable e >>= maybe (firstAvailable es) (pure . Just)

-- | Le premier exécutable présent ; échoue bruyamment si aucun. Le
-- pré-vol 'skipIfAbsent' des coureurs évite normalement d'atteindre ce
-- @fail@ — il reste comme filet pour un référent consulté hors coureur.
firstExecutable :: [String] -> IO FilePath
firstExecutable names =
  firstAvailable names >>=
    maybe (fail ("aucun exécutable parmi : " ++ intercalate ", " names)) pure

-- | Pré-vol d'un duel : si son référent exige des exécutables externes et
-- qu'aucun n'est sur le @PATH@, le duel rend un @SKIP@ vert nommé au lieu
-- d'échouer — un référent absent est une /information/, pas une panne
-- (troisième cas de la même règle que @CAUCHY_ORACLE_MATCH@ et
-- @CAUCHY_ORACLE_DUEL_TIMEOUT@ : tout obstacle d'environnement devient un
-- verdict nommé). La garde ne porte QUE sur l'absence du binaire ; un
-- référent /présent mais en désaccord/ reste un @FAIL@.
skipIfAbsent :: [String] -> String -> IO Verdict -> IO Verdict
skipIfAbsent []   _   act = act
skipIfAbsent exes nom act = do
  found <- firstAvailable exes
  case found of
    Just _  -> act
    Nothing -> pure (Verdict True
      ("SKIP " ++ nom ++ "  (référent absent : " ++ intercalate ", " exes ++ ")")
      Nothing)

-- SNIPPET:oracle-batch-referee
-- | Le référent par lots : N cas rendus en un seul script — le prélude
-- une fois, chaque cas précédé d'un marqueur imprimé — un seul
-- processus, une analyse qui redécoupe la sortie sur les marqueurs.
-- Le coût d'un appel hors processus est dominé par le lancement de
-- l'outil, pas par le calcul (phase 3 : ~11 ms le lancement, ~0,3 ms
-- le cas groupé) ; le lot rend le différentiel à 10⁴ cas praticable.
-- Le script rendu est l'artefact rejouable du harnais : @render@ du
-- 'Referee' obtenu le donne tel quel.
processBatchReferee
  :: String                       -- ^ nom du rapport
  -> [String]                     -- ^ noms d'exécutable candidats
  -> [String]                     -- ^ arguments
  -> String                       -- ^ prélude du script, une seule fois
  -> (String -> String)           -- ^ l'instruction qui imprime une ligne
  -> (q -> String)                -- ^ rendu d'un cas
  -> String                       -- ^ postlude du script
  -> (String -> Either String c)  -- ^ analyse de la tranche d'un cas
  -> Referee [q] [c]
processBatchReferee n exes args prelude sayLine render1 postlude parse1 =
  processReferee n exes args render parse
  where
    marker k = "==CAS-" ++ show (k :: Int) ++ "=="
    render qs =
      prelude
        ++ concat [ sayLine (marker k) ++ render1 q | (k, q) <- zip [1 ..] qs ]
        ++ postlude
    parse out = sequence (zipWith un [1 ..] (slices 1 (lines out)))
      where
        un k = either (\m -> Left ("cas " ++ show (k :: Int) ++ " : " ++ m)) Right . parse1
    -- Les lignes du cas k : entre son marqueur et le suivant (ou la fin).
    -- Un marqueur absent clôt le découpage ; le déficit de résultats est
    -- détecté bruyamment par l'appelant, qui connaît le nombre de cas.
    slices k ls = case break (== marker k) ls of
      (_, [])        -> []
      (_, _ : apres) ->
        let (corps, suite) = break (== marker (k + 1)) apres
        in unlines corps : slices (k + 1) suite
-- END:oracle-batch-referee

-- | Borne la taille des lots d'un référent : les scripts restent de
-- taille raisonnable, les résultats sont recollés dans l'ordre.
chunked :: Int -> Referee [q] [c] -> Referee [q] [c]
chunked m (Referee nom exes call)
  | m <= 0    = error "chunked : taille de lot non positive"
  | otherwise = Referee nom exes go
  where
    go [] = pure []
    go qs = let (tete, reste) = splitAt m qs
            in (++) <$> call tete <*> go reste

-- | Le cas seul, retrouvé depuis le lot : le référent unitaire n'est
-- plus une seconde implémentation, c'est le lot à un élément.
onSingleton :: Referee [q] [c] -> Referee q c
onSingleton (Referee nom exes call) = Referee nom exes $ \q -> do
  cs <- call [q]
  case cs of
    [c] -> pure c
    _   -> fail (nom ++ " : " ++ show (length cs) ++ " résultats pour un cas")

-- SNIPPET:oracle-duel
-- | Même entrée, deux calculs, égalité exigée. Le rétrécissement est un
-- champ obligatoire : un duel sans 'shrinker' ne se construit pas.
data Duel i r = Duel
  { duelName  :: String
  , generator :: Gen i
  , shrinker  :: i -> [i]
  , candidate :: i -> r
  , referee   :: Referee i r
  }
-- END:oracle-duel

-- | Une loi est un duel contre le référent constant « vrai » : même
-- mécanique, référent trivial. Possédé ici depuis la phase 3 — les
-- tests des phases 1–2 en portent des répliques locales, remboursées
-- au vert de chacune.
lawDuel :: String -> Gen i -> (i -> [i]) -> (i -> Bool) -> Duel i Bool
lawDuel nom g shr prop = Duel
  { duelName  = nom
  , generator = g
  , shrinker  = shr
  , candidate = prop
  , referee   = pureReferee "constant vrai" (const True)
  }

-- SNIPPET:oracle-cert
-- | Le duel certifiant : le verdict est réifié. Le juge reçoit
-- l'entrée et la sortie du candidat, consulte le référent comme il
-- l'entend (en obtenir un certificat, le vérifier, déléguer une
-- décision), et rend l'échec expliqué. Le duel d'égalité en est le cas
-- dégénéré : le certificat est le résultat du référent et le juge est
-- @(==)@. Nécessaire dès que l'égalité est mal posée — un référent
-- dont le résultat n'est pas une fonction de l'entrée (phase 3 : le
-- reste de la division multivariée dépend de la liste) se juge par
-- certificat, pas par comparaison.
data CertDuel i a = CertDuel
  { certName      :: String
  , certGenerator :: Gen i
  , certShrinker  :: i -> [i]
  , certCandidate :: i -> a
  , certJudge     :: i -> a -> IO (Either String ())
    -- ^ 'Left' : la raison de l'échec, montrée au contre-exemple.
  }
-- END:oracle-cert

-- | La propriété QuickCheck du duel certifiant. Le candidat n'est
-- forcé que par le juge : un juge qui consulte d'abord le référent
-- atteste sa santé même quand le candidat est un squelette.
certProperty :: Show i => CertDuel i a -> Property
certProperty d =
  forAllShrink (certGenerator d) (certShrinker d) $ \i -> ioProperty $ do
    v <- certJudge d i (certCandidate d i)
    pure $ case v of
      Right () -> property True
      Left why -> counterexample
        ("entree   : " ++ show i ++ "\nverdict  : " ++ why) False

-- | Joue un duel certifiant sur @n@ cas.
runCertDuel :: Show i => Int -> CertDuel i a -> IO Verdict
runCertDuel = runCertDuelWith []

-- | Comme 'runCertDuel', mais déclare les exécutables externes que le juge
-- consultera. Le référent d'un duel certifiant vit /dans son juge/, hors
-- du type 'CertDuel' ; le coureur ne peut donc pas lire @refExes@ tout
-- seul. Les passer ici rend le pré-vol 'skipIfAbsent' disponible aussi
-- pour ce chemin : binaire absent ⇒ @SKIP@ vert. À alimenter par
-- @refExes@ du référent que le juge appelle.
runCertDuelWith :: Show i => [String] -> Int -> CertDuel i a -> IO Verdict
runCertDuelWith exes n d =
  skipIfAbsent exes (certName d) (runProperty n (certName d) (certProperty d))

-- SNIPPET:oracle-batch-duel
-- | Le duel par lots : la consultation du référent, enfouie dans le
-- juge du duel certifiant, est réifiée en /questions/ — 'batchQueries'
-- rend les entrées à soumettre au référent (elles peuvent dépendre de
-- la sortie du candidat : le défaut r − r′ de la phase 3), le juge
-- redevient pur. C'est cette factorisation qui autorise le groupement :
-- les questions de N cas partent en un seul appel. Le duel d'égalité
-- est le cas dégénéré — une question, le juge est @(==)@.
data BatchDuel i a q c = BatchDuel
  { batchName      :: String
  , batchGenerator :: Gen i
  , batchShrinker  :: i -> [i]
  , batchCandidate :: i -> a
  , batchQueries   :: i -> a -> [q]
  , batchJudge     :: i -> a -> [c] -> Either String ()
    -- ^ Reçoit exactement les réponses à ses questions, dans l'ordre.
  }
-- END:oracle-batch-duel

-- | Joue un duel par lots : @n@ entrées pré-tirées (tailles en rampe,
-- comme QuickCheck), une consultation du référent pour le lot entier,
-- jugement cas par cas ; au premier échec, rétrécissement glouton où
-- chaque vague de candidats part elle aussi en un seul lot. Un candidat
-- qui lève (squelette du rouge) est un échec du cas, pas du harnais ;
-- un déficit de réponses du référent est une panne, bruyante.
runBatchDuel :: (Show i, Show q) => Int -> Referee [q] [c] -> BatchDuel i a q c -> IO Verdict
runBatchDuel n ref d = skipIfAbsent (refExes ref) (batchName d) $ borne (batchName d) $ do
  is <- mapM (\k -> generate (resize (k `mod` 100) (batchGenerator d)))
             [0 .. n - 1]
  fails <- judgeBatch ref d is
  case fails of
    [] -> pure (Verdict True
            ("OK   " ++ batchName d ++ "  (" ++ show n ++ " cas)") Nothing)
    (f : _) -> do
      (iMin, whyMin) <- shrinkBatch ref d f
      let ce = [show iMin, whyMin]
      pure (Verdict False
        ("FAIL " ++ batchName d ++ " — contre-exemple : " ++ unwords ce)
        (Just ce))

-- | Juge un lot d'entrées : les cas tombés, avec leur raison.
judgeBatch :: (Show i, Show q)
           => Referee [q] [c] -> BatchDuel i a q c -> [i] -> IO [(i, String)]
judgeBatch ref d is = do
  prepared <- mapM prepare is
  let qs = concat [ qs' | Right (_, qs') <- prepared ]
  cs <- if null qs then pure [] else refCall ref qs
  if length cs /= length qs
    then fail (refName ref ++ " : " ++ show (length cs)
               ++ " réponses pour " ++ show (length qs) ++ " questions")
    else verdicts is prepared cs
  where
    -- Forcer ce que le rendu forcera (via 'show') : l'error d'un
    -- squelette tombe ici, cas par cas, au lieu d'emporter le lot.
    prepare i = capture $ do
      let a   = batchCandidate d i
          qs' = batchQueries d i a
      _ <- evaluate (length (show qs'))
      pure (a, qs')
    -- Le jugement aussi est forcé sous capture : quand la question ne
    -- dépend pas du candidat, l'error d'un squelette n'éclôt qu'ici.
    verdicts [] _ _ = pure []
    verdicts (i : is') (Left why : ps) cs =
      ((i, why) :) <$> verdicts is' ps cs
    verdicts (i : is') (Right (a, qs') : ps) cs = do
      let (miennes, reste) = splitAt (length qs') cs
      v <- capture (evaluate (force (batchJudge d i a miennes)))
      let ici = case v of
            Left panne      -> [(i, panne)]
            Right (Left w)  -> [(i, w)]
            Right (Right _) -> []
      (ici ++) <$> verdicts is' ps reste
    verdicts _ [] _ = pure []
    force v = length (either id (const "") v) `seq` v
    capture act =
      either (\e -> Left (show (e :: SomeException))) Right <$> try act

-- | Rétrécissement glouton, borné : la première candidate encore en
-- échec relance la descente, chaque vague en un seul lot.
shrinkBatch :: (Show i, Show q)
            => Referee [q] [c] -> BatchDuel i a q c -> (i, String) -> IO (i, String)
shrinkBatch ref d = go (100 :: Int)
  where
    go 0 f = pure f
    go k (i, why) = do
      fails <- judgeBatch ref d (batchShrinker d i)
      case fails of
        []      -> pure (i, why)
        (f : _) -> go (k - 1) f

-- | La propriété QuickCheck du duel.
duelProperty :: (Show i, Show r, Eq r) => Duel i r -> Property
duelProperty d =
  forAllShrink (generator d) (shrinker d) $ \i -> ioProperty $ do
    attendu <- refCall (referee d) i
    let obtenu = candidate d i
    pure . counterexample (mismatch i attendu obtenu) $ obtenu == attendu
  where
    mismatch i attendu obtenu =
      "entree   : " ++ show i ++
      "\nreferent : " ++ show attendu ++
      "\ncandidat : " ++ show obtenu

-- | Le verdict d'un duel : la ligne de rapport — au format que les pages
-- de vérification rejouent — et, en cas d'échec, le contre-exemple
-- rétréci.
data Verdict = Verdict
  { vPassed  :: Bool
  , vLine    :: String
  , vMinimal :: Maybe [String]
  }

-- | Découpe une liste de motifs séparés par des virgules (vide ignoré).
commaSplit :: String -> [String]
commaSplit s = filter (not . null) (go s)
  where
    go t = case break (== ',') t of
      (a, [])     -> [a]
      (a, _ : b)  -> a : go b

-- | Le tour de contrôle de tout duel nommé, quatre services :
--
-- * @CAUCHY_ORACLE_SKIP@ (sous-chaînes séparées par des virgules) — tout
--   duel dont le nom contient l'une d'elles est sauté en vert. Le pendant
--   /exclusif/ de @CAUCHY_ORACLE_MATCH@ : la CI rapide des PR y déclare les
--   familles lourdes (p. ex. @cyclic-6,katsura@) ; main ne le pose pas et
--   joue la suite complète. La couverture exhaustive reste garantie à la
--   fusion.
-- * @CAUCHY_ORACLE_MATCH@ (sous-chaîne du nom) — lancer /un/ duel sans payer
--   la suite ; hors motif, verdict @SKIP@ vert sans exécution. La
--   suite complète reste l'artefact de jalon et de CI.
-- * @CAUCHY_ORACLE_DUEL_TIMEOUT@ (secondes) — un duel qui dépasse rend un
--   verdict rouge « dépassement », nommé, au lieu de bloquer la
--   suite : tout blocage devient une information. 'timeout' repose sur
--   les exceptions asynchrones, délivrées aux points d'allocation —
--   trois angles morts distincts, à ne pas confondre :
--
--     1. un sous-processus bloqué dans un appel étranger /sûr/
--        (@readProcessWithExitCode@ en attente d'un Singular pendu) —
--        n'est interruptible que sous le RTS fileté (@-threaded@ sur la
--        stanza de test) ; sans lui, le thread bloqué en FFI ne reçoit
--        jamais l'exception. C'est le seul angle que @-threaded@ ferme ;
--     2. une boucle Haskell pure non-allouante échappe à 'timeout' en
--        tout état de cause ; elle n'arrive pas ici — les duels
--        allouent (polynômes sur Map) ;
--     3. un calcul dominé par un appel étranger /non sûr/ (@ccall
--        unsafe@ vers libgmp — @mpz_gcd@\/@mpz_mul@ sur des coefficients
--        ℚ géants, comme le lex à 3 indéterminées qui explose) tient la
--        capability sans point de sûreté : ni 'timeout' ni @-threaded@
--        ne le bornent. Le remède est côté /entrée/ (borner la taille
--        des familles tirées — cf. @genElimFamille@), pas côté garde.
--
--   L'invariant tenu côté harnais : tout appel référent d'un duel
--   nommé passe sous 'borne' (le @refCall@ vit dans le candidat, le
--   juge, ou un 'CertDuel' — jamais avant le coureur).
-- * Le chronométrage, toujours : la durée s'ajoute à la ligne de
--   verdict dès qu'elle se voit (≥ 0,1 s) — la prochaine lenteur se
--   localise en une lecture.
borne :: String -> IO Verdict -> IO Verdict
borne nom act = do
  skips <- maybe [] commaSplit <$> lookupEnv "CAUCHY_ORACLE_SKIP"
  motif <- lookupEnv "CAUCHY_ORACLE_MATCH"
  if any (`isInfixOf` nom) skips
    then pure (Verdict True ("SKIP " ++ nom ++ "  (CAUCHY_ORACLE_SKIP)") Nothing)
    else case motif of
      Just m | not (m `isInfixOf` nom) ->
        pure (Verdict True ("SKIP " ++ nom ++ "  (CAUCHY_ORACLE_MATCH)") Nothing)
      _ -> do
        budget <- lookupEnv "CAUCHY_ORACLE_DUEL_TIMEOUT"
        t0 <- getMonotonicTime
        -- Battement : un item long (cyclic-6 ~130 s) reste muet pendant
        -- tout son calcul — « inobservable toute sa durée ». Un fil
        -- annexe tique toutes les 10 s sur stderr (il vit, et depuis
        -- combien de temps) sans polluer les lignes de verdict parsées
        -- sur stdout ; le 'finally' le tue avec l'item, quelle qu'en soit
        -- l'issue. (Le battement tourne même sans -threaded : buchberger
        -- alloue, le scheduler rend la main aux points d'allocation.)
        battement <- forkIO (tic t0)
        v <- garde budget `finally` killThread battement
        t1 <- getMonotonicTime
        pure (chronometre (t1 - t0) v)
  where
    -- La garde de temps : 'timeout' borne le calcul, le dépassement
    -- devient un FAIL nommé. (Limites de 'timeout' : voir le Haddock —
    -- les trois angles morts.)
    garde budget = case budget >>= readMaybe of
      Nothing -> act
      Just s  -> do
        r <- timeout (s * 1000000) act
        pure $ case r of
          Just verdict -> verdict
          Nothing      -> Verdict False
            ("FAIL " ++ nom ++ " — dépassement (" ++ show (s :: Int) ++ " s)")
            Nothing
    tic t0 = do
      threadDelay (10 * 1000000)
      t <- getMonotonicTime
      hPutStrLn stderr
        ("    ⏳ " ++ nom ++ " — " ++ show (round (t - t0) :: Int) ++ " s")
      tic t0

-- | La durée sur la ligne — les duels instantanés restent sobres.
chronometre :: Double -> Verdict -> Verdict
chronometre d v
  | d < 0.1   = v
  | otherwise = v { vLine = vLine v ++ printf "  [%.1f s]" d }

-- | Joue un duel sur @n@ cas.
runDuel :: (Show i, Show r, Eq r) => Int -> Duel i r -> IO Verdict
runDuel n d =
  let nom = refName (referee d) ++ " / " ++ duelName d
  in skipIfAbsent (refExes (referee d)) nom (runProperty n nom (duelProperty d))

-- | Le coureur partagé : @n@ cas, un nom, une propriété — un verdict.
-- Exporté pour les propriétés déjà empaquetées ailleurs (les batteries
-- de lois de @quickcheck-classes-base@, p. ex.) : générateur et
-- rétrécissement sont alors les leurs, seul le rapport est du harnais.
runProperty :: Int -> String -> Property -> IO Verdict
runProperty n nom prop = borne nom $ do
  r <- quickCheckWithResult stdArgs { maxSuccess = n, chatty = False } prop
  pure $ case r of
    Success {} -> Verdict True ("OK   " ++ nom ++ "  (" ++ show n ++ " cas)") Nothing
    Failure { failingTestCase = c } ->
      Verdict False ("FAIL " ++ nom ++ " — contre-exemple : " ++ unwords c) (Just c)
    _ -> Verdict False ("FAIL " ++ nom ++ " — " ++ output r) Nothing

-- | Joue une suite hétérogène, renvoie le succès global. Chaque ligne
-- s'imprime — et se vide — dès que son verdict tombe : un run long est
-- observable pendant qu'il court, pas seulement à la fin.
runSuite :: [IO Verdict] -> IO Bool
runSuite acts = do
  vs <- mapM un acts
  pure (all vPassed vs)
  where
    un act = do
      v <- act
      putStrLn (vLine v)
      hFlush stdout
      pure v
