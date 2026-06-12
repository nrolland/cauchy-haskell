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
    -- * Le duel
  , Duel(..)
  , duelProperty
    -- * Exécution et rapport
  , Verdict(..)
  , runDuel
  , runSuite
  ) where

import Data.List (intercalate)
import System.Directory (findExecutable)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Test.QuickCheck

-- SNIPPET:oracle-referee
-- | Le référent : un nom (celui du rapport) et un appel. Un référent en
-- bibliothèque (@poly@) est pur ; un outil externe (Singular) passe par
-- un processus — le type ne distingue pas, c'est le point.
data Referee i r = Referee
  { refName :: String
  , refCall :: i -> IO r
  }

-- | Référent en bibliothèque.
pureReferee :: String -> (i -> r) -> Referee i r
pureReferee n f = Referee n (pure . f)
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
processReferee n exes args render parse = Referee n call
  where
    call i = do
      exe <- firstExecutable exes
      (code, out, err) <- readProcessWithExitCode exe args (render i)
      case code of
        ExitFailure c ->
          fail (n ++ " : code de sortie " ++ show c ++ " — " ++ err)
        ExitSuccess ->
          either (\m -> fail (n ++ " : analyse — " ++ m)) pure (parse out)

firstExecutable :: [String] -> IO FilePath
firstExecutable names = go names
  where
    go []       = fail ("aucun exécutable parmi : " ++ intercalate ", " names)
    go (e : es) = findExecutable e >>= maybe (go es) pure

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

-- | Joue un duel sur @n@ cas.
runDuel :: (Show i, Show r, Eq r) => Int -> Duel i r -> IO Verdict
runDuel n d = do
  r <- quickCheckWithResult stdArgs { maxSuccess = n, chatty = False }
                            (duelProperty d)
  let nom = refName (referee d) ++ " / " ++ duelName d
  pure $ case r of
    Success {} -> Verdict True ("OK   " ++ nom ++ "  (" ++ show n ++ " cas)") Nothing
    Failure { failingTestCase = c } ->
      Verdict False ("FAIL " ++ nom ++ " — contre-exemple : " ++ unwords c) (Just c)
    _ -> Verdict False ("FAIL " ++ nom ++ " — " ++ output r) Nothing

-- | Joue une suite hétérogène, imprime chaque ligne, renvoie le succès
-- global.
runSuite :: [IO Verdict] -> IO Bool
runSuite acts = do
  vs <- sequence acts
  mapM_ (putStrLn . vLine) vs
  pure (all vPassed vs)
