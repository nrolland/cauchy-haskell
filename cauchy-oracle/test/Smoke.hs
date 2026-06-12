-- | Auto-test du harnais, et fumée Singular.
--
-- 1. Un duel honnête doit passer.
-- 2. Un duel saboté doit échouer, et rétrécir jusqu'au plus petit
--    contre-exemple — un harnais qui ne sait pas échouer ne prouve rien.
-- 3. Fumée Singular (le chemin critique de la phase 4, dérisqué sans une
--    ligne de Gröbner) : un reduce trivial, activé par ORACLE_SINGULAR=1 ;
--    sinon SKIP explicite — jamais silencieux.
module Main (main) where

import Data.Char (isSpace)
import System.Environment (lookupEnv)
import System.Exit (exitFailure, exitSuccess)
import Test.Cauchy.Oracle
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

  singular <- singularSmoke
  putStrLn (vLine singular)

  if vPassed honest && detected && shrunk && vPassed singular
    then exitSuccess
    else exitFailure

-- | reduce(x² + x, std⟨x⟩) = 0 — le plus petit calcul que Singular sache
-- faire, suffisant pour prouver que le conteneur CI parle à l'outil.
singularSmoke :: IO Verdict
singularSmoke = do
  gate <- lookupEnv "ORACLE_SINGULAR"
  case gate of
    Nothing -> pure (Verdict True
      "SKIP singular / fumée reduce (ORACLE_SINGULAR non défini)" Nothing)
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
