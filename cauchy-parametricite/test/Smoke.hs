-- | Vérification native (sans wasm) des définitions d'exposition et des
-- données des widgets. La /même/ étoile de la bibliothèque — sur 'Matrix',
-- sur 'Series', sur le tropical — calcule ces valeurs ; si le rendu ou les
-- nombres dévient, ce test échoue. C'est la garde contre une réplique JS
-- qui mentirait : ce que cette suite fixe est exactement ce que la frontière
-- wasm (@wasm\/Exports.hs@) sérialise pour les pages.
module Main (main) where

import Control.Monad (unless)
import Data.List (isInfixOf)
import Data.Monoid (Sum (..))
import System.Exit (exitFailure)

import Data.Semiring.Tropical (Tropical (..))

import Data.Cauchy.Parametricite.Showcase
  ( fermetureBool, fermetureRegex, fermetureTrop )
import Data.Cauchy.Parametricite.Widgets
  ( etoileJson, grapheJson, listeJson, puissanceJson, valeurSensJson )

check :: (Eq a, Show a) => String -> a -> a -> IO Bool
check nom attendu obtenu
  | attendu == obtenu = do putStrLn ("OK   " ++ nom ++ " = " ++ show obtenu); pure True
  | otherwise         = do
      putStrLn ("FAIL " ++ nom ++ " : attendu " ++ show attendu ++ ", obtenu " ++ show obtenu)
      pure False

-- La loi tient : le membre droit (star x) et le membre gauche (1 + x·star x)
-- coïncident. On donne la valeur ASCII attendue des deux membres et on
-- vérifie que le JSON porte « droit = ce membre, gauche = ce même membre ».
loiTient :: String -> String -> String -> IO Bool
loiTient nom membre js
  | sub `isInfixOf` js = do putStrLn ("OK   " ++ nom ++ " : droit = gauche = " ++ membre); pure True
  | otherwise          = do putStrLn ("FAIL " ++ nom ++ " : " ++ js); pure False
  where sub = "\"droit\":" ++ membre ++ ",\"gauche\":" ++ membre

main :: IO ()
main = do
  oks <- sequence
    -- ④ graphe-fermeture : la même formule, trois semi-anneaux.
    [ check "regex (boucle a)"   "a*bc*" (fermetureRegex True)
    , check "regex (sans a)"     "bc*"   (fermetureRegex False)
    , check "bool atteignable"   True    (fermetureBool True)
    , check "trop coût minimal"  (Tropical (Sum 1)) (fermetureTrop True)

    -- ② puissance contre fermeture (Matrix 3) : masses des sommes partielles
    -- et — sur 𝔹 — la fermeture réelle (star de Matrix) qui égale le plateau.
    , check "puiss 𝔹 acyclique"
        "{\"sr\":0,\"cycle\":0,\"masses\":[3,5,6,6,6,6,6],\"closure\":6}"
        (puissanceJson 0)
    , check "puiss 𝔹 cyclique (saturation 9)"
        "{\"sr\":0,\"cycle\":1,\"masses\":[3,6,9,9,9,9,9],\"closure\":9}"
        (puissanceJson 1)
    , check "puiss ℕ acyclique (plateau, pas d'étoile)"
        "{\"sr\":1,\"cycle\":0,\"masses\":[3,5,6,6,6,6,6],\"closure\":null}"
        (puissanceJson 2)
    , check "puiss ℕ cyclique (divergence linéaire)"
        "{\"sr\":1,\"cycle\":1,\"masses\":[3,6,9,12,15,18,21],\"closure\":null}"
        (puissanceJson 3)

    -- ③ valeur contre sens : mêmes nombres à gauche, le coefficient de
    -- star(x+x²) relu dans S à droite.
    , check "sens ℚ = Fibonacci"
        "{\"bare\":[1,1,2,3,5,8],\"sens\":[\"1\",\"1\",\"2\",\"3\",\"5\",\"8\"]}"
        (valeurSensJson 0)
    , check "sens tropical pondéré = ⌈n/2⌉"
        "{\"bare\":[1,1,2,3,5,8],\"sens\":[\"0\",\"1\",\"1\",\"2\",\"2\",\"3\"]}"
        (valeurSensJson 1)
    , check "sens 𝔹 = existence"
        "{\"bare\":[1,1,2,3,5,8],\"sens\":[\"1\",\"1\",\"1\",\"1\",\"1\",\"1\"]}"
        (valeurSensJson 2)

    -- ③ liste géométrique : kⁿ = [xⁿ] star(k·x).
    , check "liste k=2 → 2ⁿ" "[\"1\",\"2\",\"4\",\"8\",\"16\"]" (listeJson 2)
    , check "liste k=3 → 3ⁿ" "[\"1\",\"3\",\"9\",\"27\",\"81\"]" (listeJson 3)

    -- ④ graphe-fermeture : les trois facteurs et le résultat, par porteur.
    , check "graphe regex (boucle a)"
        "{\"sr\":0,\"fa\":\"a*\",\"fb\":\"b\",\"fc\":\"c*\",\"res\":\"a*bc*\"}"
        (grapheJson 1)
    , check "graphe 𝔹 atteignable"
        "{\"sr\":1,\"fa\":1,\"fb\":1,\"fc\":1,\"res\":true}"
        (grapheJson 3)
    , check "graphe tropical coût 1"
        "{\"sr\":2,\"fa\":0,\"fb\":1,\"fc\":0,\"res\":1}"
        (grapheJson 5)
    ]
  -- ① la loi, par instance : droit = gauche dans chaque porteur.
  loi <- sequence
    [ loiTient "loi 𝔹"        "\"1\""                            (etoileJson 0)
    , loiTient "loi Series ℚ" "[\"1\",\"1\",\"1\",\"1\",\"1\",\"1\"]" (etoileJson 1)
    , loiTient "loi tropical" "\"0\""                            (etoileJson 2)
    ]
  unless (and oks && and loi) exitFailure
