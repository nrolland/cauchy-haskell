-- | Données des widgets de la vitrine des langages : la sortie de la
-- bibliothèque, sérialisée pour les pages. La partie wasm
-- (@wasm/LangExports.hs@) n'est qu'un emballage JSFFI autour de ce
-- module — qui ne dépend de rien de wasm et se compile avec un GHC
-- natif. Les définitions exposées ('Showcase') sont celles que les
-- duels jugent ; les expressions du catalogue sont des entrées de
-- démonstration, pas des définitions.
module LanguageWidgets
  ( decoupagesJson
  , coutJson
  , filtreRowJson
  , traceJson
  ) where

import Data.List (intercalate)
import Data.Monoid (Sum (..))
import Data.Semiring.Tropical (Tropical (..))
import Numeric.Natural (Natural)

import qualified Data.Cauchy.Language.Rational as CR
import           Data.Cauchy.Language.Rational (Expr (..))
import qualified Data.Cauchy.Language.Series as CS

import Showcase (AB (..), coutMinimal, decoupages, sigma)

jsonOf :: [String] -> String
jsonOf xs = "[" ++ intercalate "," xs ++ "]"

str :: String -> String
str s = show s

-- | p(aⁿ) pour p = (a+aa)*, S = ℕ : n = 0 .. k−1 — les valeurs que le
-- duel « découpages » juge contre la récurrence à la main.
decoupagesJson :: Int -> String
decoupagesJson k = jsonOf
  [ str (show (CS.at (replicate n A) (decoupages :: CS.Series AB Natural)))
  | n <- [0 .. k - 1] ]

-- | p(aⁿ) pour p = (3·a ⊕ 5·aa)*, S = Trop : « ∞ » hors langage.
coutJson :: Int -> String
coutJson k = jsonOf
  [ str (rend (CS.at (replicate n A) coutMinimal)) | n <- [0 .. k - 1] ]
  where
    rend Infinity             = "∞"
    rend (Tropical (Sum n))   = show n

-- | Les expressions de démonstration des pages (entrées, pas des
-- définitions) ; l'indice est celui des boutons des widgets.
catalogue :: [Expr AB]
catalogue =
  [ ETimes (EStar (EPlus (ELetter A) (ELetter B)))
           (ETimes (ELetter A) (ELetter B))            -- (a+b)*ab (page ③)
  , EStar (EPlus (ELetter A) (ETimes (ELetter A) (ELetter B))) -- (a+ab)*
  , EStar (ETimes (ELetter A) (EPlus (ELetter A) (ELetter B))) -- (a(a+b))*
  ]

exprAt :: Int -> Expr AB
exprAt i | i >= 0 && i < length catalogue = catalogue !! i
         | otherwise                      = head catalogue

-- | Rendu compact d'une expression : étoile > concaténation > somme.
rendExpr :: Expr AB -> String
rendExpr = go (0 :: Int)
  where
    go _ EZero       = "0"
    go _ EOne        = "1"
    go _ (ELetter A) = "a"
    go _ (ELetter B) = "b"
    go p (EPlus e f)  = paren (p > 0) (go 0 e ++ "+" ++ go 0 f)
    go p (ETimes e f) = paren (p > 1) (go 1 e ++ go 1 f)
    go _ (EStar e)    = go 2 e ++ "*"
    paren True  s = "(" ++ s ++ ")"
    paren False s = s

lettre :: Char -> AB
lettre 'b' = B
lettre _   = A

-- | Les mots sur {a,b} en ordre longueur-lexicographique.
shortlexMots :: [[AB]]
shortlexMots = concatMap mots [0 ..]
  where
    mots :: Int -> [[AB]]
    mots 0 = [[]]
    mots n = [ c : w | c <- sigma, w <- mots (n - 1) ]

rendMot :: [AB] -> String
rendMot [] = "\x03b5"
rendMot w  = map (\c -> if c == A then 'a' else 'b') w

-- | Les verdicts du filtre ν(∂_w e) sur les k premiers mots shortlex —
-- la rangée mobile du cadre de confrontation de ⑥ ; la rangée fixe est
-- celle du référent, figée du run.
filtreRowJson :: Int -> Int -> String
filtreRowJson i k =
  "{\"mots\":" ++ jsonOf (map (str . rendMot) ws)
  ++ ",\"verdicts\":" ++ jsonOf [ if CR.match e w then "1" else "0" | w <- ws ]
  ++ "}"
  where
    e  = exprAt i
    ws = take k shortlexMots

-- | La trace du filtre : les dérivées successives (formes ACI) le long
-- du mot, ν à chaque pas — le widget de ③, branché au code compilé.
traceJson :: Int -> String -> String
traceJson i mot =
  "{\"etapes\":" ++ jsonOf (map etape (scanl pas e0 (map lettre mot))) ++ "}"
  where
    e0 = CR.normACI (exprAt i)
    pas e c = CR.normACI (CR.deltaE c e)
    etape e = "{\"e\":" ++ str (rendExpr e)
           ++ ",\"nu\":" ++ (if CR.nuE e then "1" else "0") ++ "}"
