-- | Le vocabulaire Singular de la famille : rendu d'une description
-- en expression, analyse de la notation courte, déclaration d'anneau,
-- protocole d'idéaux, référent par lots. C'est la source unique,
-- hoistée des suites des phases 3–4 — la dette « réplique
-- render\/parse » datée 2026-06-12 est remboursée ici, au vert de la
-- série 4. Une suite de tests n'étant pas importable par une autre,
-- la source unique vit dans le harnais.
--
-- Représentation pivot : la /description/ [(exposants, coefficient)],
-- jamais un porteur d'une bibliothèque jugée — le vocabulaire doit
-- rester sain quand le candidat est un squelette.
--
-- Limites assumées : variables en lettres seules (six — cyclic-6 est
-- la plus large des familles du duel décisif), exposants imprimés en
-- notation courte (@xy2@ = x·y²) — analysés chiffre à chiffre, licite
-- tant que les degrés restent petits. L'arité est partout un paramètre
-- explicite, gardée au rendu comme à l'analyse : un exposant abandonné
-- en silence ferait juger un autre polynôme que celui soumis.
module Test.Cauchy.Singular
  ( -- * La description et sa forme canonique
    TermL
  , OrderName
  , normalizeT
  , addT
  , subT
    -- * Rendu et analyse
  , renderPoly
  , parsePoly
  , variables
  , ringOf
  , cleanLines
    -- * Le référent par lots
  , singularExes
  , singularBatch
    -- * Le protocole d'idéaux
  , printIdeal
  , parseIdeal
  , parseIdealOnly
  ) where

import Data.Char (isDigit, isSpace)
import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator, (%))
import Numeric.Natural (Natural)

import Test.Cauchy.Oracle (Referee, processBatchReferee)

-- | Une description de polynôme : exposants → coefficient, sur ℚ.
type TermL = [([Natural], Rational)]

-- | L'ordre du ring Singular : @"lp"@ = lex, @"Dp"@ = grlex,
-- @"dp"@ = grevlex (sondé le 2026-06-12).
type OrderName = String

-- | Forme canonique : exposants égaux combinés, zéros éliminés, ordre
-- croissant des listes d'exposants — la comparaison des descriptions
-- passe par ici.
normalizeT :: TermL -> TermL
normalizeT =
  sortOn fst . filter ((/= 0) . snd) . Map.toList . Map.fromListWith (+)

-- | Somme et différence de descriptions (pour le défaut r − r′).
addT :: TermL -> TermL -> TermL
addT a b = normalizeT (a ++ b)

subT :: TermL -> TermL -> TermL
subT a b = addT a (map (fmap negate) b)

-- ---------------------------------------------------------------------
-- Rendu : description → expression Singular.

-- | Les indéterminées, en lettres seules — six : cyclic-6 est la plus
-- large des familles. L'arité d'un appel est toujours un préfixe.
variables :: [Char]
variables = "xyzuvw"

-- | Rendu d'une description, à l'arité @k@ donnée. Arité gardée des
-- deux côtés : un terme plus large que @k@ comme un @k@ au-delà des
-- variables sont des erreurs du harnais — un zip nu abandonnerait les
-- exposants excédentaires en silence et le référent jugerait un autre
-- polynôme que celui soumis (le piège exact de katsura).
renderPoly :: Int -> TermL -> String
renderPoly k ts
  | k > length variables =
      error ("Test.Cauchy.Singular : renderPoly — arité " ++ show k
             ++ " au-delà des variables " ++ variables)
  | otherwise = case normalizeT ts of
      [] -> "0"
      ns -> intercalate "+" (map term ns)
  where
    term (es, c)
      | length es > k =
          error ("Test.Cauchy.Singular : renderPoly — terme à "
                 ++ show (length es) ++ " exposants pour l'arité "
                 ++ show k)
      | otherwise = intercalate "*" (coef c : pows es)
    coef c
      | denominator c == 1 = "(" ++ show (numerator c) ++ ")"
      | otherwise = "(" ++ show (numerator c) ++ "/"
                        ++ show (denominator c) ++ ")"
    pows es =
      [ [v] ++ "^" ++ show e
      | (v, e) <- zip variables es
      , e /= 0
      ]

-- | La déclaration d'anneau : @k@ indéterminées sur ℚ, ordre donné.
-- Gardes d'arité et d'ordre — un ordre inconnu de Singular ferait
-- échouer le script loin de sa cause.
ringOf :: Int -> OrderName -> String
ringOf k ord
  | k > length variables =
      error ("Test.Cauchy.Singular : ringOf — arité " ++ show k
             ++ " au-delà des variables " ++ variables)
  | ord `notElem` ["lp", "Dp", "dp"] =
      error ("Test.Cauchy.Singular : ringOf — ordre inconnu " ++ ord)
  | otherwise =
      "ring r=0,(" ++ intercalate "," (map (: []) (take k variables))
        ++ ")," ++ ord ++ ";\n"

-- ---------------------------------------------------------------------
-- Analyse : sortie Singular (notation courte) → description.

-- | Analyse un polynôme imprimé par Singular : termes ±, coefficient
-- entier ou fraction, puis lettres à exposant en chiffres (@x2y@,
-- @xy3@). Arité fixée par l'appelant et gardée : une lettre reconnue
-- mais au-delà de l'arité est un 'Left' — l'abandonner en silence
-- était le bug latent de la réplique remboursée.
parsePoly :: Int -> String -> Either String TermL
parsePoly k raw =
  let s = filter (not . isSpace) raw
  in if s == "0" then Right [] else normalizeT <$> mapM term (splitTerms s)
  where
    splitTerms ('+' : cs) = splitTerms cs
    splitTerms cs = go cs ""
      where
        go [] acc = [reverse acc]
        go (c : rest) acc
          | (c == '+' || c == '-') && not (null acc) =
              reverse acc : go rest [c]
          | otherwise = go rest (c : acc)
    term t0 = do
      let (sgn, t1) = case t0 of
            '-' : r -> (-1, r)
            '+' : r -> (1, r)
            r       -> (1 :: Rational, r)
      (c, t2) <- coefOf t1
      es <- powsOf t2 (replicate k 0)
      pure (es, sgn * c)
    coefOf cs = case span isDigit cs of
      ("", _) -> Right (1, cs)
      (n, '/' : rest) -> case span isDigit rest of
        ("", _)    -> Left ("fraction sans dénominateur : " ++ cs)
        (d, rest') -> Right (read n % read d, dropStar rest')
      (n, rest) -> Right (fromInteger (read n), dropStar rest)
    dropStar ('*' : cs) = cs
    dropStar cs         = cs
    powsOf [] es = Right es
    powsOf (c : cs) es = case lookup c (zip variables [0 :: Int ..]) of
      Nothing -> Left ("indéterminée inconnue : " ++ [c])
      Just i
        | i >= k ->
            Left ("indéterminée hors arité : " ++ [c]
                  ++ " (indice " ++ show i ++ ", arité " ++ show k ++ ")")
        | otherwise ->
            let (ds, rest) = span isDigit cs
                e = if null ds then 1 else read ds
                rest' = dropStar (dropCaret rest)
            in powsOf rest' (bump i e es)
      where
        dropCaret ('^' : r) = r
        dropCaret r         = r
    bump i e es =
      [ if j == i then v + e else v | (j, v) <- zip [0 ..] es ]

-- | Les lignes utiles d'une sortie : ni vides, ni commentaires (les
-- redéfinitions entre cas d'un lot n'émettent que des lignes @//@).
cleanLines :: String -> [String]
cleanLines =
  filter (\l -> not (null l) && take 2 l /= "//")
    . map (dropWhile isSpace) . lines

-- ---------------------------------------------------------------------
-- Le référent par lots.

-- | Les noms d'exécutable candidats — la casse varie selon le paquet.
singularExes :: [String]
singularExes = ["Singular", "singular"]

-- | Un référent Singular par lots : le prélude — l'anneau, et ce que
-- la phase y ajoute (@option(redSB)@ en phase 4, rien en phase 3) —
-- déclaré une fois, chaque cas précédé d'un marqueur imprimé (une
-- chaîne nue est imprimée telle quelle).
singularBatch
  :: String -> String -> (q -> String) -> (String -> Either String c)
  -> Referee [q] [c]
singularBatch nom prelude render1 parse1 =
  processBatchReferee nom singularExes ["-q"] prelude say render1
    "exit;\n" parse1
  where
    say s = show s ++ ";\n"

-- ---------------------------------------------------------------------
-- Le protocole d'idéaux : taille puis éléments.

-- | Un idéal imprimé élément par élément, précédé de sa taille —
-- le protocole commun des sorties d'idéaux.
printIdeal :: String -> String
printIdeal nom =
  "int n_" ++ nom ++ "=size(" ++ nom ++ ");\nn_" ++ nom ++ ";\n"
    ++ "int i_" ++ nom ++ ";\n"
    ++ "for(i_" ++ nom ++ "=1;i_" ++ nom ++ "<=n_" ++ nom ++ ";i_"
    ++ nom ++ "++){" ++ nom ++ "[i_" ++ nom ++ "];}\n"

-- | Analyse @taille puis éléments@, rend la suite non consommée.
parseIdeal :: Int -> [String] -> Either String ([TermL], [String])
parseIdeal k (n : ls)
  | all isDigit n && not (null n) =
      let m = read n
      in if length ls >= m
           then (,) <$> mapM (parsePoly k) (take m ls) <*> pure (drop m ls)
           else Left ("idéal tronqué : " ++ show (n : ls))
parseIdeal _ ls = Left ("taille d'idéal attendue : " ++ show ls)

-- | Analyse exactement un idéal — la tranche d'un cas.
parseIdealOnly :: Int -> String -> Either String [TermL]
parseIdealOnly k out = do
  (gs, rest) <- parseIdeal k (cleanLines out)
  if null rest then Right gs
               else Left ("sortie d'idéal excédentaire : " ++ show rest)
