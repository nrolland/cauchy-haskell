-- | Le référent Singular de la phase 3 : trois référents
-- ('processReferee' de cauchy-oracle — le premier référent hors
-- processus de la famille, exercé pour de vrai). Le vocabulaire —
-- rendu, analyse, anneau, lot — vient de 'Test.Cauchy.Singular' : la
-- réplique render\/parse datée 2026-06-12 est remboursée, la source
-- unique est le harnais ; ne restent ici que les wrappers d'arité
-- (trois variables, ordre lex, pas de @option(redSB)@ — le
-- comportement de la phase 3, inchangé).
--
-- Représentation pivot : la /description/ [(exposants, coefficient)],
-- jamais un porteur de la bibliothèque jugée — le référent doit rester
-- sain quand le candidat est un squelette.
--
-- Les cas sont groupés par script ('processBatchReferee') : une
-- déclaration d'anneau, N cas séparés par des marqueurs imprimés, un
-- seul processus — la note datée 2026-06-12 « un processus par cas »
-- est remboursée ; le référent unitaire est le lot à un élément.
module SingularRef
  ( TermL
  , normalizeT
  , addT
  , subT
  , renderPoly
  , parsePoly
  , divisionRef
  , divisionRefN
  , reduceStdRef
  , reduceStdRefN
  , stdRef
  , stdRefN
  ) where

import Data.Char (isDigit)
import Data.List (intercalate)

import Test.Cauchy.Oracle (Referee, onSingleton)
import Test.Cauchy.Singular
  (TermL, addT, cleanLines, normalizeT, parsePoly, subT)
import qualified Test.Cauchy.Singular as S

-- | Le rendu de la phase 3 : l'arité maximale est 3 (cyclic-3) —
-- le type @TermL -> String@ des appelants est préservé.
renderPoly :: TermL -> String
renderPoly = S.renderPoly 3

-- | Le lot de la phase 3 : anneau lex à @k@ variables, sans
-- @option(redSB)@ — le prélude de la phase 4 est l'affaire de sa
-- propre suite.
singularBatch
  :: Int -> String -> (q -> String) -> (String -> Either String c)
  -> Referee [q] [c]
singularBatch k nom = S.singularBatch nom (S.ringOf k "lp")

-- ---------------------------------------------------------------------
-- Les trois référents — le lot d'abord, l'unitaire en est le singleton.

-- SNIPPET:singular-division-ref
-- | @division(ideal(p), G)@ : le certificat complet du référent —
-- quotients, reste, unité (1 pour un ordre global). C'est lui que le
-- duel certifiant vérifie avec l'arithmétique du candidat.
divisionRefN :: Int -> Referee [(TermL, [TermL])] [([TermL], TermL, TermL)]
divisionRefN k = singularBatch k "singular division" render parse
  where
    render (p, ds) =
      "poly p=" ++ renderPoly p ++ ";\n"
        ++ "ideal G=" ++ intercalate "," (map renderPoly ds) ++ ";\n"
        ++ "list L=division(ideal(p),G);\n"
        ++ concat
             [ "L[1][" ++ show i ++ ",1];\n" | i <- [1 .. length ds] ]
        ++ "L[2][1];\nL[3][1,1];\n"
    parse out = case cleanLines out of
      ls | length ls >= 3 -> do
        let n = length ls - 2
        qs <- mapM (parsePoly k) (take n ls)
        r  <- parsePoly k (ls !! n)
        u  <- parsePoly k (ls !! (n + 1))
        pure (qs, r, u)
      ls -> Left ("sortie division inattendue : " ++ show ls)

divisionRef :: Int -> Referee (TermL, [TermL]) ([TermL], TermL, TermL)
divisionRef = onSingleton . divisionRefN
-- END:singular-division-ref

-- | @reduce(p, std(G))@ : la forme normale du référent — canonique
-- parce que jugée contre une base standard que le référent calcule
-- lui-même ; le candidat n'implémente aucun Buchberger.
reduceStdRefN :: Int -> Referee [(TermL, [TermL])] [TermL]
reduceStdRefN k = singularBatch k "singular reduce·std" render parse
  where
    render (p, ds) =
      "poly p=" ++ renderPoly p ++ ";\n"
        ++ "ideal G=" ++ intercalate "," (map renderPoly ds) ++ ";\n"
        ++ "reduce(p,std(G));\n"
    parse out = case cleanLines out of
      [l] -> parsePoly k l
      ls  -> Left ("sortie reduce inattendue : " ++ show ls)

reduceStdRef :: Int -> Referee (TermL, [TermL]) TermL
reduceStdRef = onSingleton . reduceStdRefN

-- | @std(G)@ : la base standard du référent (les fixtures de ③ — le
-- candidat divise par elle, jamais ne la calcule).
stdRefN :: Int -> Referee [[TermL]] [[TermL]]
stdRefN k = singularBatch k "singular std" render parse
  where
    render ds =
      "ideal G=" ++ intercalate "," (map renderPoly ds) ++ ";\n"
        ++ "ideal S=std(G);\nint n=size(S);\nn;\nint i;\n"
        ++ "for(i=1;i<=n;i++){S[i];}\n"
    parse out = case cleanLines out of
      (n : ls) | length ls == read' n -> mapM (parsePoly k) ls
      ls -> Left ("sortie std inattendue : " ++ show ls)
      where
        read' n = if all isDigit n then read n else -1

stdRef :: Int -> Referee [TermL] [TermL]
stdRef = onSingleton . stdRefN
