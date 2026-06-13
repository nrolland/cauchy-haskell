-- | Le référent Singular de la phase 4 : bases réduites (@option
-- (redSB)@), familles cyclic\/katsura générées par le référent
-- lui-même (@polylib.lib@ — jamais retranscrites), élimination.
--
-- Représentation pivot : la /description/ [(exposants, coefficient)],
-- jamais un porteur de la bibliothèque jugée — le référent doit
-- rester sain quand le candidat est un squelette.
--
-- Les référents sont par lots d'emblée ('processBatchReferee' de
-- cauchy-oracle, PR #64) : l'anneau en prélude, un marqueur par cas,
-- l'unitaire est le lot à un élément. Le vocabulaire — rendu, analyse,
-- anneau, protocole d'idéaux, lot — vient de 'Test.Cauchy.Singular' :
-- la réplique de @cauchy-poly\/test\/SingularRef.hs@, dette datée
-- 2026-06-12, est remboursée — la source unique est le harnais ; ne
-- reste ici que le prélude de la phase (@option(redSB)@) et la
-- génération des familles.
module SingularGroebner
  ( TermL
  , OrderName
  , normalizeT
  , renderPoly
  , parsePoly
    -- * Les référents, par lots
  , stdRedSBRefN
  , reduceStdRefN
  , eliminateRefN
    -- * La génération des familles (unitaire : un ring par famille)
  , familyRef
  ) where

import Data.List (intercalate)

import Test.Cauchy.Oracle (Referee, processReferee)
import Test.Cauchy.Singular
  (OrderName, TermL, cleanLines, normalizeT, parseIdeal, parseIdealOnly,
   parsePoly, printIdeal, renderPoly, ringOf, singularExes, variables)
import qualified Test.Cauchy.Singular as S

-- | Le lot de la phase 4 : l'anneau et @option(redSB)@ déclarés une
-- fois en prélude — la base réduite est LA base (③ Théorème 3),
-- l'égalité ensemble contre ensemble est bien posée sur elle.
singularBatch
  :: Int -> OrderName -> String
  -> (q -> String) -> (String -> Either String c)
  -> Referee [q] [c]
singularBatch k ord nom =
  S.singularBatch nom (ringOf k ord ++ "option(redSB);\n")

-- ---------------------------------------------------------------------
-- Les référents — le lot d'abord, l'unitaire en est le singleton.

-- | @option(redSB); std(G)@ : LA base réduite du référent — unique à
-- ordre fixé (③ Théorème 3), l'égalité ensemble contre ensemble est
-- bien posée sur elle.
stdRedSBRefN :: Int -> OrderName -> Referee [[TermL]] [[TermL]]
stdRedSBRefN k ord = singularBatch k ord "singular std·redSB" render parse
  where
    render ds =
      "ideal G=" ++ intercalate "," (map (renderPoly k) ds) ++ ";\n"
        ++ "ideal S=std(G);\n" ++ printIdeal "S"
    parse = parseIdealOnly k

-- | @reduce(p, std(G))@ : la forme normale du référent — le juge de
-- l'appartenance (p ∈ ⟨G⟩ ⟺ 0 chez lui comme chez nous, ① Corollaire).
reduceStdRefN :: Int -> OrderName -> Referee [(TermL, [TermL])] [TermL]
reduceStdRefN k ord = singularBatch k ord "singular reduce·std" render parse
  where
    render (p, ds) =
      "poly p=" ++ renderPoly k p ++ ";\n"
        ++ "ideal G=" ++ intercalate "," (map (renderPoly k) ds) ++ ";\n"
        ++ "reduce(p,std(G));\n"
    parse out = case cleanLines out of
      [l] -> parsePoly k l
      ls  -> Left ("sortie reduce inattendue : " ++ show ls)

-- | @std(eliminate(I, x₁·…·xⱼ))@ : l'idéal d'élimination Iⱼ du
-- référent, en base réduite — le juge de la coupe (④ Théorème 1).
-- L'ordre du ring est celui de la comparaison (la coupe lex se juge
-- dans lp). @eliminate@ est disponible sans LIB (sondé 2026-06-12).
eliminateRefN :: Int -> OrderName -> Int -> Referee [[TermL]] [[TermL]]
eliminateRefN k ord j = singularBatch k ord "singular eliminate" render parse
  where
    render ds =
      "ideal G=" ++ intercalate "," (map (renderPoly k) ds) ++ ";\n"
        ++ "ideal E=std(eliminate(G,"
        ++ intercalate "*" (map (: []) (take j variables)) ++ "));\n"
        ++ printIdeal "E"
    parse = parseIdealOnly k

-- | @katsura(n)@ \/ @cyclic(n)@ de @polylib.lib@ — n polynômes dans
-- les n indéterminées du ring (convention mesurée, note d'entrée du
-- 2026-06-12) — avec leur base réduite, dans le même processus : la
-- famille du duel décisif n'est jamais retranscrite, le référent la
-- génère et la résout. Unitaire et non par lots : l'arité est le ring
-- lui-même, un ring par famille.
familyRef :: String -> Int -> OrderName -> Referee () ([TermL], [TermL])
familyRef name n ord =
  processReferee ("singular " ++ name ++ "-" ++ show n) singularExes ["-q"]
    render parse
  where
    render () =
      "LIB \"polylib.lib\";\n"
        ++ ringOf n ord
        ++ "ideal F=" ++ name ++ "(" ++ show n ++ ");\n"
        ++ "option(redSB);\nideal S=std(F);\n"
        ++ printIdeal "F" ++ printIdeal "S" ++ "exit;\n"
    parse out = do
      (fs, rest)  <- parseIdeal n (cleanLines out)
      (ss, rest') <- parseIdeal n rest
      if null rest'
        then Right (fs, ss)
        else Left ("sortie famille excédentaire : " ++ show rest')
