{-# LANGUAGE TypeFamilies #-}
-- | Bases de Gröbner et appartenance à l'idéal (série 4).
--
-- La série 3 laissait une équation sans forme normale : le reste de
-- la division dépend de la liste des diviseurs. On ne répare pas
-- l'algorithme, on répare la liste (page ①) : G est une base de
-- Gröbner de I = ⟨G⟩ quand ses têtes engendrent toutes celles de
-- l'idéal — ⟨lm G⟩ = ⟨lm I⟩ — et alors le reste de la division de la
-- série 3, inchangée, devient canonique. Trois mouvements sur ce
-- pivot : /reconnaître/ une telle liste en un nombre fini de tests
-- ('spol', 'isGroebner' — page ②) ; en /produire/ une ('buchberger',
-- 'reduce' — page ③) ; /récolter/ — l'appartenance décidée ('nf',
-- 'member' — page ①) et la projection calculée ('cut' — page ④).
--
-- Tout est sur corps : annuler les têtes l'exige — l'hypothèse
-- @Field s@ de chaque signature est celle de l'arc entier. L'ordre
-- est le type d'indice @o@, comme dans toute la famille : @MPoly
-- (Lex 2) s@ et @MPoly (GrevLex 2) s@ sont deux types, et une base de
-- Gröbner est une base /pour cet ordre/.
module Data.Cauchy.Groebner
  ( -- * La forme normale et l'appartenance (page ①)
    nf
  , member
    -- * Le S-polynôme et le critère fini (page ②)
  , spol
  , isGroebner
    -- * La complétion et la base réduite (page ③)
  , buchberger
  , reduce
    -- * La coupe d'élimination (page ④)
  , cut
  ) where

import Prelude hiding (negate)

import Data.List (minimumBy, partition, sortOn, tails)
import Data.Ord (comparing)
import Numeric.Natural (Natural)

import Data.Euclidean (Field)
import qualified Data.Euclidean as E
import Data.Semiring (Ring (..), Semiring (..))

import Data.Cauchy.Multi (MPoly, division, fromTerms, leading, toTerms)
import Data.Cauchy.Order (Exp, MonomialOrder (..), components, divides,
                          minus, sup, totalDegree)

-- | NF(p, G) : le reste de la division de la série 3 (① Théorème 1).
-- Quand G est une base de Gröbner, il ne dépend que de p, de ⟨G⟩ et
-- de l'ordre — ni de l'ordre de la liste, ni de la stratégie ; les
-- quotients, eux, restent libres. Hypothèses du théorème : S corps,
-- ordre admissible (le type d'indice @o@).
{-# INLINABLE nf #-}
-- SNIPPET:groebner-nf
-- NOTE:division: le reste de la division du multivarié, inchangé — sur une base de Gröbner il ne dépend que de p, de l'idéal et de l'ordre : NF(p, I, ≺)
nf :: (MonomialOrder o, Field s, Ring s, Eq s)
   => MPoly o s -> [MPoly o s] -> MPoly o s
nf p ds = snd (division p ds)
-- END:groebner-nf

-- | p ∈ ⟨G⟩, décidé par NF(p, G) = 0 (① Corollaire 1). Hypothèse :
-- G est une base de Gröbner — sinon un reste non nul ne prouve rien.
{-# INLINABLE member #-}
-- SNIPPET:groebner-member
-- NOTE:nf: l'appartenance décidée par un seul reste — hypothèse : G est une base de Gröbner, sinon un reste non nul ne prouve rien
member :: (MonomialOrder o, Field s, Ring s, Eq s)
       => MPoly o s -> [MPoly o s] -> Bool
member p g = nf p g == zero
-- END:groebner-member

-- | Spol(p, q) = (x^(γ−α)\/lc p)·p − (x^(γ−β)\/lc q)·q, où α = lm p,
-- β = lm q et γ = α∨β (② Définition 1) : les deux têtes hissées au
-- coin commun se superposent et s'annulent — lm(Spol(p, q)) ≺ γ.
-- Précondition : p et q non nuls (la tête doit exister).
{-# INLINABLE spol #-}
-- SNIPPET:groebner-spol
-- NOTE:Field: S corps — annuler une tête inverse son coefficient de tête (E.quot, plus bas) ; l'hypothèse de tout l'arc
-- NOTE:sup: γ = α ∨ β, multiple commun par construction — la soustraction minus est donc totale ici (loi jugée chez les ordres)
spol :: (MonomialOrder o, Field s, Ring s, Eq s)
     => MPoly o s -> MPoly o s -> MPoly o s
spol p q = case (leading p, leading q) of
  (Just (am, ac), Just (bm, bc)) ->
    let gamma = sup (toExp am) (toExp bm)
    in (hisse gamma am ac `times` p)
         `plus` negate (hisse gamma bm bc `times` q)
  _ -> error "cauchy-groebner : spol — la tête d'un polynôme nul n'existe pas"
  where
    -- x^(γ−α)/c : le monôme qui hisse la tête (α, c) au coin γ ; la
    -- soustraction est totale ici — γ est un multiple commun par
    -- construction ('sup' est un majorant, loi jugée chez cauchy-order).
    hisse gamma m c = case gamma `minus` toExp m of
      Just d  -> fromTerms [(fromExp d, one `E.quot` c)]
      Nothing -> error "cauchy-groebner : spol — α∨β n'est pas un multiple commun"
-- END:groebner-spol

-- | Le critère de Buchberger (② Théorème 1) : G est une base de
-- Gröbner si et seulement si Spol(dᵢ, dⱼ) →G 0 pour chacune des
-- s(s−1)\/2 paires — le test infini de la définition devenu fini.
{-# INLINABLE isGroebner #-}
-- SNIPPET:groebner-isgroebner
-- NOTE:tails: chaque paire non ordonnée une fois — les s(s−1)/2 du critère, le test infini de la définition rendu fini
isGroebner :: (MonomialOrder o, Field s, Ring s, Eq s)
           => [MPoly o s] -> Bool
isGroebner gs0 =
  and [ nf (spol a b) gs == zero | (a : bs) <- tails gs, b <- bs ]
  where
    gs = filter (/= zero) gs0
-- END:groebner-isgroebner

-- | La complétion (③ Théorèmes 1 et 2) : chaque échec du critère —
-- un reste non nul de la réduction de Spol(dᵢ, dⱼ) — est adjoint à
-- G ; chaque adjonction agrandit strictement ⟨lm G⟩ et le lemme de
-- Dickson force l'arrêt. La sortie engendre le même idéal que
-- l'entrée et passe le critère : une base de Gröbner de ⟨F⟩.
--
-- Les élagages, sans effet sur le contrat : l'adjonction élague les
-- paires à la Gebauer–Möller — coins strictement couverts (M), un
-- seul par coin (F), têtes premières entre elles (le premier critère
-- de ② : γ = α + β ⟺ Spol →{p,q} 0), paires anciennes dont le coin
-- est couvert par la tête nouvelle (B) ; la file et le choix du
-- réducteur suivent le degré fantôme — le /sucre/ de Giovini, Mora,
-- Niesi, Robbiano et Traverso (1991), le degré qu'aurait le calcul
-- homogénéisé — sans quoi les coefficients intermédiaires sur ℚ
-- explosent (cyclic-6 : 10⁴ chiffres constatés contre 10¹ au but).
-- Chaque générateur est normalisé à lc = 1 — l'idéal n'en bouge pas.
{-# INLINABLE buchberger #-}
-- SNIPPET:groebner-buchberger
-- NOTE:complete: la descente n'est bornée par aucun type — Dickson la prouve, GHC l'ignore ; chaque exécution verte la constate
buchberger :: (MonomialOrder o, Field s, Ring s, Eq s)
           => [MPoly o s] -> [MPoly o s]
buchberger fs = complete (foldl adjoint (Etat 0 [] [] []) entrees)
  where
    entrees = [ (monic f, degTotal f) | f <- filter (/= zero) fs ]
    valeur e i = case lookup i (eBase e) of
      Just ps -> ps
      Nothing -> error "cauchy-groebner : buchberger — indice inconnu"
    reducs e = [ valeur e i | i <- eReducs e ]
    complete e = case ePaires e of
      [] -> map (fst . snd) (eBase e)
      ((cle, (i, j)) : reste) ->
        let (a, _) = valeur e i
            (b, _) = valeur e j
            (r, sr) = reduit (reducs e) (spol a b) (fst cle)
            e' = e { ePaires = reste }
        in if r == zero
             then complete e'
             else complete (adjoint e' (monic r, sr))
-- END:groebner-buchberger
    -- L'adjonction de h : la base s'allonge (rien n'en sort, l'indice
    -- est l'identité), les réducteurs à tête couverte s'effacent, les
    -- paires nouvelles sont élaguées (M, F, premier critère), les
    -- anciennes filtrées (B), la file fusionnée par (sucre, degré du
    -- coin) croissant.
    adjoint e (h, sh) = Etat
      { eSuivant = n + 1
      , eBase    = eBase e ++ [(n, (h, sh))]
      , eReducs  = [ i | i <- eReducs e
                   , not (th `divides` teteDe i) ] ++ [n]
      , ePaires  = fusion vieilles (sortOn fst nouvelles)
      }
      where
        n = eSuivant e
        th = tete h
        teteDe i = tete (fst (valeur e i))
        coinDe i = sup (teteDe i) th
        sucreDe i =
          let (_, si) = valeur e i
              c = coinDe i
          in max (totalDegree c - totalDegree (teteDe i) + si)
                 (totalDegree c - totalDegree th + sh)
        cand = [ (coinDe i, i) | (i, _) <- eBase e ]
        -- M : un coin strictement divisé par un autre coin est superflu.
        survM = [ cg | cg@(c, _) <- cand
                , not (any (\(c', _) -> c' /= c && c' `divides` c) cand) ]
        -- F : un seul représentant par coin — de préférence un à têtes
        -- premières entre elles, que le premier critère éliminera.
        unParCoin [] = []
        unParCoin (cg@(c, _) : reste) =
          let (memes, autres) = partition ((== c) . fst) reste
              premiers = [ cg' | cg'@(_, i) <- cg : memes
                         , c == teteDe i <> th ]
          in (case premiers of p : _ -> p; [] -> cg) : unParCoin autres
        -- Premier critère : γ = α + β ⟺ têtes premières entre elles.
        nouvelles = [ ((sucreDe i, totalDegree c), (i, n))
                    | (c, i) <- unParCoin survM
                    , c /= teteDe i <> th ]
        -- B : une paire ancienne dont le coin est multiple de la tête
        -- de h — sans être le coin d'aucune des deux paires avec h —
        -- est couverte par celles-ci.
        vieilles = [ p | p@(_, (i, j)) <- ePaires e
                   , let c = sup (teteDe i) (teteDe j)
                   , not (th `divides` c && coinDe i /= c && coinDe j /= c) ]
        fusion xs [] = xs
        fusion [] ys = ys
        fusion (x : xs) (y : ys)
          | fst x <= fst y = x : fusion xs (y : ys)
          | otherwise      = y : fusion (x : xs) ys

-- L'état de la complétion : compteur d'indices, base associative
-- (l'indice est l'identité — les paires y réfèrent —, la tête est
-- immuable, le sucre accompagne la valeur), réducteurs (indices à
-- tête non couverte par une tête plus récente — les seuls utiles pour
-- réduire), file de paires triée par clé (sucre, degré du coin).
data Etat o s = Etat
  { eSuivant :: Int
  , eBase    :: [(Int, (MPoly o s, Natural))]
  , eReducs  :: [Int]
  , ePaires  :: [((Natural, Natural), (Int, Int))]
  }

-- Réduction complète guidée par le sucre : à chaque pas, parmi les
-- réducteurs dont la tête divise, celui de moindre bond de sucre — à
-- bond égal, le plus court. Le reste rendu n'a aucun terme divisible
-- par une tête de la liste (même garantie que 'division') ; le sucre
-- rendu majore le degré du calcul homogénéisé.
{-# INLINABLE reduit #-}
reduit :: (MonomialOrder o, Field s, Ring s, Eq s)
       => [(MPoly o s, Natural)] -> MPoly o s -> Natural
       -> (MPoly o s, Natural)
reduit gs = go zero
  where
    go r f sf = case leading f of
      Nothing -> (r, sf)
      Just (m, c) ->
        let cands = [ (bond, length (toTerms g), d, g, lcg)
                    | (g, sg) <- gs
                    , Just (lmg, lcg) <- [leading g]
                    , Just d <- [toExp m `minus` toExp lmg]
                    , let bond = totalDegree d + sg ]
            lt = fromTerms [(m, c)]
        in case cands of
             [] -> go (r `plus` lt) (f `plus` negate lt) sf
             _  ->
               let (bond, _, d, g, lcg) =
                     minimumBy (comparing (\(b, t, _, _, _) -> (b, t))) cands
                   q = fromTerms [(fromExp d, c `E.quot` lcg)]
               in go r (f `plus` negate (q `times` g)) (max sf bond)

-- | L'inter-réduction (③ Théorème 3) : chaque générateur réduit par
-- les autres, têtes normalisées à lc = 1, générateurs superflus
-- écartés. Sur une base de Gröbner, la sortie est LA base réduite —
-- unique à ordre fixé ; l'idéal gagne un représentant canonique et
-- l'égalité d'idéaux un test décidable.
{-# INLINABLE reduce #-}
-- SNIPPET:groebner-reduce
-- NOTE:monic: chaque générateur réduit par les autres puis normalisé à lc = 1 ; sur une base de Gröbner, la sortie est LA base réduite, unique à ordre fixé
reduce :: (MonomialOrder o, Field s, Ring s, Eq s)
       => [MPoly o s] -> [MPoly o s]
reduce gs0 = [ monic (rednf g (sauf i)) | (i, g) <- indexes ]
-- END:groebner-reduce
  where
    -- Le chemin de réduction est libre ici, bien que « sauf i » ne
    -- soit pas une base de Gröbner : deux formes pleinement réduites
    -- r et r′ de g modulo les autres gardés ont la même tête lm(g)
    -- (couverte par aucun autre gardé) à coefficient égal, et aucun
    -- terme divisible par une tête de l'ensemble gardé — qui engendre
    -- ⟨lm I⟩ quand l'entrée est une base de Gröbner ; r − r′ ∈ I sans
    -- terme dans ⟨lm I⟩ est nul. La version guidée par le sucre rend
    -- donc le même reste que 'nf', par un chemin qui contient les
    -- coefficients. C'est le duel décisif (ensemble contre ensemble,
    -- redSB du référent) qui en témoigne — pas ce commentaire.
    rednf g hs = fst (reduit [ (h, degTotal h) | h <- hs ] g (degTotal g))
    -- Écarte tout générateur dont la tête est couverte par celle d'un
    -- autre encore en lice — à têtes égales, un seul survit.
    garde acc [] = reverse acc
    garde acc (g : rest)
      | any ((`divides` tete g) . tete) (acc ++ rest) = garde acc rest
      | otherwise = garde (g : acc) rest
    kept = garde [] (filter (/= zero) gs0)
    indexes = zip [0 :: Int ..] kept
    sauf i = [ h | (j, h) <- indexes, j /= i ]

-- | La coupe (④ Théorème 1) : @cut j G@ garde les éléments de G qui
-- ne mentionnent aucune des j premières indéterminées. Si G est une
-- base de Gröbner pour un ordre qui élimine x₁ … xⱼ (lex l'est pour
-- chaque j), la coupe est une base de Gröbner de l'idéal
-- d'élimination Iⱼ = ⟨G⟩ ∩ S[xⱼ₊₁, …, xₖ] — la projection, calculée.
-- Sans cette hypothèse d'ordre la coupe peut manquer Iⱼ (grevlex,
-- témoin de ④).
{-# INLINABLE cut #-}
-- SNIPPET:groebner-cut
-- NOTE:take: garde les générateurs sans aucune des j premières indéterminées — une base de Iⱼ seulement si l'ordre élimine x₁…xⱼ (lex oui, grevlex non, témoin y² − xz)
cut :: MonomialOrder o => Int -> [MPoly o s] -> [MPoly o s]
cut j = filter (all sans . toTerms)
  where
    sans (m, _) = all (== 0) (take j (components (toExp m)))
-- END:groebner-cut

-- | L'exposant de tête d'un polynôme non nul — le vocabulaire interne
-- de la complétion.
{-# INLINABLE tete #-}
tete :: MonomialOrder o => MPoly o s -> Exp (Arity o)
tete p = case leading p of
  Just (m, _) -> toExp m
  Nothing     -> error "cauchy-groebner : tête d'un polynôme nul"

-- | Tête normalisée à lc = 1 (S corps : lc s'inverse) — l'idéal
-- engendré n'en bouge pas, les coefficients restent contenus.
{-# INLINABLE monic #-}
monic :: (MonomialOrder o, Field s, Ring s, Eq s) => MPoly o s -> MPoly o s
monic p = case leading p of
  Nothing     -> p
  Just (_, c) -> fromTerms [ (m, b `E.quot` c) | (m, b) <- toTerms p ]

-- | Le degré total — le sucre initial d'un générateur.
{-# INLINABLE degTotal #-}
degTotal :: MonomialOrder o => MPoly o s -> Natural
degTotal p = maximum (0 : [ totalDegree (toExp m) | (m, _) <- toTerms p ])
