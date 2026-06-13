-- | L'oracle de la phase 2 : les onze lignes CONTRAT des pages ①②③④,
-- réalisées en duels exécutables — au rouge, chaque duel échouait par
-- l'@error@ du squelette ; au vert, tous passent.
--
-- ① lois de S⟨Σ⟩ ×4 (Bool, ℕ, Trop, M₂(Bool) — non commutatif) ;
--   ∗ sur Bool⟨Σ⟩ ≡ concaténation ensembliste naïve ; h_σ morphisme
--   (la liberté, Théorème 2, testée — sur S commutatif : l'hypothèse
--   de centralité du théorème).
-- ② lois de S⟨⟨Σ⟩⟩ sur sections (|w| ≤ n) ×4 ; Leibniz
--   ∂ₐ(p∗q) = ∂ₐp ∗ q + ν(p)·∂ₐq et observation p(w) = ν(∂_w p)
--   contre le coefficient direct, aussi sur M₂(Bool) — le côté de
--   l'action scalaire est jugé en non-commutatif ; étoile gardée
--   ∂ₐ(p*) = ∂ₐp ∗ p* sur sommes gardées à lettres mêlées.
-- ③ filtre ν(∂_w e) : regex-applicative (le moteur de référence,
--   tranché 2026-06-12) ET la sémantique des langages à la main jugent
--   la même entrée — leur désaccord est une panne bruyante du harnais,
--   pas un contre-exemple ; at ∘ denote ≡ match (S = Bool) ;
--   saturation de l'automate des dérivées (états finis modulo ACI).
-- ④ distance ≡ Bellman-Ford à la main dans M₆(Trop), poids ≥ 0 ;
--   comptage sur DAG ≡ programmation dynamique à la main dans M₆(ℕ) ;
--   axiome de l'étoile star m = 1 + m ∗ star m dans M₃(M₂(Bool)).
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Control.Applicative (empty, many, (<|>))
import Control.Monad (replicateM, unless)
import Data.List (nub, sortBy)
import Data.Maybe (isJust)
import Data.Monoid (Sum (..))
import Data.Ord (comparing)
import Numeric.Natural (Natural)
import System.Exit (exitFailure)

import Test.Cauchy.Oracle (Duel (..), Verdict, lawDuel, pureReferee, runDuel, runSuite)
import Test.QuickCheck

import Data.Semiring (Semiring (..))
import Data.Semiring.Tropical (Tropical (..))
import Data.Star (Star (..))

import qualified Text.Regex.Applicative as RE

import qualified Data.Cauchy.Language.Poly as CP
import qualified Data.Cauchy.Language.Rational as CR
import qualified Data.Cauchy.Language.Series as CS
import qualified Data.Cauchy.Language.Weighted as CW

import Showcase (AB (..), Trop, coutMinimal, decoupages, sigma)

-- ---------------------------------------------------------------------
-- L'alphabet AB et les instances S du panorama vivent dans Showcase
-- (avec les définitions d'exposition de la vitrine, jugées ci-dessous).
-- Trop = (ℕ ∪ {∞}, min, +) : à poids ≥ 0 — et Natural ne porte que
-- ceux-là — boucler ne diminue jamais un coût : la frontière
-- d'hypothèses de ④.

toTrop :: Maybe Natural -> Trop
toTrop = maybe Infinity (Tropical . Sum)

unTrop :: Trop -> Maybe Natural
unTrop Infinity         = Nothing
unTrop (Tropical (Sum n)) = Just n

-- ℕ pour le comptage ; l'étoile n'y est licite que sur un argument nul
-- (DAG : matrice nilpotente, diagonale nulle) — toute autre étoile est
-- un cycle pondéré, déclaré divergent, l'autre bord de la frontière.
newtype Count = Count Natural deriving (Eq, Show)

unCount :: Count -> Natural
unCount (Count n) = n

instance Semiring Count where
  zero = Count 0
  one  = Count 1
  plus  (Count a) (Count b) = Count (a + b)
  times (Count a) (Count b) = Count (a * b)

instance Star Count where
  star (Count 0) = one
  star c = error ("étoile divergente dans ℕ : " ++ show c)

-- SNIPPET:lang-duel-b2
-- M₂(Bool) à la main : le plus petit S non commutatif des duels
-- (e₁₂·e₂₁ ≠ e₂₁·e₁₂) — c'est lui qui rend observable le côté de
-- l'action scalaire (ν(p)·∂ₐq de Leibniz, scale de subst) et l'ordre
-- des facteurs matriciels. Indépendant de CW.Matrix, le code jugé.
newtype B2 = B2 (Bool, Bool, Bool, Bool) deriving (Eq, Show)

instance Semiring B2 where
  zero = B2 (False, False, False, False)
  one  = B2 (True, False, False, True)
  plus  (B2 (a, b, c, d)) (B2 (a', b', c', d')) =
    B2 (a || a', b || b', c || c', d || d')
  times (B2 (a, b, c, d)) (B2 (a', b', c', d')) =
    B2 ( (a && a') || (b && c'), (a && b') || (b && d')
       , (c && a') || (d && c'), (c && b') || (d && d') )

-- L'étoile par point fixe : plus est idempotente et le porteur fini,
-- la suite 1, 1+a·s, … est croissante et stationne.
instance Star B2 where
  star a = go one
    where
      go s = let s' = one `plus` (a `times` s) in if s' == s then s else go s'
-- END:lang-duel-b2

genB2 :: Gen B2
genB2 = B2 <$> ((,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)

-- ---------------------------------------------------------------------
-- Générateurs : des descriptions finies, jamais des porteurs.
-- lawDuel appartient au harnais depuis la phase 3 ; la réplique locale
-- est fusionnée (vitrine, 2026-06-12). Les rétrécisseurs produits
-- répliquent encore ceux de cauchy-poly/test/Duels.hs — fusion le jour
-- où cauchy-oracle les possédera.

genN :: Gen Natural
genN = fromInteger <$> choose (0, 9)

genT :: Gen Trop
genT = frequency [(1, pure Infinity), (3, Tropical . Sum <$> genN)]

genWordUpTo :: Int -> Gen [AB]
genWordUpTo n = do k <- choose (0, n); vectorOf k (elements sigma)

genTerms :: Gen s -> Gen [([AB], s)]
genTerms gs = do n <- choose (0, 4); vectorOf n ((,) <$> genWordUpTo 3 <*> gs)

shrinkTerms :: [([AB], s)] -> [[([AB], s)]]
shrinkTerms = shrinkList (const [])

shrinkPair :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair sa sb (a, b) = [(a', b) | a' <- sa a] ++ [(a, b') | b' <- sb b]

shrinkTriple :: (a -> [a]) -> (b -> [b]) -> (c -> [c]) -> (a, b, c) -> [(a, b, c)]
shrinkTriple sa sb sc (a, b, c) =
     [(a', b, c) | a' <- sa a]
  ++ [(a, b', c) | b' <- sb b]
  ++ [(a, b, c') | c' <- sc c]

-- Les coupures d'un mot : la fibre uv = w, |w|+1 éléments — l'énoncé
-- de ①, utilisé par les référents à la main.
splits :: [a] -> [([a], [a])]
splits w = [splitAt k w | k <- [0 .. length w]]

shortlex :: [[AB]] -> [[AB]]
shortlex = sortBy (comparing (\w -> (length w, w)))

sumS :: Semiring s => [s] -> s
sumS = foldr plus zero

-- ---------------------------------------------------------------------
-- ① — lois de S⟨Σ⟩ ×3 ; ∗ ≡ concaténation ensembliste ; h_σ morphisme.

-- | Les sept lois du noyau, pour une instance S nommée. L'égalité est
-- celle du type (représentation canonique, décidable).
polyLaws :: (Show s, Eq s, Semiring s) => String -> Gen s -> [IO Verdict]
polyLaws inst gs =
  [ run "plus-assoc"   (\p q r -> ((p .+. q) .+. r) == (p .+. (q .+. r)))
  , run "plus-comm"    (\p q _ -> (p .+. q) == (q .+. p))
  , run "plus-zero"    (\p _ _ -> (p .+. zero) == p)
  , run "times-assoc"  (\p q r -> ((p .*. q) .*. r) == (p .*. (q .*. r)))
  , run "times-one"    (\p _ _ -> ((p .*. one) == p) && ((one .*. p) == p))
  , run "distrib"      (\p q r -> (p .*. (q .+. r)) == ((p .*. q) .+. (p .*. r))
                              && ((q .+. r) .*. p) == ((q .*. p) .+. (r .*. p)))
  , run "annihilation" (\p _ _ -> ((zero .*. p) == zero) && ((p .*. zero) == zero))
  ]
  where
    (.+.) = plus
    (.*.) = times
    gen3 = (,,) <$> genTerms gs <*> genTerms gs <*> genTerms gs
    shr3 = shrinkTriple shrinkTerms shrinkTerms shrinkTerms
    run nm law = runDuel 300 $
      lawDuel ("S⟨Σ⟩ " ++ inst ++ " : " ++ nm) gen3 shr3
              (\(ta, tb, tc) ->
                 law (CP.fromTerms ta) (CP.fromTerms tb) (CP.fromTerms tc))

genWordSet :: Gen [[AB]]
genWordSet = do n <- choose (0, 4); nub <$> vectorOf n (genWordUpTo 3)

-- | Bool⟨Σ⟩ est l'algèbre des langages finis : ∗ doit être la
-- concaténation ensembliste, énumérée naïvement par le référent.
duelConcatSets :: Duel ([[AB]], [[AB]]) [([AB], Bool)]
duelConcatSets = Duel
  { duelName  = "(∗) sur Bool⟨Σ⟩"
  , generator = (,) <$> genWordSet <*> genWordSet
  , shrinker  = shrinkPair (shrinkList (const [])) (shrinkList (const []))
  , candidate = \(ps, qs) -> CP.toTerms (asSet ps `times` asSet qs)
  , referee   = pureReferee "concaténation ensembliste naïve" $ \(ps, qs) ->
      [ (w, True) | w <- shortlex (nub [u ++ v | u <- ps, v <- qs]) ]
  }
  where
    asSet ws = CP.fromTerms [(w, True) | w <- ws] :: CP.Poly AB Bool

-- | La liberté de Σ*, testée : h_σ = subst σ est un morphisme et
-- prolonge σ (l'unicité du Théorème 2 de ①).
duelSubst :: Duel ([([AB], Natural)], [([AB], Natural)],
                   ([([AB], Natural)], [([AB], Natural)])) Bool
duelSubst = lawDuel "h_σ : S⟨Σ⟩ → S⟨Σ⟩ morphisme prolongeant σ (S = ℕ)"
  ((,,) <$> genTerms genN <*> genTerms genN
        <*> ((,) <$> genTerms genN <*> genTerms genN))
  (shrinkTriple shrinkTerms shrinkTerms (shrinkPair shrinkTerms shrinkTerms))
  (\(tp, tq, (ta, tb)) ->
     let p = CP.fromTerms tp
         q = CP.fromTerms tq
         sg A = CP.fromTerms ta
         sg B = CP.fromTerms tb
         h = CP.subst sg
     in h (p `plus` q) == (h p `plus` h q)
        && h (p `times` q) == (h p `times` h q)
        && h one == one
        && h (CP.letter A) == sg A
        && h (CP.letter B) == sg B)

-- ---------------------------------------------------------------------
-- ② — lois de S⟨⟨Σ⟩⟩ sur sections ; Leibniz ; observation ; étoile
-- gardée.
--
-- Les séries d'entrée sont tirées comme descriptions inductives finies
-- puis dépliées ; l'égalité est celle des sections |w| ≤ n — la seule
-- observation du type.

-- SNIPPET:lang-duel-desc
data Desc s
  = DPoly [([AB], s)]
  | DPlus  (Desc s) (Desc s)
  | DTimes (Desc s) (Desc s)
  | DStarG [(AB, Desc s)]     -- star (Σ letter aᵢ ∗ dᵢ), liste non vide :
                              -- la garde par construction, lettres mêlées
  deriving Show

-- | Σ letter aᵢ ∗ qᵢ : gardée par construction (ν = 0).
guardedSum :: (Eq s, Semiring s) => [(AB, CS.Series AB s)] -> CS.Series AB s
guardedSum ps = foldr1 plus [ CS.fromPoly (CP.letter l) `times` q | (l, q) <- ps ]

interp :: (Eq s, Semiring s) => Desc s -> CS.Series AB s
interp (DPoly ts)    = CS.fromPoly (CP.fromTerms ts)
interp (DPlus a b)   = interp a `plus` interp b
interp (DTimes a b)  = interp a `times` interp b
interp (DStarG ps)   = star (guardedSum [ (l, interp d) | (l, d) <- ps ])
-- END:lang-duel-desc

genDesc :: Gen s -> Gen (Desc s)
genDesc gs = go (2 :: Int)
  where
    leaf = DPoly <$> genTerms gs
    go 0 = leaf
    go d = frequency
      [ (3, leaf)
      , (2, DPlus  <$> go (d - 1) <*> go (d - 1))
      , (2, DTimes <$> go (d - 1) <*> go (d - 1))
      , (1, do k <- choose (1, 2)
               DStarG <$> vectorOf k ((,) <$> elements sigma <*> go (d - 1)))
      ]

shrinkDesc :: Desc s -> [Desc s]
shrinkDesc (DPoly ts)   = map DPoly (shrinkTerms ts)
shrinkDesc (DPlus a b)  = [a, b] ++ [DPlus a' b | a' <- shrinkDesc a]
                                 ++ [DPlus a b' | b' <- shrinkDesc b]
shrinkDesc (DTimes a b) = [a, b] ++ [DTimes a' b | a' <- shrinkDesc a]
                                 ++ [DTimes a b' | b' <- shrinkDesc b]
shrinkDesc (DStarG ps)  = map snd ps
  ++ [ DStarG ps' | ps' <- shrinkList (const []) ps, not (null ps') ]

-- | Longueur d'observation des sections.
sectionLen :: Int
sectionLen = 4

wordsUpTo :: Int -> [[AB]]
wordsUpTo n = concatMap (\k -> replicateM k sigma) [0 .. n]

-- | L'égalité des sections finies par longueur.
(=~=) :: (Eq s, Semiring s) => CS.Series AB s -> CS.Series AB s -> Bool
u =~= v = all (\w -> CS.at w u == CS.at w v) (wordsUpTo sectionLen)

-- | Les sept lois, sur sections, pour une instance S nommée.
seriesLaws :: (Show s, Eq s, Semiring s) => String -> Gen s -> [IO Verdict]
seriesLaws inst gs =
  [ run "plus-assoc"   (\a b c -> ((a .+. b) .+. c) =~= (a .+. (b .+. c)))
  , run "plus-comm"    (\a b _ -> (a .+. b) =~= (b .+. a))
  , run "plus-zero"    (\a _ _ -> (a .+. zero) =~= a)
  , run "times-assoc"  (\a b c -> ((a .*. b) .*. c) =~= (a .*. (b .*. c)))
  , run "times-one"    (\a _ _ -> ((a .*. one) =~= a) && ((one .*. a) =~= a))
  , run "distrib"      (\a b c -> (a .*. (b .+. c)) =~= ((a .*. b) .+. (a .*. c))
                              && ((b .+. c) .*. a) =~= ((b .*. a) .+. (c .*. a)))
  , run "annihilation" (\a _ _ -> ((zero .*. a) =~= zero) && ((a .*. zero) =~= zero))
  ]
  where
    (.+.) = plus
    (.*.) = times
    gen3 = (,,) <$> genDesc gs <*> genDesc gs <*> genDesc gs
    shr3 = shrinkTriple shrinkDesc shrinkDesc shrinkDesc
    run nm law = runDuel 300 $
      lawDuel ("S⟨⟨Σ⟩⟩ " ++ inst ++ " : " ++ nm) gen3 shr3
              (\(a, b, c) -> law (interp a) (interp b) (interp c))

-- Au vert, le produit de Series est /défini/ par Leibniz : ce duel ne
-- teste plus un théorème mais la cohérence de la plomberie
-- delta/at/times. L'ancre externe de ② est duelObservation, contre le
-- coefficient calculé à la main. L'instance M₂(Bool) rend observable
-- le côté de l'action scalaire ν(p)·∂ₐq.
duelLeibniz :: (Show s, Eq s, Semiring s)
            => String -> Gen s -> Duel (AB, Desc s, Desc s) Bool
duelLeibniz inst gs =
  lawDuel ("Leibniz : ∂ₐ(p∗q) = ∂ₐp ∗ q + ν(p)·∂ₐq (S = " ++ inst ++ ")")
  ((,,) <$> elements sigma <*> genDesc gs <*> genDesc gs)
  (shrinkTriple (const []) shrinkDesc shrinkDesc)
  (\(a, dp, dq) ->
     let p = interp dp
         q = interp dq
         nup = CS.fromPoly (CP.fromTerms [([], CS.nu p)])
     in CS.delta a (p `times` q)
          =~= ((CS.delta a p `times` q) `plus` (nup `times` CS.delta a q)))

-- Le coefficient direct, calculé à la main par récurrence sur la
-- description et les coupures — le référent du rouge, indépendant du
-- squelette jugé.
coeffD :: Semiring s => Desc s -> [AB] -> s
coeffD (DPoly ts) w   = sumS [c | (u, c) <- ts, u == w]
coeffD (DPlus a b) w  = coeffD a w `plus` coeffD b w
coeffD (DTimes a b) w = sumS [ coeffD a u `times` coeffD b v
                             | (u, v) <- splits w ]
coeffD (DStarG ps) w = go w
  where
    hd []       = zero
    hd (c : cs) = sumS [ coeffD d cs | (l, d) <- ps, l == c ]
    go [] = one
    go u  = sumS [ hd p `times` go q | (p, q) <- splits u, not (null p) ]

duelObservation :: (Show s, Eq s, Semiring s)
                => String -> Gen s -> Duel (Desc s, [AB]) (s, s)
duelObservation inst gs = Duel
  { duelName  = "observation : p(w) = ν(∂_w p) (S = " ++ inst ++ ")"
  , generator = (,) <$> genDesc gs <*> genWordUpTo 4
  , shrinker  = shrinkPair shrinkDesc (const [])
  , candidate = \(d, w) ->
      let p = interp d
      in (CS.at w p, CS.nu (foldl (flip CS.delta) p w))
  , referee   = pureReferee "coefficient direct (à la main)" $ \(d, w) ->
      let c = coeffD d w in (c, c)
  }

duelStarGuard :: (Show s, Eq s, Semiring s)
              => String -> Gen s -> Duel (AB, [(AB, Desc s)]) Bool
duelStarGuard inst gs =
  lawDuel ("étoile gardée : ∂ₐ(p*) = ∂ₐp ∗ p* (ν p = 0, S = " ++ inst ++ ")")
  ((,) <$> elements sigma
       <*> (choose (1, 2) >>= \k ->
              vectorOf k ((,) <$> elements sigma <*> genDesc gs)))
  (shrinkPair (const [])
              (\ps -> [ ps' | ps' <- shrinkList (const []) ps, not (null ps') ]))
  (\(a, ps) ->
     let p = guardedSum [ (l, interp d) | (l, d) <- ps ]  -- gardée par construction
     in CS.delta a (star p) =~= (CS.delta a p `times` star p))

-- ---------------------------------------------------------------------
-- ③ — le filtre contre la sémantique des langages ; la saturation de
-- l'automate des dérivées.

genExpr :: Gen (CR.Expr AB)
genExpr = go (3 :: Int)
  where
    leaf = frequency
      [ (1, pure CR.EZero)
      , (2, pure CR.EOne)
      , (4, CR.ELetter <$> elements sigma)
      ]
    go 0 = leaf
    go d = frequency
      [ (3, leaf)
      , (2, CR.EPlus  <$> go (d - 1) <*> go (d - 1))
      , (2, CR.ETimes <$> go (d - 1) <*> go (d - 1))
      , (1, CR.EStar  <$> go (d - 1))
      ]

shrinkExpr :: CR.Expr AB -> [CR.Expr AB]
shrinkExpr (CR.EPlus a b)  = [a, b] ++ [CR.EPlus a' b | a' <- shrinkExpr a]
                                    ++ [CR.EPlus a b' | b' <- shrinkExpr b]
shrinkExpr (CR.ETimes a b) = [a, b] ++ [CR.ETimes a' b | a' <- shrinkExpr a]
                                    ++ [CR.ETimes a b' | b' <- shrinkExpr b]
shrinkExpr (CR.EStar a)    = [a] ++ map CR.EStar (shrinkExpr a)
shrinkExpr _               = []

-- Le moteur de référence, tranché à la porte des bibliothèques du
-- vert (2026-06-12) : regex-applicative — symbole polymorphe (il juge
-- directement sur AB), simulation de type NFA, algorithmiquement
-- indépendant des dérivées du candidat.
toRE :: CR.Expr AB -> RE.RE AB ()
toRE CR.EZero        = empty
toRE CR.EOne         = pure ()
toRE (CR.ELetter a)  = () <$ RE.sym a
toRE (CR.EPlus e f)  = toRE e <|> toRE f
toRE (CR.ETimes e f) = toRE e *> toRE f
toRE (CR.EStar e)    = () <$ many (toRE e)

-- La sémantique des langages, par récurrence sur la syntaxe et les
-- coupures du mot — le référent à la main du rouge, second juge du
-- même duel : les deux référents jugent la même entrée et leur
-- désaccord lève une panne bruyante du harnais, pas un contre-exemple.
inLang :: CR.Expr AB -> [AB] -> Bool
inLang CR.EZero _       = False
inLang CR.EOne w        = null w
inLang (CR.ELetter a) w = w == [a]
inLang (CR.EPlus e f) w = inLang e w || inLang f w
inLang (CR.ETimes e f) w =
  any (\(u, v) -> inLang e u && inLang f v) (splits w)
inLang (CR.EStar e) w =
  null w || any (\(u, v) -> not (null u) && inLang e u && inLang (CR.EStar e) v)
                (splits w)

-- SNIPPET:lang-duel-filtre
duelFiltre :: Duel (CR.Expr AB, [AB]) Bool
duelFiltre = Duel
  { duelName  = "filtre : ν(∂_w e)"
  , generator = (,) <$> genExpr <*> genWordUpTo 6
  , shrinker  = shrinkPair shrinkExpr (shrinkList (const []))
  , candidate = uncurry CR.match
  , referee   = pureReferee "regex-applicative ∧ sémantique (désaccord = panne)" $
      \(e, w) ->
        let r1 = isJust (RE.match (toRE e) w)
            r2 = inLang e w
        in if r1 /= r2
             then error ("désaccord entre référents sur " ++ show (e, w))
             else r1
  }
-- END:lang-duel-filtre

-- denote, exportée et montrée en vitrine, entre dans la boucle : sa
-- série caractéristique sur Bool doit coïncider avec le filtre.
duelDenote :: Duel (CR.Expr AB, [AB]) Bool
duelDenote = lawDuel "at w (denote e) = match e w (S = Bool)"
  ((,) <$> genExpr <*> genWordUpTo 6)
  (shrinkPair shrinkExpr (shrinkList (const [])))
  (\(e, w) -> CS.at w (CR.denote e :: CS.Series AB Bool) == CR.match e w)

-- La finitude de Brzozowski, constatée par construction : l'ensemble
-- rendu contient e, est sans doublon, et est clos par dérivation
-- modulo ACI — l'exploration a saturé.
duelSaturation :: Duel (CR.Expr AB) Bool
duelSaturation = lawDuel "dérivées mod ACI : saturation (états finis)"
  genExpr shrinkExpr $ \e ->
    let qs = CR.derivatives sigma e
    in CR.normACI e `elem` qs
       && length qs == length (nub qs)
       && all (\q -> all (\a -> CR.normACI (CR.deltaE a q) `elem` qs) sigma) qs

-- ---------------------------------------------------------------------
-- ④ — l'étoile de M₆(Trop) contre Bellman-Ford ; celle de M₆(ℕ) sur
-- DAG contre la programmation dynamique.

dim :: Int
dim = 6

upd :: Int -> Int -> a -> [[a]] -> [[a]]
upd i j x m =
  [ [ if (r, c) == (i, j) then x else e | (c, e) <- zip [0 ..] row ]
  | (r, row) <- zip [0 ..] m ]

genTropRows :: Gen [[Maybe Natural]]
genTropRows = vectorOf dim (vectorOf dim
  (frequency [(3, pure Nothing), (2, Just <$> genN)]))

-- Rétrécir = couper une arête (poids → ∞), jamais en inventer.
shrinkEdges :: [[Maybe Natural]] -> [[[Maybe Natural]]]
shrinkEdges m =
  [ upd i j Nothing m
  | i <- [0 .. dim - 1], j <- [0 .. dim - 1], isJust (m !! i !! j) ]

-- SNIPPET:lang-duel-bellman
-- Bellman-Ford à la main : depuis chaque source, dim tours de
-- relaxation ; Nothing = ∞.
minM :: Maybe Natural -> Maybe Natural -> Maybe Natural
minM Nothing y = y
minM x Nothing = x
minM (Just a) (Just b) = Just (min a b)

bellman :: [[Maybe Natural]] -> [[Maybe Natural]]
bellman g = [from i | i <- [0 .. dim - 1]]
  where
    from i = iterate relax start !! dim
      where
        start = [if j == i then Just 0 else Nothing | j <- [0 .. dim - 1]]
        relax d = [ foldr minM (d !! j)
                      [ addM (d !! k) (g !! k !! j) | k <- [0 .. dim - 1] ]
                  | j <- [0 .. dim - 1] ]
    addM (Just x) (Just y) = Just (x + y)
    addM _ _               = Nothing
-- END:lang-duel-bellman

duelDistance :: Duel [[Maybe Natural]] [[Maybe Natural]]
duelDistance = Duel
  { duelName  = "distance : étoile dans M₆(Trop), poids ≥ 0"
  , generator = genTropRows
  , shrinker  = shrinkEdges
  , candidate = \g ->
      map (map unTrop)
          (CW.toRows (star (CW.fromRows (map (map toTrop) g) :: CW.Matrix 6 Trop)))
  , referee   = pureReferee "Bellman-Ford (à la main)" bellman
  }

-- Un DAG par construction : des multiplicités au-dessus de la
-- diagonale seulement.
genDagRows :: Gen [[Natural]]
genDagRows =
  mapM (\i -> mapM (\j ->
          if j <= i then pure 0
          else frequency [(2, pure 0), (2, fromInteger <$> choose (1, 3))])
        [0 .. dim - 1])
       [0 .. dim - 1]

shrinkDag :: [[Natural]] -> [[[Natural]]]
shrinkDag m =
  [ upd i j 0 m
  | i <- [0 .. dim - 1], j <- [0 .. dim - 1], m !! i !! j /= 0 ]

-- SNIPPET:lang-duel-dag
-- La programmation dynamique à la main : le nombre de chemins i → j,
-- par récurrence sur le sommet de départ (le chemin vide compte pour
-- i = j — c'est le 1 de l'étoile).
dagPaths :: [[Natural]] -> [[Natural]]
dagPaths m = [[paths i j | j <- [0 .. dim - 1]] | i <- [0 .. dim - 1]]
  where
    paths i j
      | i == j    = 1
      | otherwise = sum [ (m !! i !! k) * paths k j | k <- [i + 1 .. dim - 1] ]
-- END:lang-duel-dag

duelComptage :: Duel [[Natural]] [[Natural]]
duelComptage = Duel
  { duelName  = "comptage : étoile dans M₆(ℕ) sur DAG"
  , generator = genDagRows
  , shrinker  = shrinkDag
  , candidate = \m ->
      map (map unCount)
          (CW.toRows (star (CW.fromRows (map (map Count) m) :: CW.Matrix 6 Count)))
  , referee   = pureReferee "programmation dynamique (à la main)" dagPaths
  }

-- L'axiome de l'étoile en non-commutatif : il juge l'ordre des
-- facteurs du pivot de Lehmann, que les duels à Trop et ℕ
-- (commutatifs) ne peuvent pas voir.
duelStarAxiom :: Duel [[B2]] Bool
duelStarAxiom = lawDuel "star m = 1 + m ∗ star m sur M₃(M₂(Bool))"
  (vectorOf 3 (vectorOf 3 genB2))
  (const [])
  (\rows ->
     let m = CW.fromRows rows :: CW.Matrix 3 B2
     in CW.toRows (star m) == CW.toRows (one `plus` (m `times` star m)))

-- ---------------------------------------------------------------------
-- Vitrine — les définitions d'exposition de ⑤ (test/Showcase.hs) sont
-- jugées comme le reste : ce que la page montre est ce que l'oracle
-- voit, et ce que le widget wasm exécute.

duelDecoupages :: Duel Int Natural
duelDecoupages = Duel
  { duelName  = "vitrine : (star (a+aa))(aⁿ) = découpages de aⁿ (S = ℕ)"
  , generator = choose (0, 12)
  , shrinker  = \n -> [0 .. n - 1]
  , candidate = \n -> CS.at (replicate n A) (decoupages :: CS.Series AB Natural)
  , referee   = pureReferee "récurrence des blocs a, aa (à la main)" comptage
  }
  where
    comptage n = d !! n
      where d = 1 : 1 : zipWith (+) d (tail d)

duelCoutMinimal :: Duel Int (Maybe Natural)
duelCoutMinimal = Duel
  { duelName  = "vitrine : (star (3·a ⊕ 5·aa))(aⁿ) = coût minimal (S = Trop)"
  , generator = choose (0, 12)
  , shrinker  = \n -> [0 .. n - 1]
  , candidate = \n -> unTrop (CS.at (replicate n A) coutMinimal)
  , referee   = pureReferee "programmation dynamique (à la main)" (Just . cout)
  }
  where
    cout :: Int -> Natural
    cout n = c !! n
      where c = 0 : 3 : zipWith min (map (3 +) (tail c)) (map (5 +) c)

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  let bitABit = 10000   -- « différentiel, 10⁴ cas » (①③)
  ok <- runSuite $
    -- ① lois ×3, concaténation ensembliste, liberté
    polyLaws "Bool" (arbitrary :: Gen Bool)
    ++ polyLaws "ℕ" genN
    ++ polyLaws "Trop" genT
    ++ polyLaws "M₂(Bool)" genB2
    ++ [ runDuel bitABit duelConcatSets
       , runDuel 1000    duelSubst
       ]
    -- ② lois sur sections ×4, Leibniz, observation, étoile gardée —
    -- M₂(Bool) rend observable le côté de l'action scalaire
    ++ seriesLaws "Bool" (arbitrary :: Gen Bool)
    ++ seriesLaws "ℕ" genN
    ++ seriesLaws "Trop" genT
    ++ seriesLaws "M₂(Bool)" genB2
    ++ [ runDuel 300  (duelLeibniz "ℕ" genN)
       , runDuel 300  (duelLeibniz "M₂(Bool)" genB2)
       , runDuel 1000 (duelObservation "ℕ" genN)
       , runDuel 500  (duelObservation "M₂(Bool)" genB2)
       , runDuel 300  (duelStarGuard "ℕ" genN)
       , runDuel 300  (duelStarGuard "M₂(Bool)" genB2)
       ]
    -- ③ filtre (deux référents sur la même entrée), denote, saturation
    ++ [ runDuel bitABit duelFiltre
       , runDuel 1000    duelDenote
       , runDuel 300     duelSaturation
       ]
    -- ④ distance, comptage, axiome de l'étoile en non-commutatif
    ++ [ runDuel 1000 duelDistance
       , runDuel 1000 duelComptage
       , runDuel 1000 duelStarAxiom
       ]
    -- vitrine : les définitions d'exposition de ⑤, jugées
    ++ [ runDuel 100 duelDecoupages
       , runDuel 100 duelCoutMinimal
       ]
  unless ok exitFailure
  putStrLn "PHASE 2 ORACLE: all green"
