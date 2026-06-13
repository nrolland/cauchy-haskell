-- | Le rouge du volet 5 : les treize lignes CONTRAT de
-- plan-backends.md (§oracle) en duels exécutables. Chaque duel doit
-- échouer tant que le squelette de Data.Cauchy.Backends lève @manque@
-- — c'est le constat recherché (plan-backends.md : « le rouge constate
-- les treize lignes en échec contre un squelette sans constructeur
-- avant le premier commit du vert »).
--
-- ① la transformée : l'aller-retour (1/n)·DFT_{ω⁻¹} ∘ DFT_ω = id sur
--   𝔽₁₇, n = 2^e ; le morphisme DFT(p ∗_cyc q) = DFT(p) ⊙ DFT(q) ; la
--   réduction linéaire→cyclique (rembourrage n > deg p + deg q) contre
--   la convolution du noyau, verte depuis le volet 0 ; le contre-exemple
--   ℤ/15, ω = 4 non principale ⇒ aller-retour ≠ id (témoin exhibé).
-- ② la FFT : bit-identique ntt ≡ dft puis chemin rapide ≡ chemin naïf à
--   10⁴ cas ; le compte exact M(n) = (n/2)·log₂ n (égalité, pas borne).
--   Le croisement des courbes est mesuré au vert (aucune mesure
--   anticipée — plan-backends.md §oracle ②).
-- ③ l'arithmétique exacte : convolveZ ≡ convolution entière naïve sous
--   la borne, recalculée par cas ; référent externe numpy.convolve ; le
--   garde-fou — un cas hors borne est détecté (Left), jamais rendu
--   faux ; l'ordre exact des racines des premiers retenus (ord ω = 2^e).
-- ④ F4 : nfF4 ≡ nf (la forme normale par échelonnage = par division) ;
--   la base de F4 ≡ la base réduite de Buchberger, ensemble contre
--   ensemble ; le duel décisif du volet 4 — base réduite contre
--   Singular std·redSB, cyclic-4..6 et katsura-3..5 générées par le
--   référent — rejoué tel quel avec F4. Le croisement F4/Buchberger est
--   mesuré au vert.
--
-- Le référent numpy est gardé par CAUCHY_ORACLE_NUMPY, les duels Singular par
-- CAUCHY_ORACLE_SINGULAR (sinon SKIP explicite). 'SingularGroebner' est
-- réutilisé tel quel depuis le volet 4 (note d'entrée §1 : « zéro ligne
-- nouvelle de harnais ») ; les générateurs/rétrécisseurs du multivarié
-- sont répliqués de MultiDuels (dette connue des volets 1–4, datée
-- 2026-06-13 — remboursement quand le harnais les possédera).
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- L'instance Arbitrary (Mod m) est orpheline à dessein : un générateur
-- du seul harnais, jamais exporté (le paquet 'mod' n'en fournit pas).
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import Control.Monad (unless)
import Data.List (sortOn)
import Data.Mod (Mod, invertMod)
import Data.Proxy (Proxy (..))
import Data.Ratio ((%))
import GHC.TypeLits (KnownNat, natVal)
import Numeric.Natural (Natural)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)

import Test.Cauchy.Oracle
  (BatchDuel (..), CertDuel (..), Duel (..), Referee (..), Verdict (..),
   chunked, lawDuel, processBatchReferee, pureReferee, runBatchDuel,
   runCertDuel, runDuel, runSuite)
import Test.QuickCheck

import Data.Semiring (Semiring (..))

import Data.Cauchy.Backends
import Data.Cauchy.Groebner (buchberger, nf, reduce)
import Data.Cauchy.Multi (MPoly, fromTerms, leading, toTerms)
import Data.Cauchy.Order (GrLex (..), GrevLex (..), Lex (..),
                          MonomialOrder (..), components, expo)
import Data.Cauchy.Poly (fromCoeffs, toCoeffs)

import SingularGroebner (TermL, familyRef, normalizeT, stdRedSBRefN)

-- ---------------------------------------------------------------------
-- Le porteur des transformées : ℤ/m via 'Data.Mod' (paquet 'mod', adopté
-- à la porte d'écosystème) — la dette du porteur vendorié au rouge (Zn,
-- powZn, recipZn de Fermat, écrits à la main) remboursée au vert :
-- 'Mod m' apporte 'Semiring'/'Num', et 'invertMod' (total) donne ω⁻¹ et
-- n⁻¹, sur 𝔽₁₇ (corps) comme sur ℤ/15 (composite, où Fermat échouerait).

-- | Tirage uniforme dans ℤ/m — instance orpheline, propre au harnais
-- (le paquet 'mod' n'en fournit pas).
instance KnownNat m => Arbitrary (Mod m) where
  arbitrary = fromInteger . toInteger <$> (arbitrary :: Gen Int)
  shrink _  = []

-- | L'inverse dans ℤ/m par 'invertMod' (total) : sur 𝔽₁₇ comme sur ℤ/15.
recipMod :: KnownNat m => Mod m -> Mod m
recipMod x = case invertMod x of
  Just y  -> y
  Nothing -> error "Duels : recipMod — élément non inversible"

-- | La donnée d'une racine principale d'ordre n = 2^e, dérivée d'un
-- générateur g de 𝔽_ℓ^× d'ordre multiplicatif @ordMul@ : ω = g^{ordMul/n}.
principalRoot :: KnownNat m => Mod m -> Integer -> Int -> Root (Mod m)
principalRoot g ordMul n = Root
  { rootOmega    = w
  , rootInvOmega = recipMod w
  , rootInvOrder = recipMod (fromIntegral n)
  , rootOrder    = n
  }
  where w = g ^ (ordMul `div` toInteger n)

-- | 𝔽₁₇ : 3 est racine primitive (ord 3 = 16), donc ω_n = 3^{16/n} est
-- principale d'ordre n pour tout n | 16.
root17 :: Int -> Root (Mod 17)
root17 = principalRoot 3 16

-- | Le contre-exemple « presque » de ① : dans ℤ/15, ω = 4 vérifie
-- ω² = 1, ω ≠ 1, 2 inversible — seule la principalité manque
-- (1 + 4 = 5 ≠ 0). Inverses par 'invertMod' (4⁻¹ = 4, 2⁻¹ = 8 mod 15).
-- L'aller-retour rend [10,1] sur [0,1] — une matrice ≠ id.
rootZ15 :: Root (Mod 15)
rootZ15 = Root 4 (recipMod 4) (recipMod 2) 2

-- ---------------------------------------------------------------------
-- Les chemins lents (référents de ①–③) et la plomberie arithmétique.

-- | La convolution linéaire du noyau (vert depuis le volet 0) : la
-- multiplication de S[x], source unique dans monoid-semiring.
naiveConv :: (Eq a, Semiring a) => [a] -> [a] -> [a]
naiveConv as bs = toCoeffs (fromCoeffs as `times` fromCoeffs bs)

-- | La convolution cyclique naïve sur n composantes : l'opération que
-- ① rend en produit point à point dans l'image de la transformée.
naiveCyclic :: Semiring a => Int -> [a] -> [a] -> [a]
naiveCyclic n v w =
  [ foldr plus zero [ (v !! j) `times` (w !! ((k - j) `mod` n)) | j <- [0 .. n - 1] ]
  | k <- [0 .. n - 1] ]

-- | Le produit point à point ⊙ de ①.
pointwise :: Semiring a => [a] -> [a] -> [a]
pointwise = zipWith times

-- | Le chemin rapide complet (① réduction, ② contrat) : rembourrer à
-- n = 2^e > deg p + deg q, convolution cyclique par la transformée,
-- tronquer à la longueur linéaire.
fastConv :: [Mod 17] -> [Mod 17] -> [Mod 17]
fastConv as bs = trimZ (take m (convolve (root17 n) (pad n as) (pad n bs)))
  where
    m = length as + length bs - 1
    n = nextPow2 m

-- | La convolution entière naïve (référent de ③), longueur t_p + t_q − 1.
naiveIntConv :: [Integer] -> [Integer] -> [Integer]
naiveIntConv as bs =
  [ sum [ as !! i * bs !! (k - i)
        | i <- [max 0 (k - lb + 1) .. min k (la - 1)] ]
  | k <- [0 .. la + lb - 2] ]
  where la = length as; lb = length bs

pad :: Semiring a => Int -> [a] -> [a]
pad n xs = take n (xs ++ repeat zero)

trimZ :: (Eq a, Semiring a) => [a] -> [a]
trimZ = reverse . dropWhile (== zero) . reverse

nextPow2 :: Int -> Int
nextPow2 k = head [ p | e <- [0 ..], let p = 2 ^ (e :: Int), p >= max 1 k ]

-- | log₂ d'une puissance de deux (floor en général).
ilog2 :: Int -> Int
ilog2 n = length (takeWhile (< n) (iterate (* 2) 1))

modpow :: Integer -> Integer -> Integer -> Integer
modpow _ 0 _ = 1
modpow b e m
  | even e    = let h = modpow b (e `div` 2) m in (h * h) `mod` m
  | otherwise = (b `mod` m * modpow b (e - 1) m) `mod` m

-- ---------------------------------------------------------------------
-- Générateurs et rétrécisseurs.

genVec17 :: Int -> Gen [Mod 17]
genVec17 k = chooseInt (1, k) >>= \n -> vectorOf n arbitrary

genIntVec :: Gen [Integer]
genIntVec = chooseInt (1, 8) >>= \n -> vectorOf n (toInteger <$> chooseInt (-100, 100))

-- | Rétrécit une description en retirant des éléments, jamais jusqu'au
-- vide (la longueur 0 n'a pas de racine n = 2^e à exhiber).
shrinkDrop :: [a] -> [[a]]
shrinkDrop = filter (not . null) . shrinkList (const [])

shrinkIntVec :: [Integer] -> [[Integer]]
shrinkIntVec = filter (not . null) . shrinkList shrink

shrinkPair :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair sa sb (a, b) = [ (a', b) | a' <- sa a ] ++ [ (a, b') | b' <- sb b ]

-- Le multivarié de ④ : descriptions [(exposants, coefficient ℚ)],
-- répliquées de MultiDuels (dette datée).
genQ :: Gen Rational
genQ = (%) <$> choose (-6, 6) <*> choose (1, 4)

genExps :: Int -> Gen [Natural]
genExps k = vectorOf k (fromIntegral <$> chooseInt (0, 3))

genDesc :: Int -> Gen TermL
genDesc k = chooseInt (0, 5) >>= \n -> vectorOf n ((,) <$> genExps k <*> genQ)

genTermS :: Int -> Gen ([Natural], Rational)
genTermS k = (,) <$> vectorOf k (fromIntegral <$> chooseInt (0, 2))
                 <*> (genQ `suchThat` (/= 0))

genDescS :: Int -> Gen TermL
genDescS k =
  (normalizeT <$> (chooseInt (1, 3) >>= \n -> vectorOf n (genTermS k)))
    `suchThat` (not . null)

genF :: Int -> Gen [TermL]
genF k = chooseInt (1, 3) >>= \m -> vectorOf m (genDescS k)

shrinkTermQ :: ([Natural], Rational) -> [([Natural], Rational)]
shrinkTermQ (es, c) =
     [ (es', c) | es' <- shrinkComps es ]
  ++ [ (es, c') | c' <- shrink c, c' /= 0 ]
  where
    shrinkComps ns =
      [ take i ns ++ [n'] ++ drop (i + 1) ns
      | (i, n) <- zip [0 :: Int ..] ns, n' <- shrink n ]

shrinkDescQ :: TermL -> [TermL]
shrinkDescQ = shrinkList shrinkTermQ

shrinkF :: [TermL] -> [[TermL]]
shrinkF = filter (not . null) . shrinkList (filter (not . null . normalizeT) . shrinkDescQ)

unless' :: Bool -> String -> Either String ()
unless' True  _   = Right ()
unless' False why = Left why

seul :: [c] -> Either String c
seul [c] = Right c
seul cs  = Left (show (length cs) ++ " réponses pour une question")

-- Des descriptions aux porteurs multivariés et retour.
mk :: MonomialOrder o => ([Natural] -> o) -> TermL -> MPoly o Rational
mk wrap = fromTerms . map (\(es, c) -> (wrap es, c))

obsP :: MonomialOrder o => MPoly o Rational -> TermL
obsP = normalizeT . map (\(o, c) -> (components (toExp o), c)) . toTerms

-- | Normalisation ensemble contre ensemble : lc = 1, tri par têtes.
normalSet :: MonomialOrder o => [MPoly o Rational] -> [TermL]
normalSet =
  map obsP . sortOn (fmap fst . leading) . map monic . filter (/= zero)
  where
    monic p = case leading p of
      Nothing      -> p
      Just (_, lc) -> fromTerms [ (m, c / lc) | (m, c) <- toTerms p ]

lex2 :: [Natural] -> Lex 2
lex2 = Lex . expo

grl2 :: [Natural] -> GrLex 2
grl2 = GrLex . expo

grv2 :: [Natural] -> GrevLex 2
grv2 = GrevLex . expo

-- ---------------------------------------------------------------------
-- ① La transformée : la convolution devient produit point à point.

-- L'aller-retour : (1/n)·DFT_{ω⁻¹} ∘ DFT_ω = id sur des vecteurs
-- aléatoires de 𝔽₁₇, n = 2^e.
allerRetourDuel :: Int -> IO Verdict
allerRetourDuel n = runDuel 200 $ lawDuel
  ("① aller-retour 𝔽₁₇ (n=" ++ show n ++ ") : (1/n)·DFT_{ω⁻¹} ∘ DFT_ω = id")
  (vectorOf n arbitrary)
  (const [])
  (\v -> idft (root17 n) (dft (root17 n) v) == v)

-- Le morphisme : DFT(p ∗_cyc q) = DFT(p) ⊙ DFT(q) point à point.
morphismeDuel :: Int -> IO Verdict
morphismeDuel n = runDuel 300 $ lawDuel
  ("① morphisme 𝔽₁₇ (n=" ++ show n ++ ") : DFT(p ∗_cyc q) = DFT(p) ⊙ DFT(q)")
  ((,) <$> vectorOf n arbitrary <*> vectorOf n arbitrary)
  (const [])
  (\(v, w) ->
     let r = root17 n
     in dft r (naiveCyclic n v w) == pointwise (dft r v) (dft r w))

-- La réduction linéaire→cyclique : le chemin transformé (rembourré)
-- égale la convolution du noyau, verte depuis le volet 0.
linConvDuel :: Duel ([Mod 17], [Mod 17]) [Mod 17]
linConvDuel = Duel
  { duelName  = "① réduction linéaire→cyclique 𝔽₁₇ : chemin transformé = convolution du noyau (rembourrage n=2^e)"
  , generator = (,) <$> genVec17 4 <*> genVec17 4
  , shrinker  = shrinkPair shrinkDrop shrinkDrop
  , candidate = uncurry fastConv
  , referee   = pureReferee "convolution du noyau (𝔽₁₇, volet 0)"
                  (\(as, bs) -> trimZ (naiveConv as bs))
  }

-- Le contre-exemple ℤ/15 (témoin exhibé) : ω = 4 non principale, donc
-- l'aller-retour rend [10,1] sur [0,1] — une matrice ≠ id.
principalWitnessDuel :: Duel () [Mod 15]
principalWitnessDuel = Duel
  { duelName  = "① contre-exemple ℤ/15 : ω=4 non principale ⇒ aller-retour ≠ id (témoin [0,1] ↦ [10,1])"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> idft rootZ15 (dft rootZ15 [0, 1])
  , referee   = pureReferee "constat d'or (résidu à la main : [10,1] ≠ [0,1])"
                  (const [10, 1])
  }

-- ---------------------------------------------------------------------
-- ② La FFT : la racine principale divise le calcul.

-- Bit-identique, transformée : ntt ≡ dft sur n = 2^e.
nttEqDftDuel :: Int -> IO Verdict
nttEqDftDuel n = runDuel 1000 $ lawDuel
  ("② ntt ≡ dft 𝔽₁₇ (n=" ++ show n ++ ") : la transformée rapide = la naïve, bit à bit")
  (vectorOf n arbitrary)
  (const [])
  (\v -> ntt (root17 n) v == dft (root17 n) v)

-- Bit-identique, chemin complet : ntt ≡ chemin naïf à 10⁴ cas.
bitIdenticalDuel :: Duel ([Mod 17], [Mod 17]) [Mod 17]
bitIdenticalDuel = Duel
  { duelName  = "② bit-identique 𝔽₁₇ : chemin rapide (ntt) ≡ chemin naïf, 10⁴ cas (rembourrage compris)"
  , generator = (,) <$> genVec17 8 <*> genVec17 8
  , shrinker  = shrinkPair shrinkDrop shrinkDrop
  , candidate = uncurry fastConv
  , referee   = pureReferee "convolution du noyau (𝔽₁₇)"
                  (\(as, bs) -> trimZ (naiveConv as bs))
  }

-- Le compte exact : M(n) = (n/2)·log₂ n produits, n·log₂ n sommes
-- (égalité, pas borne).
countDuel :: Int -> Duel () Counts
countDuel n = Duel
  { duelName  = "② compte exact (n=" ++ show n ++ ") : produits = (n/2)·log₂ n, sommes = n·log₂ n"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> nttCount n
  , referee   = pureReferee "compte depuis les définitions"
                  (const (Counts ((n `div` 2) * ilog2 n) (n * ilog2 n)))
  }

-- ---------------------------------------------------------------------
-- ③ L'arithmétique exacte : le corps choisi pour sa racine.

-- ℤ par restes chinois ≡ convolution entière naïve sous la borne.
convZDuel :: Duel ([Integer], [Integer]) (Either BoundError [Integer])
convZDuel = Duel
  { duelName  = "③ ℤ par restes chinois ≡ convolution entière naïve (sous la borne)"
  , generator = (,) <$> genIntVec <*> genIntVec
  , shrinker  = shrinkPair shrinkIntVec shrinkIntVec
  , candidate = uncurry convolveZ
  , referee   = pureReferee "convolution entière naïve"
                  (\(as, bs) -> Right (naiveIntConv as bs))
  }

-- Le référent externe : numpy.convolve sur les mêmes entiers (par lots).
numpyRef :: Referee [([Integer], [Integer])] [[Integer]]
numpyRef = chunked 500 $ processBatchReferee
  "numpy.convolve" ["python3", "python"] ["-"]
  "import numpy as np\n"
  (\marker -> "print('" ++ marker ++ "')\n")
  (\(as, bs) ->
     "print(' '.join(map(str, np.convolve("
       ++ "np.array(" ++ show as ++ ",dtype=object),"
       ++ "np.array(" ++ show bs ++ ",dtype=object)).tolist())))\n")
  ""
  (\out -> Right (map read (words out)))

numpyDuel :: BatchDuel ([Integer], [Integer]) (Either BoundError [Integer])
                       ([Integer], [Integer]) [Integer]
numpyDuel = BatchDuel
  { batchName      = "③ référent externe : convolveZ ≡ numpy.convolve sur les mêmes entiers"
  , batchGenerator = (,) <$> genIntVec <*> genIntVec
  , batchShrinker  = shrinkPair shrinkIntVec shrinkIntVec
  , batchCandidate = uncurry convolveZ
  , batchQueries   = \(as, bs) _ -> [(as, bs)]
  , batchJudge     = \_ ours rs -> do
      r <- seul rs
      case ours of
        Left e   -> Left ("hors borne inattendu : " ++ show e)
        Right cs -> unless' (cs == r)
          ("convolveZ = " ++ show cs ++ ", numpy = " ++ show r)
  }

-- Le garde-fou : un cas construit hors borne est détecté (Left), jamais
-- rendu faux. Coefficients délibérément énormes — aucun ensemble fini de
-- premiers NTT ne couvre 2·(10^1000)²·64.
outOfBoundDuel :: Duel () Bool
outOfBoundDuel = Duel
  { duelName  = "③ garde-fou : un cas hors borne est détecté (Left), jamais rendu faux"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> case convolveZ huge huge of
      Left _  -> True
      Right _ -> False
  , referee   = pureReferee "constat : hors borne ⇒ Left" (const True)
  }
  where huge = replicate 64 (10 ^ (1000 :: Int))

-- Le garde-fou de /capacité/ : un premier ℓ = c·2^e + 1 n'admet de racine
-- principale d'ordre n que si n ≤ 2^e ; au-delà, 'rootMod' effondre ω à 1
-- (division entière 2^e `div` n = 0) et ses résidus sont faux. 'convolveZ'
-- doit écarter un tel premier, jamais combiner ses résidus dans le CRT.
-- Témoin à coût constant (n = 64, transformée minuscule) sur un jeu de
-- premiers injecté ('convolveZWith') : 17 = 1·2^4 + 1 (capacité 16) à côté
-- du vrai 998244353 (capacité 2^23). Pour une convolution de longueur 20
-- (m = 39, n = 64 > 16), 17 doit être écarté — 998244353 couvre seul la
-- magnitude. Régression du bug observé sur les vrais premiers : sans le
-- filtre, 12289 (e = 12) restait pour n > 4096, ω = 1, et le CRT rendait
-- un entier faux en silence (centre = −3895149463357 au lieu de 2049),
-- sans BoundError — la borne gardait la magnitude, jamais la capacité.
capacityDuel :: Duel () Bool
capacityDuel = Duel
  { duelName  = "③ garde-fou de capacité : un premier sans racine d'ordre n est écarté, jamais rendu faux"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> convolveZWith ps long long == Right (naiveIntConv long long)
  , referee   = pureReferee "constat : premier sous-capacité écarté ⇒ exact" (const True)
  }
  where
    long = replicate 20 (1 :: Integer)            -- m = 39, n = 64
    p17  = NttPrime 17 1 4 3 3                     -- 17 = 1·2^4 + 1, capacité 16
    ps   = head nttPrimes : [p17]                  -- 998244353 (capacité 2^23) + 17

-- L'ordre des racines : pour chaque premier retenu ℓ = c·2^e + 1, la
-- racine est principale d'ordre exact 2^e (ω^{2^e} = 1 et ω^{2^{e−1}} ≠ 1).
rootOrderDuel :: Duel () Bool
rootOrderDuel = Duel
  { duelName  = "③ ordre des racines : ℓ = c·2^e+1 et ord(ω) = 2^e exact, pour chaque premier retenu"
  , generator = pure ()
  , shrinker  = const []
  , candidate = \() -> all ok nttPrimes
  , referee   = pureReferee "constat : racine principale d'ordre exact 2^e" (const True)
  }
  where
    ok p =
      let l = primeModulus p; w = primePrincipalRoot p; e = primeTwoAdicExp p
          n = 2 ^ e
      in primeCofactor p * 2 ^ e + 1 == l
           && modpow w n l == 1
           && modpow w (n `div` 2) l /= 1

-- ---------------------------------------------------------------------
-- ④ F4 : la réduction devient échelonnage.

-- nfF4 ≡ nf : la forme normale par échelonnage = par division (volet 3).
nfF4Duel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
nfF4Duel nom wrap = runDuel 200 $ lawDuel
  ("④ nfF4 ≡ nf (" ++ nom ++ ") : forme normale par échelonnage = par division (volet 3)")
  ((,) <$> (normalizeT <$> genDesc 2) <*> genF 2)
  (shrinkPair shrinkDescQ shrinkF)
  (\(pT, gT) ->
     let p = mk wrap pT; g = map (mk wrap) gT
     in obsP (nfF4 p g) == obsP (nf p g))

-- La base de F4 ≡ la base réduite de Buchberger, ensemble contre ensemble.
f4VsBuchDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
f4VsBuchDuel nom wrap = runDuel 100 $ lawDuel
  ("④ base F4 ≡ base réduite de Buchberger (" ++ nom ++ "), ensemble contre ensemble")
  (genF 2) shrinkF
  (\fT -> let g = map (mk wrap) fT
          in normalSet (f4 g) == normalSet (reduce (buchberger g)))

-- ④ sur 𝔽₇ : F4, générique en 'Field', exercé en caractéristique p — pas
-- seulement à ℚ. Comble le trou #2 du volet 4 côté Gröbner (jusqu'ici
-- l'algèbre linéaire n'était duelée qu'à ℚ). Porteur 'Mod 7' (corps : ℓ
-- premier, porte 'mod' déjà au paquet ; 'invertMod' total et correct).
-- Référent : la base réduite de Buchberger sur le MÊME corps. Les deux
-- côtés passent par 'reduce' (forme réduite unique, volet 4), donc la
-- comparaison polymorphe 'normalSetF' n'a pas à remonifier.
genFp7 :: Gen [[([Natural], Mod 7)]]
genFp7 = chooseInt (1, 3) >>= \m -> vectorOf m genPolyP
  where
    genPolyP = (chooseInt (1, 3) >>= \n -> vectorOf n genTermP) `suchThat` (not . null)
    genTermP = (,) <$> vectorOf 2 (fromIntegral <$> chooseInt (0, 2))
                   <*> (fromIntegral <$> chooseInt (1, 6))  -- coeff ≠ 0 dans 𝔽₇

shrinkFp :: [[([Natural], Mod 7)]] -> [[[([Natural], Mod 7)]]]
shrinkFp = shrinkList (shrinkList shrinkTermP)
  where
    shrinkTermP (es, c) = [ (es', c) | es' <- shrinkExps es ]
    shrinkExps ns = [ take i ns ++ [n'] ++ drop (i + 1) ns
                    | (i, n) <- zip [0 :: Int ..] ns, n' <- shrink n ]

-- Des descriptions au porteur 𝔽₇ ('mk' est figé à ℚ).
mkP :: MonomialOrder o => ([Natural] -> o) -> [([Natural], Mod 7)] -> MPoly o (Mod 7)
mkP wrap = fromTerms . map (\(es, c) -> (wrap es, c))

-- Normalisation ensemble contre ensemble, polymorphe en 'Field' : têtes
-- triées, termes lus dans l'ordre canonique du porteur (les deux bases
-- comparées sortent de 'reduce', donc déjà unitaires et pleinement
-- réduites — aucune remonification ici).
normalSetF :: (MonomialOrder o, Semiring s, Eq s) => [MPoly o s] -> [[([Natural], s)]]
normalSetF = sortOn (map fst) . map obs . filter (/= zero)
  where obs = map (\(mm, c) -> (components (toExp mm), c)) . toTerms

f4VsBuchFpDuel :: MonomialOrder o => String -> ([Natural] -> o) -> IO Verdict
f4VsBuchFpDuel nom wrap = runDuel 100 $ lawDuel
  ("④ 𝔽₇ : base F4 ≡ base réduite de Buchberger (" ++ nom ++ "), corps fini")
  genFp7 shrinkFp
  (\fT -> let g = map (mkP wrap) fT
          in normalSetF (f4 g) == normalSetF (reduce (buchberger g)))

-- Le duel décisif rejoué avec F4 (familles aléatoires) : f4 F ≡
-- std·redSB du référent, ensemble contre ensemble.
decisiveF4Duel :: MonomialOrder o
               => String -> ([Natural] -> o)
               -> BatchDuel [TermL] [TermL] [TermL] [TermL]
decisiveF4Duel nom wrap = BatchDuel
  { batchName      = "④ duel décisif F4 (" ++ nom
                       ++ ") : f4 F ≡ std·redSB du référent, ensemble contre ensemble"
  , batchGenerator = genF 2
  , batchShrinker  = shrinkF
  , batchCandidate = normalSet . f4 . map (mk wrap)
  , batchQueries   = \fT _ -> [fT]
  , batchJudge     = \_ mine rs -> do
      sT <- seul rs
      let attendu = normalSet (map (mk wrap) sT)
      unless' (mine == attendu)
        ("référent : " ++ show attendu ++ " — candidat : " ++ show mine)
  }

-- Le duel décisif rejoué avec F4 (familles nommées) : cyclic-4..6 et
-- katsura-3..5, générées ET résolues par le référent (jamais
-- retranscrites), grevlex — la base de F4 contre std·redSB.
f4FamilleDuel :: forall k. KnownNat k => Proxy k -> String -> IO Verdict
f4FamilleDuel pk name =
  runCertDuel 1 $ CertDuel
    { certName      = "④ duel décisif F4 : " ++ name ++ "-" ++ show n
                        ++ " (grevlex), F4 contre std·redSB"
    , certGenerator = pure ()
    , certShrinker  = const []
    , certCandidate = const ()
    , certJudge     = \() () -> do
        (fT, sT) <- refCall (familyRef name n "dp") ()
        let mine    = normalSet (f4 (map (mk wrap) fT))
            attendu = normalSet (map (mk wrap) sT)
        pure $ unless' (mine == attendu)
          ("référent : " ++ show attendu ++ " — candidat : " ++ show mine)
    }
  where
    n = fromIntegral (natVal pk) :: Int
    wrap = GrevLex . expo :: [Natural] -> GrevLex k

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  numpyGate <- lookupEnv "CAUCHY_ORACLE_NUMPY"
  singGate  <- lookupEnv "CAUCHY_ORACLE_SINGULAR"
  numped <- case numpyGate of
    Nothing -> pure
      [ pure (Verdict True "SKIP ③ numpy.convolve (CAUCHY_ORACLE_NUMPY non défini)" Nothing) ]
    Just _  -> pure [ runBatchDuel 1000 numpyRef numpyDuel ]
  gated <- case singGate of
    Nothing -> pure
      [ pure (Verdict True
          "SKIP ④ singular : duels décisifs F4, familles cyclic/katsura (CAUCHY_ORACLE_SINGULAR non défini)"
          Nothing) ]
    Just _  -> pure
      [ runBatchDuel nSingular (parLots (stdRedSBRefN 2 "lp")) (decisiveF4Duel "lex" lex2)
      , runBatchDuel nSingular (parLots (stdRedSBRefN 2 "dp")) (decisiveF4Duel "grevlex" grv2)
      , f4FamilleDuel (Proxy :: Proxy 4) "cyclic"
      , f4FamilleDuel (Proxy :: Proxy 5) "cyclic"
      , f4FamilleDuel (Proxy :: Proxy 6) "cyclic"
      , f4FamilleDuel (Proxy :: Proxy 3) "katsura"
      , f4FamilleDuel (Proxy :: Proxy 4) "katsura"
      , f4FamilleDuel (Proxy :: Proxy 5) "katsura"
      ]
  ok <- runSuite $
    -- ① la transformée
       [ allerRetourDuel n | n <- ns ]
    ++ [ morphismeDuel n   | n <- ns ]
    ++ [ runDuel 500 linConvDuel
       , runDuel 1 principalWitnessDuel
       ]
    -- ② la FFT et son compte
    ++ [ nttEqDftDuel n | n <- ns ]
    ++ [ runDuel 10000 bitIdenticalDuel ]
    ++ [ runDuel 1 (countDuel n) | n <- ns ]
    -- ③ l'arithmétique exacte
    ++ [ runDuel 1000 convZDuel
       , runDuel 1 outOfBoundDuel
       , runDuel 1 capacityDuel
       , runDuel 1 rootOrderDuel
       ]
    -- ④ F4 (pur)
    ++ [ nfF4Duel "lex" lex2, nfF4Duel "grlex" grl2, nfF4Duel "grevlex" grv2 ]
    ++ [ f4VsBuchDuel "lex" lex2, f4VsBuchDuel "grlex" grl2
       , f4VsBuchDuel "grevlex" grv2
       ]
    ++ [ f4VsBuchFpDuel "lex" lex2, f4VsBuchFpDuel "grlex" grl2
       , f4VsBuchFpDuel "grevlex" grv2
       ]
    -- les externes (gardés)
    ++ numped
    ++ gated
  unless ok exitFailure
  putStrLn "BACKENDS (①–④) : all green"
  where
    ns        = [2, 4, 8, 16] :: [Int]
    parLots   = chunked 500
    nSingular = 1000
