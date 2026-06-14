{-# LANGUAGE ScopedTypeVariables #-}
-- | Backends rapides : la NTT et F4 (volet 5).
--
-- Squelette du temps rouge : les /types/ de l'API différentielle sont
-- posés — c'est le contrat exécutable des pages ①–④ — mais aucune
-- fonction n'est construite. Chaque corps lève 'manque' ; les treize
-- lignes CONTRAT (test/Duels.hs) les constatent toutes en échec contre
-- ce squelette, avant le premier commit du vert (plan-backends.md,
-- §oracle).
--
-- L'API est /différentielle/ : pour chaque chemin rapide, le référent
-- est le chemin lent — la convolution du noyau (vert depuis le volet 0)
-- pour ①–③, Buchberger (volet 4) pour ④ — et l'égalité est exigée bit
-- à bit. Le porteur reste au plus bas : la transformée est polymorphe
-- sur un 'Semiring' (le corps n'est pas requis ; ①–③ valent sur un
-- anneau commutatif muni d'une racine principale), la donnée de la
-- racine — ω, ω⁻¹, n⁻¹ — étant fournie par qui connaît le porteur
-- ('Root'). Le choix d'une classe ou d'une dépendance pour calculer
-- ces inverses appartient à la porte d'écosystème du vert, pas au
-- rouge.
module Data.Cauchy.Backends
  ( -- * ① La transformée
    Root (..)
  , dft
  , idft
    -- * ② La FFT et son compte
  , ntt
  , intt
  , convolve
  , Counts (..)
  , nttCount
    -- * ③ L'arithmétique exacte : ℤ par les restes chinois
  , NttPrime (..)
  , nttPrimes
  , coeffBound
  , BoundError (..)
  , convolveZ
  , convolveZWith
    -- * ④ F4 : la réduction en bloc
  , f4
  , nfF4
  ) where

import Prelude hiding (negate)

import Data.List (partition, sortBy)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Mod (Mod, invertMod, unMod)
import Data.Ord (Down (..), comparing)
import Data.Proxy (Proxy (..))
import qualified Data.Set as Set
import GHC.TypeNats (KnownNat, SomeNat (..), someNatVal)
import Numeric.Natural (Natural)

import Data.Euclidean (Field)
import qualified Data.Euclidean as E
import Data.Semiring (Ring (..), Semiring (..))

import Data.Cauchy.Groebner (reduce)
import Data.Cauchy.Multi (MPoly, coefficient, fromTerms, leading, toTerms)
import Data.Cauchy.Order (Arity, Exp, MonomialOrder (..), divides, minus, sup,
                          totalDegree)

-- | ω^e dans le porteur (e ≥ 0), produit littéral — /sans/ réduction
-- modulo n. Sur une racine principale ω^n = 1 ; le contre-exemple ℤ/15
-- (① témoin) exige justement que rien ne suppose ω^n = 1.
pow :: Semiring a => a -> Int -> a
pow w e = foldr times one (replicate e w)

-- ---------------------------------------------------------------------
-- ① La transformée : la convolution devient produit point à point.

-- | La donnée d'une racine principale n-ième, telle que la transformée
-- la consomme : ω, son inverse, l'inverse de n dans le porteur, et n.
-- Qui connaît le porteur (un corps 𝔽_ℓ, l'anneau ℤ/m) la construit ;
-- la transformée n'exige du porteur qu'un 'Semiring'.
-- SNIPPET:backends-root
-- NOTE:Semiring: le porteur n'exige qu'un semi-anneau — ni corps ni même soustraction ; ω, ω⁻¹, n⁻¹ viennent de 'Root', construits par qui connaît le porteur (𝔽_ℓ, ℤ/m). La principalité de ω n'est PAS dans le type — elle est jugée par l'oracle (témoin ℤ/15)
data Root a = Root
  { rootOmega    :: a   -- ^ ω, racine principale n-ième de l'unité
  , rootInvOmega :: a   -- ^ ω⁻¹
  , rootInvOrder :: a   -- ^ n⁻¹ dans le porteur
  , rootOrder    :: Int -- ^ n
  }

-- | p̂ = (p(1), p(ω), …, p(ω^{n−1})) : l'évaluation aux puissances de ω,
-- le chemin lent de la transformée (O(n²), évalué point par point).
dft :: Semiring a => Root a -> [a] -> [a]
dft r v =
  [ foldr plus zero [ (v !! j) `times` pow w (j * k) | j <- [0 .. n - 1] ]
  | k <- [0 .. n - 1] ]
  where w = rootOmega r
        n = rootOrder r

-- | La transformée inverse : (1/n)·DFT_{ω⁻¹}. L'aller-retour
-- @idft r . dft r@ est l'identité — quand ω est /principale/ (① ; la
-- preuve est la somme de principalité).
idft :: Semiring a => Root a -> [a] -> [a]
idft r v =
  [ invN `times`
      foldr plus zero [ (v !! j) `times` pow wInv (j * k) | j <- [0 .. n - 1] ]
  | k <- [0 .. n - 1] ]
  where wInv = rootInvOmega r
        invN = rootInvOrder r
        n    = rootOrder r
-- END:backends-root

-- ---------------------------------------------------------------------
-- ② La FFT : la racine principale divise le calcul.

-- | La transformée rapide (scission pair/impair, radix 2) : même valeur
-- que 'dft' lorsque n = 2^e, en (n/2)·log₂ n produits au lieu de n².
ntt :: Semiring a => Root a -> [a] -> [a]
ntt r = fft (rootOmega r) (rootOrder r)

-- | L'inverse rapide, pendant de 'ntt' comme 'idft' l'est de 'dft' :
-- la même scission sur ω⁻¹, puis l'échelle 1/n.
intt :: Semiring a => Root a -> [a] -> [a]
intt r = map (rootInvOrder r `times`) . fft (rootInvOmega r) (rootOrder r)

-- | La scission pair/impair, radix 2, sur n = 2^e. Pas de soustraction
-- (le porteur n'est qu'un 'Semiring') : le papillon écrit les deux
-- sorties comme E[k] + ω^k·O[k] et E[k] + ω^{k+n/2}·O[k], la périodicité
-- E[k+n/2] = E[k] (vraie quand ω^n = 1) faisant le reste. Égale 'dft'
-- bit à bit sur une racine principale (② : ntt ≡ dft).
-- SNIPPET:backends-fft
-- NOTE:plus: pas de soustraction — le porteur n'est qu'un 'Semiring' ; le papillon écrit les deux sorties comme E[k] + ω^k·O[k] et E[k] + ω^{k+n/2}·O[k], la périodicité E[k+n/2] = E[k] (vraie quand ω^n = 1) tenant lieu du signe
fft :: Semiring a => a -> Int -> [a] -> [a]
fft _ 1 v = v
fft w n v = lo ++ hi
  where
    h     = n `div` 2
    w2    = w `times` w
    e     = fft w2 h (evens v)
    o     = fft w2 h (odds v)
    ws    = take n (iterate (times w) one)   -- ω^0 … ω^{n−1}
    lo    = [ (e !! k) `plus` ((ws !! k)       `times` (o !! k)) | k <- [0 .. h - 1] ]
    hi    = [ (e !! k) `plus` ((ws !! (k + h)) `times` (o !! k)) | k <- [0 .. h - 1] ]
    evens (x : _ : xs) = x : evens xs
    evens xs           = xs
    odds  (_ : y : xs) = y : odds xs
    odds  _            = []
-- END:backends-fft

-- | La convolution cyclique par le chemin transformé :
-- @intt r (ntt r p ⊙ ntt r q)@, les deux entrées de longueur n =
-- 'rootOrder' r. La réduction linéaire→cyclique (rembourrer à
-- n > deg p + deg q) est du ressort de l'appelant, qui connaît les
-- degrés.
convolve :: (Eq a, Semiring a) => Root a -> [a] -> [a] -> [a]
convolve r p q = intt r (zipWith times (ntt r p) (ntt r q))

-- | Le compte instrumenté de 'ntt' sur n = 2^e : produits et sommes de
-- la récursion (pas la forme close — l'implémentation doit tenir le
-- compteur en phase avec le calcul). Le contrat : @products = (n/2)·log₂ n@,
-- @additions = n·log₂ n@ (égalité, pas borne).
data Counts = Counts
  { products  :: Int
  , additions :: Int
  } deriving (Eq, Show)

-- | Le compteur de produits/sommes de la récursion radix-2 sur n = 2^e.
-- Tenu /en phase/ avec 'fft' : à chaque niveau, h = n/2 papillons, et un
-- papillon est un produit (ω^k·O[k]) et deux sommes (les deux sorties).
-- La forme close (n/2)·log₂ n et n·log₂ n en tombe — l'égalité, non la
-- borne, est le contrat (② compte exact).
-- SNIPPET:backends-count
-- NOTE:products: compteur tenu /en phase/ avec 'fft' : à chaque niveau h = n/2 papillons, un produit et deux sommes chacun ; la forme close (n/2)·log₂n et n·log₂n en tombe — l'égalité, non la borne, est le contrat
nttCount :: Int -> Counts
nttCount 1 = Counts 0 0
nttCount n = Counts (2 * products sub + h) (2 * additions sub + 2 * h)
  where h   = n `div` 2
        sub = nttCount h
-- END:backends-count

-- ---------------------------------------------------------------------
-- ③ L'arithmétique exacte : le corps choisi pour sa racine.

-- | Un premier NTT ℓ = c·2^e + 1, avec un générateur de 𝔽_ℓ^× et une
-- racine principale d'ordre 2^e dérivée de lui. L'ordre exact de la
-- racine est /testé/, jamais supposé (③ : ω^{2^e} = 1 et ω^{2^{e−1}} ≠ 1).
data NttPrime = NttPrime
  { primeModulus       :: Integer -- ^ ℓ
  , primeCofactor      :: Integer -- ^ c, dans ℓ = c·2^e + 1
  , primeTwoAdicExp    :: Int     -- ^ e
  , primeGenerator     :: Integer -- ^ un générateur de 𝔽_ℓ^×
  , primePrincipalRoot :: Integer -- ^ une racine principale d'ordre 2^e
  } deriving (Eq, Show)

-- | Les premiers retenus, consignés avec leur décomposition (note
-- d'entrée §5 : 998244353 = 119·2²³ + 1, 12289 = 3·2¹² + 1).
nttPrimes :: [NttPrime]
nttPrimes = [ mk 998244353 119 23 3    -- 119·2²³ + 1, 3 racine primitive
            , mk 12289       3 12 11 ] -- 3·2¹²  + 1, 11 racine primitive
  where
    -- ω = g^c a pour ordre 2^e quand g engendre 𝔽_ℓ^× (ordre ℓ−1 = c·2^e) ;
    -- l'ordre exact est /testé/ (③ rootOrderDuel), jamais supposé.
    mk l c e g = NttPrime l c e g (modpow g c l)

-- | La borne sur les coefficients d'un produit p ∗ q :
-- min(t_p, t_q)·A_p·A_q (t = nombre de termes, A = hauteur). Calculée
-- avant le produit ; le dépassement est un échec détecté, jamais un
-- résultat faux.
coeffBound :: [Integer] -> [Integer] -> Integer
coeffBound as bs =
  toInteger (min (length as) (length bs)) * height as * height bs
  where height = maximum . (0 :) . map abs

-- | Le dépassement de borne réifié : ce dont la reconstruction par
-- restes chinois aurait eu besoin, et ce que les premiers retenus
-- couvrent. Rendu plutôt qu'un entier faux.
data BoundError = BoundExceeded
  { boundNeeded  :: Integer -- ^ 2·(borne sur les coefficients)
  , boundCovered :: Integer -- ^ produit des premiers retenus
  } deriving (Eq, Show)

-- | La convolution entière par NTT sur les premiers retenus, ℤ retrouvé
-- par restes chinois (résidu symétrique) sous la borne vérifiée. 'Left'
-- si la borne est dépassée — détecté, jamais rendu faux. Les premiers
-- sont 'nttPrimes' ; 'convolveZWith' les prend en paramètre (le garde de
-- capacité y est testable à petite échelle).
convolveZ :: [Integer] -> [Integer] -> Either BoundError [Integer]
convolveZ = convolveZWith nttPrimes

-- | 'convolveZ' paramétrée par le jeu de premiers NTT (injecté plutôt que
-- figé : le garde de capacité est ainsi témoignable sur un premier
-- synthétique à petit @e@, sans payer une transformée de taille n > 2^23).
-- SNIPPET:backends-crt
-- NOTE:filter: le garde de capacité — ℓ = c·2^e+1 n'admet de racine principale d'ordre n que si n ≤ 2^e ; au-delà 'rootMod' effondre ω à 1 (division entière 2^e `div` n = 0) et ses résidus mod ℓ sont faux. Écarter ces premiers restreint 'covered' ; la borne needed > covered garde alors magnitude ET capacité d'un seul tenant
-- NOTE:crt: restes chinois à résidu /symétrique/, ramené dans (−M/2, M/2] ; la borne vérifiée (covered impair, needed pair ⇒ jamais égaux) garantit |coefficient vrai| < M/2, levant l'ambiguïté de signe
convolveZWith :: [NttPrime] -> [Integer] -> [Integer]
              -> Either BoundError [Integer]
convolveZWith ps as bs
  | needed > covered = Left (BoundExceeded needed covered)
  | otherwise        =
      Right [ crt [ (primeModulus p, res p !! i) | p <- primes ]
            | i <- [0 .. m - 1] ]
  where
    -- Seuls les premiers dont la capacité 2-adique couvre n : ℓ = c·2^e+1
    -- n'admet de racine principale d'ordre n que si n ≤ 2^e. Au-delà,
    -- 'rootMod' effondre ω à 1 (division entière 2^e `div` n = 0) et les
    -- résidus mod ℓ sont faux. Écarter ces premiers restreint 'covered' ;
    -- la borne 'needed > covered' garde alors la magnitude /et/ la
    -- capacité d'un seul tenant — sinon un produit long à petits
    -- coefficients passait la borne et sortait faux en silence.
    primes  = filter (\p -> n <= 2 ^ primeTwoAdicExp p) ps
    needed  = 2 * coeffBound as bs
    covered = product (map primeModulus primes)
    m       = length as + length bs - 1
    n       = nextPow2 m
    -- La convolution cyclique sur 𝔽_ℓ par la transformée du volet 5 même
    -- (convolve, polymorphe), tronquée à la longueur linéaire m ≤ n.
    res p   = take m (convolveModPrime p n as bs)
    -- Restes chinois à résidu /symétrique/ : x ≡ rᵢ mod ℓᵢ, ramené dans
    -- (−M/2, M/2]. La borne vérifiée garantit |coefficient vrai| < M/2.
    crt pairs =
      let bigM = product (map fst pairs)
          x = (`mod` bigM) $ sum
                [ r * mi * modpow mi (l - 2) l
                | (l, r) <- pairs, let mi = bigM `div` l ]
      in if 2 * x > bigM then x - bigM else x
-- END:backends-crt

-- | La convolution cyclique de @as@, @bs@ (rembourrés à n = 2^e) modulo
-- le premier @p@, par 'convolve' sur le porteur 'Mod ℓ' — le modulo
-- vient au niveau type par réflexion ('someNatVal'), seul endroit du
-- paquet où l'arithmétique modulaire concrète est inévitable (porte
-- d'écosystème : 'mod' y entre). Résidus rendus dans [0, ℓ).
convolveModPrime :: NttPrime -> Int -> [Integer] -> [Integer] -> [Integer]
convolveModPrime p n as bs =
  case someNatVal (fromInteger (primeModulus p)) of
    SomeNat (_ :: Proxy q) ->
      let r  = rootMod p n :: Root (Mod q)
          xs = map fromInteger (padTo n as) :: [Mod q]
          ys = map fromInteger (padTo n bs)
      in map (toInteger . unMod) (convolve r xs ys)
  where padTo k xs = take k (xs ++ repeat 0)

-- | La racine d'ordre n = 2^d (d ≤ e) sur 'Mod ℓ', dérivée de la racine
-- d'ordre 2^e du premier : ω_n = (racine principale)^{2^e / n}. Les
-- inverses ω⁻¹ et n⁻¹ par 'invertMod' (total — corrects car ℓ premier).
-- SNIPPET:backends-rootmod
-- NOTE:div: si n > 2^e cette division entière vaut 0 et ω s'effondre à 1 — la racine n'existe pas ; c'est l'effondrement que le filtre de capacité de 'convolveZWith' prévient en amont, hors de cette fonction
-- NOTE:invertMod: ℓ premier ⇒ 𝔽_ℓ corps ⇒ 'invertMod' total et correct (ω⁻¹, n⁻¹) ; sur un composite il échouerait — la primalité est l'hypothèse, jugée par l'oracle d'ordre des racines
rootMod :: forall q. KnownNat q => NttPrime -> Int -> Root (Mod q)
rootMod p n = Root w (inv w) (inv (fromIntegral n)) n
  where
    e = primeTwoAdicExp p
    w = (fromInteger (primePrincipalRoot p) :: Mod q) ^ (2 ^ e `div` n :: Int)
    inv x = case invertMod x of
      Just y  -> y
      Nothing -> error "cauchy-backends : rootMod — élément non inversible mod ℓ"
-- END:backends-rootmod

-- | La plus petite puissance de deux ≥ k.
nextPow2 :: Int -> Int
nextPow2 k = head [ q | e <- [0 ..], let q = 2 ^ (e :: Int), q >= max 1 k ]

-- | Exponentiation modulaire (carré-multiplie) : ω = g^c, et l'inverse
-- de Fermat dans le CRT.
modpow :: Integer -> Integer -> Integer -> Integer
modpow _ 0 _ = 1
modpow b e m
  | even e    = let h = modpow b (e `div` 2) m in (h * h) `mod` m
  | otherwise = (b `mod` m) * modpow b (e - 1) m `mod` m

-- ---------------------------------------------------------------------
-- ④ F4 : la réduction devient échelonnage.

-- | La complétion en bloc : la base de Gröbner /réduite/ de ⟨F⟩,
-- calculée par échelonnage de matrices de Macaulay. Même résultat que
-- 'Data.Cauchy.Groebner.buchberger' puis 'reduce' — la base réduite
-- étant unique (volet 4), l'égalité ensemble contre ensemble est le
-- contrat.
-- SNIPPET:backends-f4
-- NOTE:Field: S corps — l'échelonnage pivote (monicB inverse le coefficient de tête) ; l'hypothèse de tout l'arc Gröbner, reconduite
-- NOTE:reduce: f4 = reduce ∘ f4core ; 'reduce' (volet 4) canonise la base — unique à ordre fixé, donc l'égalité ensemble contre ensemble avec Buchberger est bien posée, insensible au chemin de chacun
f4 :: (MonomialOrder o, Field s, Ring s, Eq s) => [MPoly o s] -> [MPoly o s]
f4 fs = reduce (f4core [ f | f <- fs, f /= zero ])
-- END:backends-f4

-- | F4 (Faugère) : la complétion par échelonnage de matrices de
-- Macaulay. Sélection normale (le plus petit degré de coin d'abord) ;
-- chaque lot de S-polynômes est fermé par préparation symbolique (tout
-- monôme réductible reçoit son réducteur), puis réduit en forme
-- échelonnée ; les lignes dont la tête est neuve (∉ têtes du lot)
-- étendent la base. ⟨lm G⟩ croît strictement à chaque tour — Dickson
-- force l'arrêt. La base réduite étant unique (volet 4), 'reduce' la
-- canonise ; le contrat (④) la confronte à Buchberger et à Singular.
f4core :: forall o s. (MonomialOrder o, Field s, Ring s, Eq s)
       => [MPoly o s] -> [MPoly o s]
f4core fs
  | null g0   = []
  | otherwise = map fst (loop g0 (prune g0 (allPairs (length g0))))
  where
    -- La base porte son /sucre/ : le degré qu'aurait le calcul
    -- homogénéisé (degré total initial pour un générateur). Sans lui, la
    -- sélection par degré de coin fait exploser les coefficients sur ℚ
    -- pour un système affine (cyclic-n) — le piège que Buchberger évite
    -- par le même sucre (Giovini–Mora–Niesi–Robbiano–Traverso 1991).
    g0 = [ (monicB f, degTot f) | f <- fs ]

    allPairs n = [ (i, j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1] ]

    poly g i = fst (g !! i)
    lmAt g i = lmExp (poly g i)
    sug  g i = snd (g !! i)
    coin g i j = sup (lmAt g i) (lmAt g j)

    -- Le sucre d'une paire : max des deux têtes hissées au coin.
    sucre g i j =
      let c = coin g i j
      in max (sug g i + totalDegree c - totalDegree (lmAt g i))
             (sug g j + totalDegree c - totalDegree (lmAt g j))

    -- Critère premier : têtes premières entre elles (γ = α + β) ⇒
    -- S-polynôme →G 0, paire élaguée (premier critère, ②).
    prune g = filter (\(i, j) -> coin g i j /= lmAt g i <> lmAt g j)

    -- Critère de chaîne (Buchberger 2 / Gebauer–Möller) : (i,j) est
    -- superflue si une tête lt_k divise lcm(lt_i,lt_j) et que les paires
    -- {i,k}, {j,k} sont déjà traitées (hors file) — son S-polynôme est
    -- alors combinaison de celles-là, réduit à 0. Sans cet élagage, F4
    -- traite ~|G|² paires, en majorité fantômes (cyclic-6 inatteignable).
    chainPrune g pending = filter keep pending
      where
        bset = Set.fromList pending
        keep (i, j) =
          not (any cover [ k | k <- [0 .. length g - 1], k /= i, k /= j ])
          where
            cover k =
              divides (lmAt g k) (coin g i j)
                && not (ord i k `Set.member` bset)
                && not (ord j k `Set.member` bset)
        ord a b = (min a b, max a b)

    loop g pending0 = case chainPrune g pending0 of
      []    -> g
      pairs ->
        let key (i, j)        = (sucre g i j, totalDegree (coin g i j))
            d@(sucBatch, _)   = minimum (map key pairs)
            (lot, reste)      = partition ((== d) . key) pairs
            half i j     = case coin g i j `minus` lmAt g i of
              Just e  -> shiftBy e (poly g i)
              Nothing -> error "cauchy-backends : f4 — le coin ne couvre pas la tête"
            ls     = concat [ [half i j, half j i] | (i, j) <- lot ]
            rows   = symbolic (map fst g) ls
            oldLMs = Set.fromList (concatMap leadMon rows)
            news   = [ monicB r
                     | r <- echelon rows
                     , m <- leadMon r
                     , not (m `Set.member` oldLMs) ]
        in if null news
             then loop g reste
             else let g'   = g ++ [ (h, max sucBatch (degTot h)) | h <- news ]
                      nouv = prune g'
                               [ (i, t) | t <- [length g .. length g' - 1]
                                        , i <- [0 .. t - 1] ]
                  in loop g' (reste ++ nouv)

-- | Le degré total d'un polynôme — le sucre initial d'un générateur.
degTot :: MonomialOrder o => MPoly o s -> Natural
degTot p = maximum (0 : [ totalDegree (toExp m) | (m, _) <- toTerms p ])

-- | Préparation symbolique : ferme le lot sous « tout monôme réductible
-- reçoit le réducteur x^{m−lt gₖ}·gₖ, de tête m ». Les têtes des lignes
-- sont les colonnes-pivots déjà fournies ; les autres monômes forment la
-- file à traiter. Clôture finie (les monômes décroissent).
symbolic :: forall o s. (MonomialOrder o, Field s, Ring s, Eq s)
         => [MPoly o s] -> [MPoly o s] -> [MPoly o s]
symbolic g rows0 = go rows0 done0 (mons rows0 `Set.difference` done0)
  where
    done0   = Set.fromList (concatMap leadMon rows0)
    mons rs = Set.fromList [ m | r <- rs, (m, _) <- toTerms r ]
    go rows done todo = case Set.minView todo of
      Nothing -> rows
      Just (m, todo')
        | m `Set.member` done -> go rows done todo'
        | otherwise -> case reductor m of
            Nothing  -> go rows (Set.insert m done) todo'
            Just red ->
              let neufs = Set.fromList [ mm | (mm, _) <- toTerms red ]
                            `Set.difference` Set.insert m done
              in go (red : rows) (Set.insert m done) (Set.union todo' neufs)
    reductor m = listToMaybe
      [ shiftBy e gk
      | gk <- g, Just (lmk, _) <- [leading gk]
      , Just e <- [toExp m `minus` toExp lmk] ]

-- | L'échelonnage de la matrice de Macaulay, /creux/ : les lignes sont
-- les polynômes eux-mêmes (porteur Map), jamais étalés en vecteurs
-- denses — la matrice de Macaulay est creuse. L'élimination de Gauss
-- procède par tête ≻ décroissante : chaque ligne est réduite contre les
-- pivots de même tête, puis devient le pivot de sa tête (neuve) ou
-- s'annule (S-polynôme réduit à 0, ligne nulle qui disparaît). /Une
-- opération de ligne est un pas de la division/ (④).
-- SNIPPET:backends-echelon
-- NOTE:reduceRow: une opération de ligne EST un pas de la division (volet 3) : r ← r − c·p, p unitaire ; la passe avant échelonne par tête ≻ décroissante, chaque ligne réduite contre les pivots de même tête
-- NOTE:backReduce: passe arrière (Gauss–Jordan) — chaque colonne-pivot effacée du reste des lignes ; les pivots deviennent pleinement réduits (forme échelonnée réduite). Sans elle les queues s'accumulent et les coefficients sur ℚ explosent
echelon :: forall o s. (MonomialOrder o, Field s, Ring s, Eq s)
        => [MPoly o s] -> [MPoly o s]
echelon rows = Map.elems (backReduce forward)
  where
    -- Passe avant : par tête ≻ décroissante, chaque ligne réduite contre
    -- les pivots de même tête puis indexée par sa tête (neuve) — ou
    -- annulée (ligne nulle = S-polynôme réduit à 0).
    forward      = foldl step Map.empty ordered
    ordered      = sortBy (comparing (Down . keyOf)) [ r | r <- rows, r /= zero ]
    keyOf r      = fst <$> leading r
    step pivs r  =
      let r' = reduceRow pivs r
      in case leading r' of
           Nothing     -> pivs
           Just (m, _) -> Map.insert m (monicB r') pivs
    reduceRow pivs r = case leading r of
      Nothing     -> r
      Just (m, c) -> case Map.lookup m pivs of
        Just p  -> reduceRow pivs (r `plus` scaleS (negate c) p)  -- r ← r − c·p (p unitaire)
        Nothing -> r
    -- Passe arrière (Gauss–Jordan) : chaque colonne-pivot effacée du
    -- /reste/ des autres lignes. Les pivots deviennent pleinement réduits
    -- — la forme échelonnée réduite. Sans elle, les queues non réduites
    -- s'accumulent dans la base et les coefficients sur ℚ explosent.
    backReduce pivs = foldl clearCol pivs (Map.keys pivs)
    clearCol acc m =
      let p = acc Map.! m
      in Map.map (\q -> let c = coefficient m q
                        in if leadIs m q || c == zero
                             then q
                             else q `plus` scaleS (negate c) p) acc
    leadIs m q = (fst <$> leading q) == Just m
    scaleS k p = fromTerms [ (mm, k `times` cc) | (mm, cc) <- toTerms p ]
-- END:backends-echelon

-- | Le monôme de tête (exposant) d'un polynôme non nul.
lmExp :: MonomialOrder o => MPoly o s -> Exp (Arity o)
lmExp p = case leading p of
  Just (m, _) -> toExp m
  Nothing     -> error "cauchy-backends : lmExp — la tête d'un polynôme nul"

-- | La tête (le monôme) d'un polynôme, en liste — vide si nul.
leadMon :: MPoly o s -> [o]
leadMon r = case leading r of
  Just (m, _) -> [m]
  Nothing     -> []

-- | Tête normalisée à lc = 1 (S corps : lc s'inverse).
monicB :: (MonomialOrder o, Field s, Ring s, Eq s) => MPoly o s -> MPoly o s
monicB p = case leading p of
  Nothing     -> p
  Just (_, c) -> fromTerms [ (m, b `E.quot` c) | (m, b) <- toTerms p ]

-- | x^e · p, l'opération de ligne élémentaire (le décalage monomial).
shiftBy :: (MonomialOrder o, Semiring s, Eq s)
        => Exp (Arity o) -> MPoly o s -> MPoly o s
shiftBy e p = fromTerms [(fromExp e, one)] `times` p

-- | La forme normale par échelonnage : une opération de ligne est un
-- pas de la division du volet 3. Même valeur que
-- 'Data.Cauchy.Groebner.nf' sur la même liste.
-- SNIPPET:backends-nf
-- NOTE:E.quot: S corps — annuler une tête inverse son coefficient de tête (via E.quot) ; l'hypothèse de l'arc Gröbner, reconduite. Chaque pas f ← f − (x^{m−lt d}·c/lc d)·d est une opération de ligne, la tête s'annule
nfF4 :: (MonomialOrder o, Field s, Ring s, Eq s)
     => MPoly o s -> [MPoly o s] -> MPoly o s
nfF4 p g = go p zero
  where
    g' = [ d | d <- g, d /= zero ]
    go f r = case leading f of
      Nothing     -> r
      Just (m, c) -> case red (toExp m) of
        -- une opération de ligne : f ← f − (x^{m−lt d}·c/lc d)·d, la tête s'annule
        Just (d, e, lcd) ->
          let factor = fromTerms [(fromExp e, c `E.quot` lcd)]
          in go (f `plus` negate (factor `times` d)) r
        -- aucune tête ne divise : le terme de tête passe au reste
        Nothing ->
          let lt = fromTerms [(m, c)]
          in go (f `plus` negate lt) (r `plus` lt)
    red me = listToMaybe
      [ (d, e, lcd)
      | d <- g', Just (lmd, lcd) <- [leading d]
      , Just e <- [me `minus` toExp lmd] ]
-- END:backends-nf
