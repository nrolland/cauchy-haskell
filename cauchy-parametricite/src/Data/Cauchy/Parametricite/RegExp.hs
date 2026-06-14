-- | Le semi-anneau des expressions rationnelles : @(∅, ε, +, ·, *)@ — le
-- porteur sur lequel l'étoile matricielle (l'élimination de Lehmann)
-- calcule l'expression régulière d'un automate (théorème de Kleene). Les
-- constructeurs intelligents normalisent (absorption de @∅@/@ε@,
-- idempotence du @+@) pour que le rendu soit propre : @star(a)·b·star(c)@
-- s'imprime @a*bc*@, pas @(a*·(b·c*))@ encombré de @ε@.
--
-- Porte d'écosystème (verdict daté 2026-06-13) : @kleene@ (phadej, 0.2,
-- 2026-05-12) possède bien un type d'expression rationnelle à structure
-- d'algèbre de Kleene, inspectable et imprimable (@Kleene.RE@). Il est
-- pourtant /écarté/, pour la raison même qui a écarté @semiring-num@ à la
-- porte des scalaires : il apporte sa /propre/ classe d'algèbre de Kleene,
-- concurrente du 'Data.Star' de @semirings@ que toute la collection partage
-- — or la thèse du volet est « une /même/ étoile, des réalisations » :
-- 'RegExp' doit être une instance du même 'Data.Star' que 'Series' et
-- 'Matrix', pas d'une classe rivale. S'y ajoute une empreinte de 9 dépendances
-- (lattices, MemoTrie, range-set-list, step-function…) pour un type d'une
-- quarantaine de lignes. Vendoriser est donc justifié : 'RegExp' est une
-- instance du 'Data.Star' commun et un /arbitre/ — l'expression produite se
-- duelle contre @regex-applicative@ (l'oracle 'test/Duels.hs').
module Data.Cauchy.Parametricite.RegExp
  ( RegExp
  , atom
  , render
  , foldRegExp
  ) where

import Data.Semiring (Semiring (..))
import Data.Star (Star (..))

-- | Une expression rationnelle sur un alphabet de 'Char'.
data RegExp
  = Empty                 -- ^ @∅@ : le langage vide (zéro)
  | Eps                   -- ^ @ε@ : le mot vide (un)
  | Sym Char              -- ^ une lettre
  | Alt RegExp RegExp     -- ^ @+@ : l'union
  | Seq RegExp RegExp     -- ^ @·@ : la concaténation
  | Rep RegExp            -- ^ @*@ : l'étoile de Kleene
  deriving (Eq, Show)

-- | L'expression réduite à une lettre.
atom :: Char -> RegExp
atom = Sym

-- | Le repli universel sur la syntaxe (catamorphisme) : l'unique observateur
-- de la structure. Il laisse brancher un moteur de reconnaissance externe —
-- la dénotation par @regex-applicative@, la sémantique des langages à la
-- main — /sans/ exposer les constructeurs, qui resteraient sinon libres de
-- bâtir une expression hors forme normale. Les oracles l'emploient ;
-- l'invariant des constructeurs intelligents reste scellé.
foldRegExp
  :: r                 -- ^ @∅@
  -> r                 -- ^ @ε@
  -> (Char -> r)       -- ^ une lettre
  -> (r -> r -> r)     -- ^ @+@
  -> (r -> r -> r)     -- ^ @·@
  -> (r -> r)          -- ^ @*@
  -> RegExp -> r
foldRegExp z e sym alt seq_ rep = go
  where
    go Empty     = z
    go Eps       = e
    go (Sym c)   = sym c
    go (Alt a b) = alt (go a) (go b)
    go (Seq a b) = seq_ (go a) (go b)
    go (Rep a)   = rep (go a)

-- Constructeurs intelligents : ils portent les lois d'absorption qui
-- gardent les expressions petites — sans eux, l'élimination de Lehmann
-- accumulerait des @ε@ et des @∅@ parasites.
rAlt :: RegExp -> RegExp -> RegExp
rAlt Empty b = b
rAlt a Empty = a
rAlt a b
  | a == b    = a
  | otherwise = Alt a b

rSeq :: RegExp -> RegExp -> RegExp
rSeq Empty _ = Empty
rSeq _ Empty = Empty
rSeq Eps b   = b
rSeq a Eps   = a
rSeq a b     = Seq a b

rRep :: RegExp -> RegExp
rRep Empty = Eps
rRep Eps   = Eps
rRep a     = Rep a

instance Semiring RegExp where
  zero  = Empty
  one   = Eps
  plus  = rAlt
  times = rSeq

instance Star RegExp where
  star = rRep

-- | Rendu avec le minimum de parenthèses : @+@ lie le plus lâche,
-- puis @·@, puis @*@ le plus fort.
render :: RegExp -> String
render = go (0 :: Int)
  where
    go _ Empty     = "\8709"             -- ∅
    go _ Eps       = "\949"              -- ε
    go _ (Sym c)   = [c]
    go p (Alt a b) = paren (p > 1) (go 1 a ++ "+" ++ go 1 b)
    go p (Seq a b) = paren (p > 2) (go 2 a ++ go 2 b)
    go _ (Rep a)   = go 3 a ++ "*"
    paren True  s  = "(" ++ s ++ ")"
    paren False s  = s
