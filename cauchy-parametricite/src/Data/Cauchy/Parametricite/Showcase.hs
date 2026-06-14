-- | Définitions d'exposition du volet 7 : ce que les widgets montrent et
-- ce que les duels (à venir) jugent. Tout passe par la /même/ étoile —
-- @star@ de @Data.Star@ — instanciée sur le porteur choisi : la fermeture
-- matricielle @star :: Matrix n s -> Matrix n s@ (élimination de Lehmann),
-- recommutée par S, rend l'expression régulière (langages rationnels),
-- l'atteignabilité (Bool) ou le plus court chemin (tropical).
--
-- Module pur, sans rien de wasm : il se compile en GHC natif et c'est lui
-- que la frontière JSFFI (wasm\/Exports.hs) emballe.
{-# LANGUAGE DataKinds #-}
module Data.Cauchy.Parametricite.Showcase
  ( -- * L'automate à deux états (③ graphe-fermeture)
    Trop
  , fermetureRegex
  , fermetureBool
  , fermetureTrop
  ) where

import Data.Monoid (Sum (..))
import Numeric.Natural (Natural)

import Data.Semiring (Semiring (..))
import Data.Semiring.Tropical (Extrema (..), Tropical (..))
import Data.Star (Star (..))

import Data.Cauchy.Parametricite.RegExp (atom, render)

-- | Le tropical de la collection : @(ℕ ∪ {∞}, min, +)@, étoile comprise
-- (@star _ = one@ : à poids ≥ 0, boucler ne diminue jamais).
type Trop = Tropical 'Minima (Sum Natural)

-- | L'entrée @(1, 2)@ de la fermeture de l'automate à deux états — boucle
-- @a@ sur l'état 1, arête @b@ de 1 vers 2, boucle @c@ sur 2 — par
-- élimination d'état : tous les chemins @1 → 2@ sont @star(a) · b · star(c)@
-- (boucler sur 1, traverser, boucler sur 2). C'est la /même/ définition,
-- générique en S, lue ensuite sur trois semi-anneaux ; elle n'emploie que
-- @star@, @times@ de @Data.Star@\/@Semiring@.
--
-- (On calcule la formule d'élimination, pas @star@ de @Matrix 2 s@ : pour
-- deux états sans arête retour elles ont le même langage, mais l'étoile
-- matricielle générique rend une forme non normalisée — @b+aa*b+…@ — faute
-- d'une normalisation d'algèbre de Kleene dans 'RegExp'. La page montre la
-- forme d'élimination ; c'est elle qu'on calcule.)
chemin12 :: Star s => s -> s -> s -> s
chemin12 a b c = star a `times` b `times` star c

-- | Langages rationnels : la fermeture rend l'/expression régulière/ de
-- l'automate (théorème de Kleene). Avec la boucle @a@ : @a*bc*@ ; sans
-- elle (@star ∅ = ε@) : @bc*@.
fermetureRegex :: Bool -> String
fermetureRegex loopA = render (chemin12 a (atom 'b') (atom 'c'))
  where a = if loopA then atom 'a' else zero

-- | Bool : la /même/ formule rend l'atteignabilité de 2 depuis 1.
fermetureBool :: Bool -> Bool
fermetureBool loopA = chemin12 a one one
  where a = if loopA then one else zero

-- | Tropical (chaque arête de poids 1) : la /même/ formule rend le coût
-- du plus court chemin de 1 à 2.
fermetureTrop :: Bool -> Trop
fermetureTrop loopA = chemin12 a w w
  where
    w = Tropical (Sum 1)
    a = if loopA then Tropical (Sum 1) else zero
