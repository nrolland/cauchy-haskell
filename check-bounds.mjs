#!/usr/bin/env node
// Filet des bornes des cabals PUBLIÉS. Deux contrôles, le second optionnel :
//
//   A. Omission (toujours, ÉCHEC DUR) — chaque dépendance EXTERNE porte
//      plancher (>=) ET plafond (<), test-suites comprises. `cabal check` ne
//      vérifie les bornes que des bibliothèques ; ce filet couvre le trou des
//      test-suites, là où un plafond oublié (QuickCheck, process) casse chez
//      un aval qui teste. Statique, sans compilateur : tourne dans le pré-vol.
//
//   B. Plafond-vs-testé (si un gel cabal est donné) — compare chaque plafond
//      à la version RÉSOLUE (ce contre quoi on a compilé). C'est le geste de
//      `gen-bounds`, automatisé. Sa nature est CONSULTATIVE :
//        - plafond plus large que le majeur du testé ⇒ AVERTISSEMENT (peut
//          être voulu : `base <5`, une fourchette élargie à dessein — un
//          humain juge ; ne bloque pas) ;
//        - plafond qui EXCLUT le testé ⇒ échec dur (contradiction réelle).
//      `base` est exclu de l'avertissement (plafond large conventionnel).
//      Exige un plan résolu : ne tourne qu'en CI, après `cabal freeze`.
//
// « Externe » = tout sauf la famille cauchy et l'auto-dépendance.
//
// Usage : node check-bounds.mjs <arbre fusionné> [cabal.project.freeze]
// Sort non nul sur tout échec dur (jamais sur un simple avertissement).

import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

const root = process.argv[2];
const freeze = process.argv[3];
if (!root) {
  console.error('check-bounds.mjs : racine de l\'arbre fusionné manquante (argv[2])');
  process.exit(1);
}

const PUBLISHED = [
  ['monoid-semiring', 'monoid-semiring/monoid-semiring.cabal'],
  ['cauchy', 'cauchy/cauchy.cabal'],
  ['cauchy-backends', 'cauchy-backends/cauchy-backends.cabal'],
];

const leading = (s) => s.match(/^ */)[0].length;
const stripComment = (s) => { const i = s.indexOf('--'); return i < 0 ? s : s.slice(0, i); };

// Texte concaténé de tous les blocs build-depends d'un cabal. Fin de bloc par
// indentation : la continuation est plus indentée que le champ.
function buildDependsBlocks(text) {
  const lines = text.split('\n');
  const blocks = [];
  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(/^(\s*)build-depends:(.*)$/i);
    if (!m) continue;
    const fieldIndent = m[1].length;
    let acc = stripComment(m[2]);
    let j = i + 1;
    for (; j < lines.length; j++) {
      const line = lines[j];
      if (line.trim() === '') break;
      if (leading(line) <= fieldIndent) break;
      acc += ' ' + stripComment(line);
    }
    blocks.push(acc);
    i = j - 1;
  }
  return blocks;
}

const depName = (entry) => entry.trim().split(/\s+/)[0];
const isInternal = (name, pkg) => /^cauchy(\b|[:-])/.test(name) || name === pkg;
const hasLower = (e) => /(>=|\^>=|==|>)/.test(e);
const hasUpper = (e) => /(<|\^>=|==)/.test(e);

// Comparaison de versions (composant par composant) et prochain majeur PVP.
const parseVer = (s) => s.split('.').map(Number);
const cmp = (a, b) => {
  const n = Math.max(a.length, b.length);
  for (let i = 0; i < n; i++) { const d = (a[i] || 0) - (b[i] || 0); if (d) return Math.sign(d); }
  return 0;
};
const nextMajor = (v) => [v[0] || 0, (v[1] || 0) + 1];          // PVP : A.B -> A.(B+1)
const declaredUpper = (e) => { const m = e.match(/<\s*([0-9]+(?:\.[0-9]+)*)/); return m ? m[1] : null; };

// Versions résolues depuis un gel cabal : « any.NOM ==X.Y.Z ».
function resolvedVersions(path) {
  const map = {};
  for (const m of readFileSync(path, 'utf8').matchAll(/any\.([A-Za-z0-9-]+)\s*==\s*([0-9.]+)/g)) {
    map[m[1]] = m[2];
  }
  return map;
}

const resolved = freeze ? resolvedVersions(freeze) : null;

let fail = 0;
const allWarns = [];
for (const [pkg, rel] of PUBLISHED) {
  const path = join(root, rel);
  if (!existsSync(path)) {
    console.error(`>> ÉCHEC : cabal publié absent : ${rel}`);
    fail = 1;
    continue;
  }
  const entries = buildDependsBlocks(readFileSync(path, 'utf8'))
    .flatMap((b) => b.split(','))
    .map((e) => e.trim())
    .filter(Boolean);

  const hard = [];   // échecs durs : omission, ou plafond excluant le testé
  const warn = [];   // avertissements : plafond plus large que le testé
  const seen = new Set();
  for (const e of entries) {
    const name = depName(e);
    if (isInternal(name, pkg) || seen.has(e)) continue;
    seen.add(e);

    // A. omission (dur)
    if (!hasLower(e) || !hasUpper(e)) {
      hard.push(`omission : ${e}${hasLower(e) ? ' (plafond manquant)' : ' (bornes manquantes)'}`);
      continue;
    }

    // B. plafond-vs-testé (si gel fourni et plafond explicite « <X » connu)
    const up = declaredUpper(e);
    if (resolved && up && resolved[name]) {
      const U = parseVer(up), R = parseVer(resolved[name]), exp = nextMajor(R);
      if (cmp(U, R) <= 0) {
        hard.push(`plafond : ${name} <${up} exclut le testé ${resolved[name]}`);
      } else if (name !== 'base' && cmp(U, exp) > 0) {
        warn.push(`${pkg}: ${name} <${up} > testé ${resolved[name]} (gen-bounds dirait <${exp.join('.')})`);
      }
    }
  }

  if (hard.length) {
    console.error(`>> ÉCHEC : ${pkg} —`);
    for (const h of hard) console.error(`     ${h}`);
    fail = 1;
  } else {
    const mode = resolved ? 'plancher + plafond ; plafonds vérifiés vs testé' : 'plancher + plafond';
    console.log(`>> OK : ${pkg} — externes bornés (${mode})`);
  }
  allWarns.push(...warn);
}

if (allWarns.length) {
  console.log('\n-- avertissements (plafonds plus larges que le testé ; voulus ou à resserrer, au choix) --');
  for (const w of allWarns) console.log(`   ⚠ ${w}`);
}

process.exit(fail);
