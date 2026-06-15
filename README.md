# cauchy-haskell

Haskell packages of the *cauchy* family — the Cauchy product `f*g` over a
monoid semiring, from first principles up to fast backends.

- **[monoid-semiring](https://hackage.haskell.org/package/monoid-semiring)**
  [![Hackage](https://img.shields.io/hackage/v/monoid-semiring.svg)](https://hackage.haskell.org/package/monoid-semiring)
  — finitely supported functions from a monoid `M` to a semiring `S`, multiplied
  by convolution `(f*g)(s) = Σ_{uv=s} f(u)·g(v)` (the generalized Cauchy
  product). Polynomials, formal languages, and tropical algebra are instances.
- **cauchy** — the collection (phases 1–4) as one package: univariate
  polynomials and lazy power series, languages and weighted automata, monomial
  orders on `Nᵏ`, and Gröbner bases — all as the Cauchy product, generic in the
  semiring `S`. Built on `monoid-semiring`. *(not yet on Hackage)*
- **cauchy-backends** — the fast-path layer (phase 5): NTT convolution and F4.
  Same answers, faster — a second path to the same value, checked against the
  pure `cauchy` package as referee. *(not yet on Hackage)*

This repository is a **read-only publish target**: snapshots of the `haskell/`
subtree of a private development repository, pushed at release time. Issues and
bug reports are welcome here; pull requests cannot be merged directly, but
patches posted in an issue will be applied upstream.
