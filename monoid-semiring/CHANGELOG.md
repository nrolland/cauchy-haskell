# Revision history for monoid-semiring

## 0.1.0.0 — 2026-06-11

* First release. The monoid semiring `M →₀ S`: finitely supported functions
  from a monoid `M` to a semiring `S` (the `Semiring` class of the
  `semirings` package), multiplied by the generalized Cauchy product
  `(f * g)(s) = Σ_{uv = s} f(u) · g(v)`.
* Representation invariant: no explicit zero coefficients, so derived
  equality coincides with equality of functions.
* Oracle test suite: the seven semiring laws at three `(M, S)` instances
  (polynomials, formal languages, tropical multivariate), differential
  test against the naive definition, Fibonacci (A000045) and Catalan
  (A000108) generating-function coefficients against vendored OEIS b-files.
