# Infinite squarefree Möbius normalization

- **ID:** `infinite-squarefree-moebius-normalization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The squarefree indicator `mu^2` is normalized by the zeta function through
  the infinite identity `sum mu(n)^2/n^s = zeta(s)/zeta(2s)` on `re s > 1`, in all three
  classical faces: Dirichlet convolution, L-series, and Euler product.

## Exact relations

The single new primitive is the square dilation `sqrtPart f` of an arithmetic function,
`sqrtPart f (k^2) = f(k)` and `0` off squares.  It preserves multiplicativity because coprime
factors of a square are squares.  The formalized relations are

```text
sqrtPart mu ⍟ zeta = mu·mu            i.e.  sum_{d^2 | n} mu(d) = mu(n)^2      (1)
L(sqrtPart f, s) = L(f, 2s)           summability transferred both ways        (2)
L(mu, s) = zeta(s)^(-1)                                     on re s > 1        (3)
L(sqrtPart mu, s) = zeta(2s)^(-1)                           on re s > 1/2      (4)
L(mu·mu, s) = zeta(s)/zeta(2s)                              on re s > 1        (5)
sum' n, [Squarefree n]/n^s = zeta(s)/zeta(2s)               on re s > 1        (6)
prod' p, (1 + p^(-s)) = zeta(s)/zeta(2s)                    on re s > 1        (7)
```

## Proof

`(1)` both sides are multiplicative (dilation preserves multiplicativity; convolution with
`zeta` and pointwise squaring preserve it), so equality reduces to prime powers, where the
divisor sum telescopes to `1` at `p^0, p^1` and to `1 - 1 = 0` at `p^i`, `i >= 2`.
`(2)` the L-series terms of `sqrtPart f` vanish off squares, and reindexing along the
injection `k -> k^2` turns the term at `k^2` into the term of `f` at `2s`, via
`(k^2)^s = k^(2s)` for natural bases.  `(3)` is division in `L(zeta,s)·L(mu,s) = 1`.
`(4)` is `(2)` + `(3)` at the doubled variable, hence convergence on `re s > 1/2`.
`(5)` casts `(1)` to complex coefficients and multiplies out with the convolution theorem;
`(6)` rewrites the coefficients by `mu(n)^2 = [Squarefree n]`; `(7)` applies the general
Euler product for multiplicative arithmetic functions to the squarefree cpow kernel, whose
local factor at `p` is `1 + p^(-s)`.

## Parent classification

`[SEARCH]` These are the classical Möbius/squarefree Dirichlet series identities
(Hardy–Wright, *An Introduction to the Theory of Numbers*, ch. XVII; DLMF §27.4,
https://dlmf.nist.gov/27.4).  Mathematically standard; the formalization is not new
scientific knowledge.

## Prior-state audit

Absent from the pinned mathlib checkout: the square dilation, any L-series statement for the
squarefree indicator, the `zeta(s)/zeta(2s)` normalization in any face, and even the direct
form `L(mu, s) = zeta(s)^(-1)` (mathlib states only `L(zeta,s)·L(mu,s) = 1`,
`Mathlib/NumberTheory/LSeries/Dirichlet.lean`).  Mathlib supplies the pointwise
`moebius_sq`, the convolution and Euler-product machinery, and the `zeta` L-series bricks.
Absent from the local tree: all Möbius material was finite-support
(`RHTower/Mollifier.lean` truncated mollifier, `RHTower/PrimeLambertMobiusInversion.lean`
divisor-antidiagonal inversion, `RHProofLab/EulerProductArithmetic.lean` finite local Euler
products); no infinite squarefree normalization existed.

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/SquarefreeMoebiusNormalization.lean`.

- `sqrtPart`, `isMultiplicative_sqrtPart`: the square dilation and its multiplicativity;
- `sqrtPart_moebius_mul_zeta`, `sum_divisors_sqrtPart_moebius`: relation `(1)`;
- `LSeries_sqrtPart`, `LSeriesSummable_sqrtPart_iff`: relation `(2)`;
- `LSeries_moebius_eq_inv_riemannZeta`: relation `(3)`;
- `LSeries_sqrtPart_moebius`, `LSeriesSummable_sqrtPart_moebius`: relation `(4)` on
  `re s > 1/2`;
- `LSeries_squarefree_mul_riemannZeta_two_mul`, `LSeries_squarefree_eq_riemannZeta_div`:
  relation `(5)`;
- `tsum_squarefree_cpow`: relation `(6)`;
- `squarefreeCpow`, `isMultiplicative_squarefreeCpow`, `summable_norm_squarefreeCpow`,
  `tsum_squarefreeCpow_prime_pow`, `squarefree_eulerProduct_tprod`: relation `(7)`.

The module is imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] local tree and mathlib declaration search confirms the infinite normalization was absent
- [x] arithmetic, L-series, and Euler-product faces formalized
- [x] dilation lemma stated for arbitrary arithmetic functions (reusable beyond Möbius)
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `SquarefreeMoebiusNormalization`; the independent
existing failures are `SummableEulerCalkinInjectivity.lean` and
`ExponentialGaugeSelection.lean`, which do not depend on this module.  All twelve public
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Opens

The dilation law `(2)` is the `m = 2` case of `L(mPart f, s) = L(f, ms)` for the `m`-th
power dilation; the same reindexing gives every `m`, and with it
`sum [n is m-free]/n^s = zeta(s)/zeta(ms)` — the full `m`-free normalization ladder.
Relation `(4)` gives a Dirichlet series for `zeta(2s)^(-1)` convergent on `re s > 1/2`, a
native half-plane object for the critical-strip carriers already in the tree.
