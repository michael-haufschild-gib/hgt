# m-free Möbius ladder and the off-line carrier bridge

- **ID:** `mfree-moebius-ladder-carrier-bridge`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The square dilation is the `m = 2` rung of the full dilation ladder
  `L(mPart m f, s) = L(f, ms)`; the same reindexing gives every rung of the `m`-free
  normalization `sum [n is m-free]/n^s = zeta(s)/zeta(ms)` on `re s > 1`, and each
  `zeta(mz)^(-1)` is the atTop limit of the tree's own off-line carrier polynomials
  `dpoly2` on `re z > 1/m` — for `m = 2` a critical-strip-adjacent object with
  mollifier-grade coefficients.

## Exact relations

For `m >= 1`, with `mPart m f (k^m) = f k` (zero off `m`-th powers) and
`MFree m n = no p^m divides n`:

```text
mPart m mu ⍟ zeta = [·, m-free]      i.e.  sum_{d^m | n} mu(d) = [n is m-free]   (1)
L(mPart m f, s) = L(f, ms)           summability transferred both ways           (2)
L(mPart m mu, s) = zeta(ms)^(-1)                          on re s > 1/m          (3)
sum' n, [n is m-free]/n^s = zeta(s)/zeta(ms)              on re s > 1            (4)
dpoly2 a (Icc 1 N) z -> L(a, z)      for any summable real coefficients          (5)
dpoly2 moebiusCoeff (Icc 1 N) z -> zeta(z)^(-1)           on re z > 1            (6)
dpoly2 sqrtMoebiusCoeff (Icc 1 N) z -> zeta(2z)^(-1)      on re z > 1/2          (7)
dpoly2 (mPartMoebiusCoeff m) (Icc 1 N) z -> zeta(mz)^(-1) on re z > 1/m          (8)
```

`m = 2` recovers the squarefree module exactly: `mPart 2 = sqrtPart` and
`[·, 2-free] = mu·mu`.

## Proof

`(1)` both sides are multiplicative (coprime factors of an `m`-th power are `m`-th powers
by GCD-monoid power splitting; `m`-freeness splits over coprime factors by prime-power
transfer `Prime.pow_dvd_of_dvd_mul_left`), so equality reduces to prime powers `p^i`,
where the divisor sum collapses to `1` for `i < m` and `1 - 1 = 0` for `i >= m`.
`(2)` the terms of `mPart m f` vanish off `m`-th powers; reindexing along the injection
`k -> k^m` turns the term at `k^m` into the term of `f` at `ms`, via
`(k^m)^s = k^(ms)` for natural bases (induction from the two-factor `cpow` split).
`(3)` is `(2)` + `L(mu) = zeta^(-1)` at the `m`-fold variable, hence convergence on
`re s > 1/m`.  `(4)` casts `(1)` to complex coefficients and multiplies out with the
convolution theorem.  `(5)` is the partial-sum form of L-series summability: `HasSum`
implies convergence of range sums, and the range sum equals the `Icc 1 N` carrier
polynomial because the `0`-term vanishes.  `(6)`–`(8)` instantiate `(5)` with the Möbius
and dilated-Möbius coefficient sequences.

## Parent classification

`[SEARCH]` The `m`-free Dirichlet series `zeta(s)/zeta(ms)` is classical
(Hardy–Wright, *An Introduction to the Theory of Numbers*, ch. XVII; DLMF §27.4,
https://dlmf.nist.gov/27.4).  Truncation convergence of a Dirichlet series on its
half-plane of absolute convergence is elementary.  Not new scientific knowledge; the
formalization and the wiring into the tree's carrier machinery are new to the tree.

## Prior-state audit

Absent from the pinned mathlib checkout: any `m`-th power dilation, any `m`-free
(powerfree) predicate or indicator, and every relation `(1)`–`(4)` for any `m` (the
`m = 2` case was banked in `SquarefreeMoebiusNormalization.lean` by the predecessor card
`infinite-squarefree-moebius-normalization`).  Absent from the local tree: all of the
above, plus any link between the mollifier/carrier Dirichlet polynomials and L-series
limits — `DpolyOffline.lean` controls `dpoly2` variation between real parts but had no
convergence statement.

## Reuse audit

Built directly on existing tree infrastructure, no duplication:

- `SquarefreeMoebiusNormalization.lean`: `sqrtPart` (identified as `mPart 2`),
  `natCast_mul_cpow` (the induction step of `natCast_pow_cpow`),
  `LSeries_moebius_eq_inv_riemannZeta` (the `zeta^(-1)` endpoint of every rung),
  `sqrtPart_apply_*` lemmas (the `m = 2` identification), `intCoe_natCoe`;
- `Mollifier.lean`: `moebiusCoeff` (its off-line limit is now `(6)`),
  `abs_moebius_le_one`;
- `DpolyOffline.lean`: `dpoly2` (the carrier object of `(5)`–`(8)`);
- `SecondMoment.lean`: `dpoly`, `cosInt`, `secondMoment_meanValue` (instantiated at the
  square-dilated coefficients);
- mathlib: `exists_eq_pow_of_mul_eq_pow`, `eq_iff_eq_on_prime_powers`,
  `LSeries_mul'`, `Prime.pow_dvd_of_dvd_mul_left/right`,
  `Nat.squarefree_iff_prime_squarefree`, `HasSum.tendsto_sum_nat`.

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/MFreeLadder.lean`.

- `mPart`, `mPart_apply_pow`, `mPart_apply_of_forall_pow_ne`, `mPart_two_eq_sqrtPart`,
  `isMultiplicative_mPart`, `mPart_intCoe`: the dilation and its algebra;
- `MFree`, `mFree_two_iff_squarefree`, `mFree_mul_iff`, `mFreeIndicator`,
  `mFreeIndicator_two`, `isMultiplicative_mFreeIndicator`: the `m`-free indicator;
- `mPart_moebius_mul_zeta`, `sum_divisors_mPart_moebius`: relation `(1)`;
- `natCast_pow_cpow`, `term_mPart_pow`, `LSeriesSummable_mPart_iff`, `LSeries_mPart`:
  relation `(2)`;
- `LSeriesSummable_mPart_moebius`, `LSeries_mPart_moebius`: relation `(3)`;
- `LSeries_mFree_mul_riemannZeta`, `LSeries_mFree_eq_riemannZeta_div`,
  `tsum_mFree_cpow`: relation `(4)`;
- `tendsto_dpoly2_Icc_of_LSeriesSummable`: relation `(5)`;
- `moebiusCoeff_complex`, `tendsto_dpoly2_moebiusCoeff`: relation `(6)`;
- `sqrtMoebiusCoeff`, `sqrtMoebiusCoeff_eq_mPart`, `abs_sqrtMoebiusCoeff_le_one`,
  `tendsto_dpoly2_sqrtMoebiusCoeff`, `sqrtMollifier_secondMoment`: relation `(7)` with
  mollifier-grade coefficient bound and Montgomery–Vaughan second moment;
- `mPartMoebiusCoeff`, `mPartMoebiusCoeff_complex`, `abs_mPartMoebiusCoeff_le_one`,
  `tendsto_dpoly2_mPartMoebiusCoeff`: relation `(8)`.

The module is imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] local tree and mathlib declaration search confirms the ladder and bridge were absent
- [x] all rungs stated for every `m ≠ 0`, unconditional hypotheses only
      (`re s` half-planes)
- [x] `m = 2` rung machine-identified with the banked square-dilation module
- [x] bridge stated against the tree's native carrier objects (`dpoly2`, `dpoly`,
      `moebiusCoeff`, `secondMoment_meanValue`)
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `MFreeLadder`; the independent existing failure is
`SummableEulerCalkinInjectivity.lean`, which does not depend on this module.  All 22
public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Opens

Relation `(7)` puts `zeta(2z)^(-1)` inside the `dpoly2` floor machinery of
`DpolyOffline.lean`: a line floor for the square-dilated carrier at `re z = 1/2 + δ`
transfers along `dpoly2_chart_floor` with the mollifier-grade variation budget
`sum |a_n|·|n^(-σ₁) - n^(-σ₂)|`, so the next object is a quantitative tail bound for
`dpoly2 sqrtMoebiusCoeff` on `re z ≥ 1/2 + δ` (effective `N(δ, ε)`), which would make the
limit `(7)` a finite-cutoff certificate.  On the arithmetic side, `(1)` for varying `m`
composes: `mPart` of an indicator is again an indicator-type function, opening the
iterated ladder `zeta(s)/zeta(ms)`, `zeta(ms)/zeta(m²s)`, … as a telescoping tower of
carrier limits over nested half-planes `re s > 1/m^k`.
