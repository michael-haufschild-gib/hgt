# Elliptic-gamma additive clock factorization

- **ID:** `elliptic-gamma-additive-clock-factorization`
- **Stage:** 3-formalized
- **Type:** EXACT VALUE RELATION / HYPOTHESIS DISCHARGE
- **Scientific status:** `[KNOWN MATHEMATICS] [LEAN-FORMALIZED] [CORPUS-STRENGTHENING]`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/EllipticGammaProductCommensurableFactorization.lean`
- **Applied route:**
  `../../1-in-progress/elliptic-gamma-qft-arithmetic-closure-horizon.md`

## Exact clock relation

For additive periods `sigma,tau` and natural numbers `m,n`, the nome definition gives

```text
ellipticNome(sigma)^m = ellipticNome(tau)^n
  <=> exists k in Z, m*sigma = n*tau + k.
```

This is formalized as
`ellipticNome_pow_eq_pow_iff_additivePeriodCongruence`.

The integer is not an error term.  It is the period-one large-gauge lattice killed by the
exponential coordinate.  The theorem therefore identifies multiplicative nome dependence with
additive clock commensurability modulo the observable's gauge lattice.

## Hypothesis discharge

The existing actual-product theorem required a chosen common nome `P` and two hypotheses

```text
ellipticNome(sigma)^m = P,
ellipticNome(tau)^n = P.
```

`ellipticGammaProduct_additivePeriod_factorization` now consumes only

```text
exists k in Z, m*sigma = n*tau + k,
```

chooses `P = ellipticNome(sigma)^m`, and proves the actual elliptic-gamma product equals its
flattened finite equal-nome family.

This is the parameter form used by supersymmetric indices and partition functions, so the result
removes an artificial multiplicative-coordinate interface from the physics-facing theorem.

## HT boundary

The factorization is not by itself a DA or HT theorem.  Kato proves DA for the rational-period
multiple elliptic gamma, while the non-rational case is open in that source.  The remaining Lean
work for the dependent phase is to identify the flattened family with a literal finite product and
internalize the equal-nome differential equation.  The additive commensurability hypothesis is no
longer a gap.

## Clock interpretation

The observable forgets integer shifts of the additive period because they exponentiate to one.
Commensurability is therefore a statement about what the clock readout can distinguish, not how a
state evolves in time.

## Verification

The exact module target and direct file check passed.  Both declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
