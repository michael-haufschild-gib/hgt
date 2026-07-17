# Geometric periodic level exactness with a finite exceptional Taylor prefix

- **ID:** `geometric-periodic-fixed-ade-finite-prefix-extension`
- **Stage:** 1-in-progress
- **Type:** FIXED-RELATION FINITE-PREFIX EXTENSION
- **Status:** `[OPEN] [STATEMENT DEFECT ISOLATED]`

## Claim under investigation

Let `f(z)=sum a_n z^n` have `-log|a_n|=A lambda^n+c>0` and nonzero coefficients only from some
index `n_0` onward, with eventually periodic unit phases. Fix one particular nonzero integer ADE
`P(z,f,...,f^(m))=0`. Prove the level-exactness identities for the coefficient identity of this
same `P`, including every residue and every admissible valuation level.

## Why this is separate

Subtracting the Taylor prefix preserves differential algebraicity and therefore suffices for an
existential hypertranscendence contradiction. It does not preserve the particular polynomial `P`
whose grouped coefficient levels are being classified. The former pipeline card silently used
that stronger inference.

## Existing formal base

`GeometricPeriodicEveryLevel.lean` proves the positive exact all-index law unconditionally. A
completion here must directly show that atoms meeting the finite exceptional prefix either vanish
or lie in the exponentially negligible active complement, while retaining the grouped weights of
the original fixed ADE.

## Completion gate

- Construct a source-faithful finite-prefix active-atom decomposition for the original `P`.
- Prove its exceptional-prefix remainder is negligible at every target geometric level.
- Reuse `periodicGeometricLevelPolynomial_eq_zero_of_activeComplement_gap` without changing `P`.
