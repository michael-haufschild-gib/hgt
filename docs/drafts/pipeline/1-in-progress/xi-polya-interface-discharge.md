# Xi Pólya interface discharge

- **ID:** xi-polya-interface-discharge
- **Stage:** 1-in-progress
- **Type:** CLASSICAL THEOREM — Lean formalization target
- **Source:** `XiEntireReal.lean`, `XiConvergenceExponent.lean`, `CanonicalProduct.lean`,
  `XiCanonicalProduct.lean`, `XiHadamardFactorization.lean`, `EntireHasLog.lean`, and
  `ReBoundAffine.lean`
- **Statement:** `[PROVED, classical]` Under the Riemann hypothesis, the real critical-line
  restriction `Xi` lies in the Laguerre--Pólya class.  Consequently a strict failure of the first
  Laguerre inequality refutes RH without an assumed `hPolya` interface.

## Goal

Replace the argument `hPolya : RiemannHypothesis → LaguerrePolya Xi` in
`LaguerreInequality.lean` by an axiom-clean theorem.  This is a one-way classical consequence of RH,
not an attempted positivity proof of RH.

## Existing formal inputs

- `XiC_differentiable`, `XiC_even`, `XiC_ofReal`, and `XiC_order`.
- Square-summability of the multiplicity-weighted xi divisor.
- Locally uniform analyticity and non-accidental-zero control for genus-one canonical products over
  arbitrary index types.
- The actual Xi divisor expanded into a sigma type of exact multiplicity copies, with no chosen
  enumeration.
- The resulting canonical product has the same zero set and the same analytic order as `XiC` at
  every point.
- Filling the removable singularities of `XiC / xiCanonicalProduct` gives the entire nowhere-zero
  `xiHadamardQuotient`, with the exact identity
  `xiHadamardQuotient * xiCanonicalProduct = XiC`.
- A zero-free entire function has an entire logarithm.
- An entire logarithm with the order-one real-part bound is affine.

## Open formal core

`[OPEN CORE]` Prove the Hadamard growth step for the now-constructed zero-free entire quotient:
its entire logarithm has degree at most one.  This is the remaining minimum-modulus / Jensen part
of the classical order-one factorization, not a divisor or removable-singularity gap.  Then prove
the divisor-reflection reindexing that makes the canonical product even; evenness removes the
linear exponential.  Under RH, symmetric finite subproducts are real-split polynomials, and local
uniform convergence supplies the first two derivative limits required by `LaguerrePolya`.

## Gates

- [x] 0 → 1: all structural and convergence inputs identified in Lean
- [ ] 1 → 2: quotient growth-to-affine, even reindexing, and real-root partial-product convergence
- [ ] 2 → 3: prove `riemannHypothesis_imp_laguerrePolya_Xi` and remove `hPolya` from the detector
- [ ] 3 → 4: axiom audit, formal lint, and documentation index
