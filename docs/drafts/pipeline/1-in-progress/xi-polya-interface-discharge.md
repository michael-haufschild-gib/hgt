# Xi Pólya interface discharge

- **ID:** xi-polya-interface-discharge
- **Stage:** 1-in-progress
- **Type:** CLASSICAL THEOREM — Lean formalization target
- **Source:** `XiEntireReal.lean`, `XiConvergenceExponent.lean`, `CanonicalProduct.lean`,
  `EntireHasLog.lean`, and `ReBoundAffine.lean`
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
- Locally uniform analyticity of genus-one canonical products.
- A zero-free entire function has an entire logarithm.
- An entire logarithm with the order-one real-part bound is affine.

## Open formal core

`[OPEN CORE]` Prove the Hadamard factorization of `XiC` from these inputs, including exact
multiplicities and locally uniform convergence of the finite real-root products under RH.  Evenness
then removes the affine exponential, and the resulting real-split partial products supply the three
pointwise derivative limits in `LaguerrePolya`.

## Gates

- [x] 0 → 1: all structural and convergence inputs identified in Lean
- [ ] 1 → 2: multiplicity-aware Hadamard factorization and real-root partial-product convergence
- [ ] 2 → 3: prove `riemannHypothesis_imp_laguerrePolya_Xi` and remove `hPolya` from the detector
- [ ] 3 → 4: axiom audit, formal lint, and documentation index
