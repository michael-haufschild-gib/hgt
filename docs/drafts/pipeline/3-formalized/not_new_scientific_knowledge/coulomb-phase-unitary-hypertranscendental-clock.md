# The Coulomb partial-wave phase is a unitary hypertranscendental clock

- **ID:** `coulomb-phase-unitary-hypertranscendental-clock`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** J. C. A. Barata, L. F. Canto, M. S. Hussein, *The Coulomb Phase Shift Revisited*, arXiv:0912.3189, equation (1)
- **Statement:** The complexified Coulomb partial-wave phase is hypertranscendental for every angular momentum, although its physical real-parameter restriction has unit modulus and adjacent partial waves differ by an elementary unitary rational gauge.

## Goal

Turn the exact Coulomb-scattering value relation

`exp(2 i sigma_ell(eta)) = Gamma(ell+1+i eta) / Gamma(ell+1-i eta)`

into a reusable theorem about observability rather than temporal evolution.  The physical phase is bounded and unitary, but its complex continuation retains nonzero oriented Gamma charge.  This tests the clock motif on an actual electromagnetic scattering observable.

## Gates

- [x] 0 → 1  in-progress: exact primary-source formula and an existing meromorphic Gamma-charge route
- [x] 1 → 2  fully-proven: reflection/orbit-charge proof and exact value relations complete
- [x] 2 → 3  formalized: exact target and touched file pass; axiom audit is standard only
- [ ] 3 → 4  publication-ready: standalone exposition

## Approach

Represent the continuation in the complex Sommerfeld coordinate `z` by

`Gamma(z+ell+1) / Gamma(-z+ell+1)`.

Euler reflection converts the negative-slope denominator into a differentially algebraic sine gauge and a positive-slope Gamma factor on the same integer translation orbit.  The resulting oriented orbit charge is `2`, so the existing meromorphic superselection theorem gives hypertranscendence.  Separately use Gamma conjugation and the one-step functional equation to prove physical unitarity, parameter reflection, and the adjacent-partial-wave recurrence.

`FermiCoulombGammaCore.lean` now supplies a complementary magnitude channel from the relativistic
beta-decay Fermi function.  At weight `ell+1`, multiplying that magnitude core by the Coulomb phase
reconstructs `exp(pi*xi) Gamma(ell+1+i*xi)^2`.  Thus the phase and magnitude observations jointly
recover an oriented Gamma source up to a square.

## Non-circularity and scope

The physical identification is the source formula.  Lean proves the Gamma value relations and the differential classification of the stated complex continuation.  It does not infer a statement about the complete Coulomb amplitude after an infinite partial-wave sum, screened potentials, nuclear corrections, or experimental reconstruction.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.CoulombGammaPhaseClock`

- `coulombPhaseMero_eq_orientedProduct`
- `hypertranscendentalOver_coulombPhaseMero`
- `norm_coulombPhaseValue`
- `coulombPhaseValue_succ`
- `coulombPhaseValue_neg`

Verification:

- `lake build +GaloisForLFunctions.HTGeometry.CoulombGammaPhaseClock`
- `lake env lean GaloisForLFunctions/HTGeometry/CoulombGammaPhaseClock.lean`
- `#print axioms` for all five theorems: only `propext`, `Classical.choice`, `Quot.sound`

## Log

- 2026-07-17 — exact formula located in the primary math-physics source; scratch proof of all four relations passes against the current toolchain.
- 2026-07-17 — promoted after exact-module build, direct-file verification, and standard-only axiom audit.
- 2026-07-17 — connected to the beta-decay Fermi magnitude core by an exact
  magnitude--phase reconstruction theorem.
