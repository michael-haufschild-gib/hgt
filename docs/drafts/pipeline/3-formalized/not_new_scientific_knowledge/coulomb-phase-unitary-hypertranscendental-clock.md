# The Coulomb partial-wave phase is a unitary hypertranscendental clock

- **ID:** `coulomb-phase-unitary-hypertranscendental-clock`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** J. C. A. Barata, L. F. Canto, M. S. Hussein, *The Coulomb Phase Shift Revisited*, arXiv:0912.3189, equation (1)
- **Statement:** The complexified Coulomb partial-wave phase is hypertranscendental for every angular momentum, although its physical real-parameter restriction has unit modulus; globally, reflected-frequency intensity is exactly one while both the orientation observation and the Wigner--Smith logarithmic delay remain HT and cannot be recovered from intensity by a finite differential circuit.

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

The general reflected-frequency observation theorem gives a second exact decomposition.  Since
`S_ell(-z)=S_ell(z)^(-1)`, the global meromorphic intensity is exactly one and the orientation
quotient is `S_ell(z)^2`.  The latter is HT.  Therefore rational clocks and the unit intensity,
closed under finite field operations and differentiation, cannot reconstruct the Coulomb phase.

The Wigner--Smith observation strengthens this no-go positively.  The logarithmic delay
`S_ell'/S_ell` is exactly the difference of the two oppositely oriented Gamma logarithmic
derivatives and is HT.  Thus differentiation exposes a standard scattering-time observable that
retains the source even though the complete reflected-frequency intensity is globally constant.
The same Coulomb-like factor occurs in far-zone scalar, electromagnetic, and gravitational-wave
black-hole scattering; this imports no claim about Born extraction of quasinormal modes.

## Non-circularity and scope

The physical identification is the source formula.  Lean proves the Gamma value relations and the differential classification of the stated complex continuation.  It does not infer a statement about the complete Coulomb amplitude after an infinite partial-wave sum, screened potentials, nuclear corrections, or experimental reconstruction.

## Lean certificate

Modules:

- `GaloisForLFunctions.HTGeometry.CoulombGammaPhaseClock`
- `GaloisForLFunctions.HTGeometry.CoulombPhaseIntensityObservability`

- `coulombPhaseMero_eq_orientedProduct`
- `hypertranscendentalOver_coulombPhaseMero`
- `norm_coulombPhaseValue`
- `coulombPhaseValue_succ`
- `coulombPhaseValue_neg`
- `coulombPhaseIntensityObservationMero_eq_one`
- `coulombPhaseOrientationObservationMero_eq_square`
- `hypertranscendentalOver_coulombPhaseOrientationObservationMero`
- `no_scalarAwareFiniteDifferentialCircuit_coulombPhase_from_intensity`
- `coulombWignerSmithLogClockMero_eq_orientedLogDerivatives`
- `hypertranscendentalOver_coulombWignerSmithLogClockMero`
- `no_scalarAwareFiniteDifferentialCircuit_coulombWignerSmith_from_intensity`

Verification:

- `lake build +GaloisForLFunctions.HTGeometry.CoulombGammaPhaseClock`
- `lake env lean GaloisForLFunctions/HTGeometry/CoulombGammaPhaseClock.lean`
- `#print axioms` for all five theorems: only `propext`, `Classical.choice`, `Quot.sound`

## Log

- 2026-07-17 — exact formula located in the primary math-physics source; scratch proof of all four relations passes against the current toolchain.
- 2026-07-17 — promoted after exact-module build, direct-file verification, and standard-only axiom audit.
- 2026-07-17 — connected to the beta-decay Fermi magnitude core by an exact
  magnitude--phase reconstruction theorem.
- 2026-07-17 — applied the general reflected-frequency selector: unit global intensity, HT square
  phase, and finite-differential non-recovery verified with a serialized exact target, direct check,
  and standard-only axiom audit.
- 2026-07-17 — added the Wigner--Smith positive observable: exact oriented log-derivative relation,
  unconditional HT delay, and finite-differential non-recovery from unit intensity.  The touched
  file passes direct Lean verification; the four new surfaces have only the standard three axioms.
