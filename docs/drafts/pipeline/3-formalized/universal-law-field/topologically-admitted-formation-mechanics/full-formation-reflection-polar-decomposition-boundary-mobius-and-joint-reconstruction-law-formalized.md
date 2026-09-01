# Full formation reflection polar mechanics — Lean formalization

- **Source:** `docs/drafts/pipeline/3-formalized/universal-law-field/topologically-admitted-formation-mechanics/full-formation-reflection-polar-decomposition-boundary-mobius-and-joint-reconstruction-law.md`
- **ID:** ULF-TAFM-22
- **Status:** `[FORMALIZED] [UNCONDITIONAL] [AXIOM-CLEAN] [NOT RH]`
- **Modules:**
  - `GaloisForLFunctions.HTGeometry.FormationReflectionPolarMechanics`
  - `GaloisForLFunctions.HTGeometry.ShiftedEulerFormationReflectionPolarMechanics`

## Coordinate-free formation law

`FormationReflectionPolarMechanics.lean` defines a finite free-commutative formation profile as a
`Finsupp` multiplicity vector and formalizes:

- `formationMultiplicityDefect_eq_sum`
- `formationMultiplicityDefect_nonneg`
- `formationMultiplicityDefect_eq_zero_iff`
- `formationReflectionPacketCoefficient_neg`
- `formationReflectionMultiplier_neg_mul`
- `norm_formationReflectionMultiplier_ofReal`
- `formationReflectionMultiplier_ofReal`
- `formationReflectionMultiplier_div_norm_ofReal`
- `formationMultiplicityDefect_reconstruct`
- `formationReflection_joint_reconstruction`
- `norm_formationReflectionMultiplier_eq_one_iff`
- `formationMobius_eq_reflection_boundaryPhase`
- `formationCenteredReflectionRatio_conservation`
- `formationReflectionPolarMechanics_completion_certificate`

The last theorem is the universal boundary-Möbius law: exterior projection followed by normalized
reflection equals the Möbius law of every positively weighted free-commutative formation monoid.

## Prime-logarithm specialization

`ShiftedEulerFormationReflectionPolarMechanics.lean` proves prime factorization with logarithmic
weights realizes the abstract formation object and formalizes:

- exact total/support/multiplicity-weight realization;
- `shiftedEulerValuationDefect_eq_log_div`, the exact `log(n / rad(n))` law;
- squarefree-radical positivity, divisibility, squarefreeness, and equality classification;
- `shiftedEulerCoeff_neg`, the full shifted-Euler reflection law;
- `shiftedEulerReflectionMultiplier_neg_mul`, information-neutral two-step lift;
- exact phase/modulus polar decomposition and joint reconstruction;
- `norm_shiftedEulerReflectionMultiplier_eq_one_iff`, squarefree unitary-locus selection;
- `moebius_cast_eq_shiftedEulerReflection_boundaryPhase`, source-native Möbius reconstruction;
- `squarefreeProjection_shiftedEulerCoeff_neg`, predicted fourth-organ identity.
- `shiftedEulerFormationReflectionPolarMechanics_completion_certificate`, the closed arithmetic
  theorem-family certificate.

## Verification

Both source files pass direct foreground elaboration with `lake env lean`. Targeted leaf build
`GaloisForLFunctions.HTGeometry.ShiftedEulerFormationReflectionPolarMechanics` passes
`8659/8659`; no umbrella or full-project build was run. Nine newly added theorem declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`. Both modules contain no `sorry`,
`admit`, new `axiom`, `opaque`, or `unsafe` declaration. Modules are wired into
`HTGeometry.UniversalLawField`.
