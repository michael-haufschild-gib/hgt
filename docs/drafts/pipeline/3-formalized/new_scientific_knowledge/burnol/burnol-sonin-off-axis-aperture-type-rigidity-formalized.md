# Burnol--Sonin off-axis aperture-type rigidity — formalized

- **ID:** `burnol-sonin-off-axis-aperture-type-rigidity-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-sonin-off-axis-aperture-type-rigidity.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationAperture.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvenCosineAperture.lean
formal/GaloisForLFunctions/RHTower/ArchimedeanMellinFourier.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninRieszVector.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninContinuousEvaluation.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninApertureRieszBound.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninCrossApertureRiesz.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninApertureMonotone.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEigenWitness.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonMellinNonvanishing.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSourceVectorSpace.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationNonvanishing.lean
formal/GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean
```

## Formal theorem chain

```text
1  soninMellinEvaluation, SoninHeadConstant            the completed evaluator and head class
2  norm_soninMellinEvaluation_le_aperture_even         the ambient bound              (3)--(7)
3  soninCosineUnitary, soninExtendedSpace              F_+ and L_a; cosine invariance
4  archimedean functional equation of the completed weight                              (8)
5  norm_soninMellinEvaluation_cosine_le_aperture       the reflected bound           (3),(4)
6  burnolExtendedSoninEvaluationVector                 the Riesz vector k_(w,a)
7  norm_burnolExtendedSoninEvaluationVector_geometric_lower   the geometric lower bound  (11)
8  norm_burnolExtendedSoninEvaluationVector_geometric_upper   the two-sided law          (12)
9  tendsto_log_norm_burnolExtendedSoninEvaluationVector       the exponent limit         (13)
10 soninExtendedSpace_mono, burnolExtendedSoninEvaluationVector_ne_zero_of_le
     aperture monotonicity of nonvanishing
11 exists_cosine_eigen_witness, mem_soninExtendedSpace_symmetrized   the eigen reduction
12 coPoissonIndicatorSoninCosine, soninMellinEvaluation_coPoissonIndicatorSoninCosine
     the explicit inhabitant and its closed-form Mellin transform
13 inner_eq_zero_on_burnolCoPoissonVectorSpace_iff     annihilation exactly at the zeros
14 not_finiteDimensional_burnolCoPoissonVectorSpace    the source span is infinite dimensional
15 burnolExtendedSoninEvaluationVector_ne_zero         the witness at a hypothetical zero  (10)
16 tendsto_log_norm_burnolExtendedSoninEvaluationVector_unconditional
     the aperture-type law (13) with no nonvanishing premise
17 burnolCoPoissonQuotientEvaluationVector_ne_zero_of_annihilator
     the co-Poisson quotient vectors y_(rho,N) are nonzero
```

Statements `(15)`--`(18)` of the paper card are the hostile literature audit and carry no Lean
obligation.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/BurnolSoninProjectedEvaluationTransport.lean  -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolSoninBilateralKernel.lean               -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean                -- clean
lake build GaloisForLFunctions.RHTower.BurnolBilateralApertureRH                        -- success
```

Every declaration named above reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.
All modules are wired into `GaloisForLFunctions.RHTower`.
