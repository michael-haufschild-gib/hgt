# Xi Euler-ray two-node response barrier — formalized

- **ID:** `xi-euler-ray-two-node-response-barrier-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `xi-euler-ray-two-node-response-barrier.md`
- **Umbrella import:** `GaloisForLFunctions.RHTower`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/RHTower/XiSquaredEulerRayTwoPointPositivity.lean` | the dependency-closed finite algebraic core |
| `formal/GaloisForLFunctions/RHTower/XiSquaredEulerRayFullResponse.lean` | the analytic promotion to the complete Xi divisor |
| `formal/GaloisForLFunctions/RHTower/XiSquaredEulerRayCubicAmplification.lean` | mixed exterior-cubic masking and finite-amplitude amplification |
| `formal/GaloisForLFunctions/RHTower/XiTransversePrimeSourceProjectiveTangent.lean` | the Brownian–Laplace factorization and oriented first-contact grade |

`XiSquaredEulerRayFullResponse`, `XiSquaredEulerRayCubicAmplification` and
`XiTransversePrimeSourceProjectiveTangent` are imported directly by `GaloisForLFunctions.RHTower`;
`XiSquaredEulerRayTwoPointPositivity` is reachable through the first of them.

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`:

- `RHTower.xiSquaredEulerOrbitCharge_pos_of_ne_half`, `RHTower.xiSquaredEulerFiniteKernel_diag_pos`,
  `RHTower.xiSquaredEulerFiniteKernel_twoPoint_det_pos` — strict one- and two-node positivity for
  every nonempty finite Xi orbit packet;
- `RHTower.xiSquaredEulerOrbitKernel_threePointDet_neg` — the exact three-node factorization and
  strict negativity for a transverse orbit, i.e. detector order exactly three;
- `RHTower.xiSquaredEulerFullResponse_eq_logDeriv`, `RHTower.xiSquaredEulerFullQ_eq_logDeriv_re` —
  the exact analytic normalization `ξ′(½+x)/(x·ξ(½+x)) = ∑_q Re (x²+a_q²)⁻¹` for `x > 0`;
- `RHTower.xiSquaredEulerFullKernel_diag_pos`, `RHTower.xiSquaredEulerFullKernel_twoPoint_det_pos` —
  strict radial monotonicity and strict two-node positivity for the actual infinite Xi response;
- `RHTower.symmetricThreePointDet_add_smul`,
  `RHTower.symmetricThreePointDet_add_smul_neg_of_maskingBudget_lt`,
  `RHTower.exists_symmetricThreePointDet_add_smul_neg`,
  `RHTower.exists_xiSquaredEulerReweightedFullKernel_threePointDet_neg` — the mixed-discriminant
  expansion and the finite-amplitude masking theorem;
- `RHTower.xiTransversePrimePowerBrownianLaplaceSample_eq`,
  `RHTower.xiTransverseShiftArithmetic_primePow_normalized_eq_brownianLaplace`,
  `RHTower.tendsto_xiTransversePrimeApertureRatio_valuationLayer_firstDefect` — the all-valuation
  Brownian–Laplace factorization, projective collapse, and oriented first-contact grade.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/XiSquaredEulerRayFullResponse.lean
lake env lean GaloisForLFunctions/RHTower/XiSquaredEulerRayCubicAmplification.lean
lake env lean GaloisForLFunctions/RHTower/XiTransversePrimeSourceProjectiveTangent.lean
```

Six-capstone axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

## Boundary

The formalized surface stops exactly where the paper card says it does: three-node negativity for
the *sum* is not inferred, because the mixed exterior-cubic masking terms remain the open core.
The card's one remaining gate is an external parent-theory and literature novelty audit, which is
not a formalization obligation.  This is not a proof of RH.
