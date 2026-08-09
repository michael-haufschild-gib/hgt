# Physical prime-log aperture fusion and the off-diagonal RH kernel — formalized

- **ID:** `xi-physical-prime-log-aperture-fusion-cross-kernel-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `xi-physical-prime-log-aperture-fusion-cross-kernel.md`
- **Umbrella imports:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeLogApertureFusion.lean` | the source objects and `(PFK1)`–`(PFK12k)` |
| `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeLogApertureHilbertMetric.lean` | the `L²` carrier, Hilbert distance, Gram identity, fusion-energy positivity |
| `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeFusionSourceBridge.lean` | identification with the existing `HGS29` carrier |
| `formal/GaloisForLFunctions/RHTower/PrimePowerCompletionCarrierNorm.lean` | prime-power completion stability `(PFK14)`–`(PFK17)` |
| `formal/GaloisForLFunctions/HTGeometry/LogSquaredTailIntegral.lean` | the analytic tail bound `(PFK11)` |

## Audited declaration list

Every declaration named by the paper card resolves, and `#print axioms` on each reports exactly
`propext`, `Classical.choice`, `Quot.sound`:

- `RHTower.xiPhysicalPrimeLogApertureCrossDefect_eq_pairExcess` — `(PFK12a)`;
- `RHTower.xiPhysicalPrimeLogBulkCrossDefect_width_secondDifference` — `(PFK12b)`;
- `RHTower.xiPhysicalPrimeLogBulkPairDistance_eq_iff` — `(PFK12e)`;
- `RHTower.exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_forward_recovers_cumulativeDiscrepancy`
  — `(PFK12g)`;
- `RHTower.exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_primePair`
  — `(PFK12h)`;
- `RHTower.not_exists_local_quadratic_bound_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature`
  — the linear-cusp no-go `(PFK12i)`;
- `RHTower.exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_shiftFilteredPair`
  — `(PFK12j)`;
- `RHTower.exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticSplineGerms`,
  `…_quadraticChamber_of_fiberMass_eq_zero`, `…_quadraticSplineGerms_at_primePair` — `(PFK12k)`;
- `RHTower.xiPhysicalPrimeLogAggregateApertureCarrier_eq_neg_fusedResponse_add_remainder` — the
  `HGS29` bridge;
- `RHTower.norm_primePowerCompletionCarrier_le_tail` — `(PFK14)`–`(PFK17)`;
- `GaloisForLFunctions.HTGeometry.tsum_logSq_div_sq_le` — `(PFK11)`.

All five modules are reachable from their theorem-area umbrellas
(`GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`).

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/XiPhysicalPrimeLogApertureFusion.lean
lake env lean GaloisForLFunctions/RHTower/XiPhysicalPrimeLogApertureHilbertMetric.lean
lake env lean GaloisForLFunctions/RHTower/XiPhysicalPrimeFusionSourceBridge.lean
```

Thirteen-capstone axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.  No hypothesis of
the card is carried as an unproved external input.

## Boundary

The card's remaining open gate is an external source-specific novelty audit, which is not a
formalization obligation.  The formalized content is the exact true-aperture Green germ, its
linear-cusp no-go, the coefficient-exact hypertranscendental Xi-source attachment, and the finite
quadratic-spline boundary — not a proof of RH.
