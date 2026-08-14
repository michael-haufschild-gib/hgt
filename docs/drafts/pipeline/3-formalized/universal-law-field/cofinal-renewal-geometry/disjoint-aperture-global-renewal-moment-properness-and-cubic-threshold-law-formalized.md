# Disjoint-aperture global renewal, entropy-moment properness, and cubic threshold law — Lean certificate

- **ID:** ULF-CRG-2-LEAN
- **Stage:** 3 — formalized in Lean 4
- **Paper parent:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/cofinal-renewal-geometry/disjoint-aperture-global-renewal-moment-properness-and-cubic-threshold-law.md`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalSharpness`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalStretchedSharpness`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveGlobalRenewalSymmetry`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveSourceHorizontalGlobalRenewal`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED FULL] [UNCONDITIONAL] [SHARP CLASSIFICATION]`
  `[NO SORRY] [NO ADDED AXIOMS] [NO COMPUTATION] [NOT RH]`

## Certified theorem surface

The modules prove every labeled result and corollary of ULF-CRG-2:

1. `stretchedAperture_partition_entropyMoment` proves the finite formation partition function,
   entropy--moment inequality, exact aperture moment identity, and quantitative tail properness
   in `(GRG.3)`--`(GRG.6)`;
2. the gauge integrability and work-duality declarations in
   `ConstitutiveCofinalRenewalGeometry` prove `(GRG.7)`--`(GRG.9)` for arbitrary nonnegative
   gauges with finite exponential moment;
3. `exponentialAperture_persistentCurrent_workDegree_gt_two` proves the global quadratic work
   wall `(GRG.10)`--`(GRG.11)`;
4. `exponentialAperture_totalLinearCurrent_bound` proves the summable linear-current bound
   `(GRG.12)`;
5. `geometricPolynomialRenewal_cubicSharp` constructs one normalized global polynomial renewal
   over an exact geometric baseline, proves finite KL action, constant current, and the sharp
   `d > 2` classification `(GRG.13)`--`(GRG.15)`;
6. `stretchedAperture_persistentCurrent_workDegree_gt` proves the necessary phase boundary
   `d > gamma + 1`, while `stretchedExponentialPolynomialRenewal_classSharp` constructs the exact
   normalized stretched-exponential baseline and polynomial renewal proving sufficiency and
   finite KL in `(GRG.16)`--`(GRG.19)`;
7. `globalRenewal_involution_action_height_invariant` proves both functional-equation identities
   `(GRG.20)`--`(GRG.21)` for arbitrary measurable involutions preserving baseline and height;
8. `formationLiftKernel_klDiv_isometry` supplies common-recovery equality `(GRG.22)`;
9. `klDiv_map_le_arbitrary`, `arbitraryPacket_disjointAperture_entropyMoment`, and
   `arbitraryPacket_stretchedAperture_workDegree_gt` prove that arbitrary correlated packet
   interventions cannot bypass the same moment and work wall;
10. `sourceHorizontalForward_entropyMoment`, `sourceHorizontalReverse_entropyMoment`,
    `sourceHorizontalForward_adaptiveCurrent_summable`, and
    `sourceHorizontalReverse_adaptiveCurrent_summable` close both literal abelian
    source-horizontal orientations with exact exponential rates and summable adaptive current.

The sharpness witnesses are probability laws, not unnormalized series. Their KL divergences are
proved finite in Lean before the exact current identity and work-degree classification are derived.

## Verification

Verified in repository toolchain with targeted commands:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCofinalRenewalSharpness.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCofinalRenewalStretchedSharpness.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveGlobalRenewalSymmetry.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalSharpness
lake build GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalStretchedSharpness
lake build GaloisForLFunctions.HTGeometry.ConstitutiveGlobalRenewalSymmetry
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
```

All targeted builds and umbrella ownership checks passed. Scoped source scan found no `sorry`,
`admit`, project `axiom`, `opaque`, `unsafe`, `decide`, `native_decide`, `norm_num`, or `omega`.
`#print axioms` on both sharpness capstones and the involution capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

This is a sharp classification within the stated global-renewal class. It does not construct an
arithmetic persistent current and is not RH. It proves exactly which stretched-exponential
evacuation and polynomial-work pairs admit a normalized finite-KL constant-current witness.
