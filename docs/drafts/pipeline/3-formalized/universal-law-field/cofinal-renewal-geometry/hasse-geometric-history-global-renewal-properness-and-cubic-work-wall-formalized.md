# Hasse geometric-history global renewal properness and cubic work wall — Lean certificate

- **ID:** ULF-CRG-5-LEAN
- **Stage:** 3 — formalized in Lean 4
- **Paper parent:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/cofinal-renewal-geometry/hasse-geometric-history-global-renewal-properness-and-cubic-work-wall.md`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.ConstitutiveHassePacketFormation`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveHasseGlobalRenewal`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalSharpness`
  - `GaloisForLFunctions.HTGeometry.ConstitutiveGlobalRenewalSymmetry`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED FULL] [UNCONDITIONAL] [LITERAL HASSE KERNEL]`
  `[SHARP CUBIC CLASSIFICATION] [NO SORRY] [NO ADDED AXIOMS] [NO COMPUTATION] [NOT RH]`

## Certified theorem surface

The modules prove the complete ULF-CRG-5 surface:

1. `hassePacketRatio_mem_Ioo`, `hasSum_hassePacketRecovery`, and
   `HasseHistoryProfile.kernel_apply_singleton` prove the literal Hasse geometric density,
   normalization, and Markov-kernel statements `(HGH.1)`--`(HGH.4)`;
2. `hasseHistoryAperture`, `measurableSet_hasseHistoryAperture`, and
   `pairwise_disjoint_hasseHistoryAperture` prove the measurable disjoint history partition
   `(HGH.5)`;
3. `hassePacketRatio_lt_half`, `hassePacketRecovery_succ_le_uniformGeometric`, and the packet
   aperture estimate prove the uniform geometric tail required by `(HGH.6)`;
4. `HasseHistoryProfile.partition_entropyMoment` applies the generic entropy--moment theorem to
   every arbitrary correlated finite-KL renewal of the full formed packet and proves `(HGH.6)` and
   `(HGH.9)`;
5. `HasseHistoryProfile.totalLinearHistoryCurrent_bound` proves `(HGH.10)`;
6. `HasseHistoryProfile.persistentCurrent_workDegree_gt_two` proves the necessary quadratic wall
   `(HGH.11)`--`(HGH.12)`;
7. `hassePacketRecovery_eq_geometricBaselineMass` identifies the literal point-mass Hasse packet
   with the generic normalized geometric baseline;
8. `hasseHistory_cubic_classSharp` constructs the exact normalized polynomial renewal for every
   `d > 2`, proves finite KL action, and proves constant current, thereby closing
   `(HGH.13)`--`(HGH.16)` without a placeholder source law;
9. `globalRenewal_involution_action_height_invariant` proves KL and height-law neutrality for the
   functional-equation involution. Combined with the formed Hasse Markov law, this proves the
   compatibility statement in Section 6 without preserving an old sampled history label.

The necessary and sharp directions share the same literal Hasse species: the lower theorem holds
for arbitrary packet renewals, while the upper theorem gives an explicit finite-KL member of that
class for every integer degree above two.

## Verification

Verified in repository toolchain with targeted commands:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveHasseGlobalRenewal.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveHasseGlobalRenewal
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
```

Targeted build and umbrella ownership check passed. Scoped source scan found no `sorry`, `admit`,
project `axiom`, `opaque`, `unsafe`, `decide`, `native_decide`, `norm_num`, or `omega`.
`#print axioms` on the entropy moment, total-current bound, degree wall, and sharp Hasse capstone
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

History depth is certified Hasse generation depth, not elapsed physical time. The result is a
formation/properness and sharp work-threshold theorem for this recovery species; it is not RH and
does not assert survival for every observer law.
