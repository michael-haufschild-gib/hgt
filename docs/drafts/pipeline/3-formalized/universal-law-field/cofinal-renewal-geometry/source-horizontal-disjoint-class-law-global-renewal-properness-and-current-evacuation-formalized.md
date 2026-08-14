# Source-horizontal disjoint class-law global renewal properness and current evacuation — Lean certificate

- **ID:** ULF-CRG-3-LEAN
- **Stage:** 3 — formalized in Lean 4
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry` and
  `GaloisForLFunctions.HTGeometry.ConstitutiveSourceHorizontalGlobalRenewal`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED FULL] [UNCONDITIONAL] [LITERAL SOURCE LAW]`
  `[NO SORRY] [NO ADDED AXIOMS] [NO COMPUTATION] [NOT RH]`

## Certified theorem surface

The source-specific module proves every labeled mathematical claim of ULF-CRG-3:

1. `pairwise_disjoint_sourceHorizontalClassAperture` proves `(SHG.3)` for the literal elementary
   and cyclic abelian classes using their exact order and socle invariants;
2. `sourceHorizontalClassAperture_real` proves finite additivity of the two exact singleton
   masses, while `sourceHorizontalForwardClassAperture_real_le` and
   `sourceHorizontalReverseClassAperture_real_le` prove `(SHG.5)`--`(SHG.7)` at the sharp rates
   `(2-a) log p` and `2 log p`;
3. `sourceHorizontalForward_partition` and `sourceHorizontalReverse_partition` prove the exact
   disjoint-aperture partition identities and finiteness ranges `(SHG.8)`--`(SHG.9)`;
4. `sourceHorizontalForward_entropyMoment` and `sourceHorizontalReverse_entropyMoment` quantify
   over every probability renewal with finite KL action and prove both summability and the complete
   entropy budget `(SHG.10)`--`(SHG.12)`;
5. `sourceHorizontalForward_adaptiveCurrent_summable` and
   `sourceHorizontalReverse_adaptiveCurrent_summable` instantiate the existing exact adaptive
   Jeffreys-work bound, proving the quantitative total-current estimates `(SHG.13)`--`(SHG.15)`
   and termwise evacuation `(SHG.16)`.

The arbitrary-packet and common-recovery extensions are supplied by
`ConstitutiveCofinalRenewalGeometry`: observer projection contracts KL, and any conditional-history
change contributes a nonnegative vertical action.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveSourceHorizontalGlobalRenewal.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveSourceHorizontalGlobalRenewal
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
```

All commands pass. Scoped source scan finds no `sorry`, `admit`, project `axiom`, `opaque`,
`unsafe`, `decide`, `native_decide`, `norm_num`, or `omega`. Axiom inspection of disjointness,
mass, partition, entropy-moment, and adaptive-current capstones reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

This result closes the abelian source-law renewal gate. It does not construct an arithmetic
renewal or identify a current from another organ with these apertures. Such a current must pay
infinite KL, become singular, exceed the linear work scale, leave probability laws, or fail the
literal aperture identification.
