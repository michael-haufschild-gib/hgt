# Horizontal--vertical packet renewal budget and cofinal properness law — Lean certificate

- **ID:** ULF-CRG-4-LEAN
- **Stage:** 3 — formalized in Lean 4
- **Paper parent:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/cofinal-renewal-geometry/horizontal-vertical-packet-renewal-budget-and-cofinal-properness-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED FULL] [UNCONDITIONAL] [ARBITRARY PACKET RENEWAL]`
  `[NO SORRY] [NO ADDED AXIOMS] [NO COMPUTATION] [NOT RH]`

## Certified theorem surface

The module proves the complete labeled surface of ULF-CRG-4:

1. `klDiv_map_le_arbitrary` proves KL data processing for an arbitrary measurable map on arbitrary
   measurable spaces, with no standard-Borel restriction;
2. `integral_le_klDiv_add_log_integral_exp` and its nonnegative and integrability corollaries prove
   the entropy--exponential-moment budget used by the packet gauge;
3. `packetMarginal_klDiv_le` proves `(HVP.4)`, so observer-marginal action cannot exceed total
   packet action;
4. `packetEntropy_controls_horizontalGauge` and `packetGauge_integral_eq_marginal` prove the two
   equivalent forms `(HVP.5)` and `(HVP.6)` for arbitrary correlated packet renewals;
5. `arbitraryPacket_disjointAperture_entropyMoment` turns finite packet action and a stretched-
   exponential aperture estimate into the global weighted renewal moment;
6. `arbitraryPacket_stretchedAperture_workDegree_gt` proves `(HVP.8)`: persistent current under
   polynomial work forces `d > gamma + 1`; the exponential specialization excludes degrees at
   most two;
7. `arbitraryPacket_klDiv_eq_horizontal_add_vertical` uses the canonical standard-Borel
   conditional kernel `Q.condKernel` and proves the exact chain rule `(HVP.10)` for an arbitrary
   joint packet law;
8. `packetVerticalAction_eq_lintegral` and
   `arbitraryPacket_klDiv_eq_horizontal_add_lintegral` identify the vertical action with the
   fibrewise conditional-KL integral `(HVP.11)`;
9. `arbitraryPacket_horizontal_vertical_budget` proves the sharpened common budget `(HVP.12)`;
10. `packetVerticalAction_eq_zero_iff` proves `(HVP.13)`: zero vertical action is equivalent to
    equality of renewed and reference conditional kernels almost everywhere;
11. `commonRecovery_klDiv` and `arbitraryPacket_minimumAction_eq_iff` prove `(HVP.14)` and its
    uniqueness clause: common recovery is exactly the least-action lift at fixed observer
    marginal.

The same module also proves the disjoint-aperture partition identities, exact aperture-gauge
integrals, summability/properness tail bounds, persistent-current degree wall, and total-current
bound used by the packet corollaries. Common recovery preserves horizontal action exactly;
arbitrary history changes contribute only the nonnegative vertical term.

## Verification

Verified in the repository toolchain with:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCofinalRenewalGeometry.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
```

Targeted build completed successfully. Scoped source scan found no `sorry`, `admit`, project
`axiom`, `opaque`, `unsafe`, `decide`, `native_decide`, `norm_num`, or `omega`. `#print axioms`
on the packet chain-rule, budget, work-wall, zero-vertical, and minimum-action capstones reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This theorem is not RH and does not construct an arithmetic persistent current. It proves that any
finite-KL Markov recovery completion cannot use latent history to replenish an evacuated observer
aperture. Any proposed escape must violate a stated hypothesis: finite action, absolute continuity,
Markov/source-dependent recovery, observer-readable gauge, or probability-law normalization.
