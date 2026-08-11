# Collective-repair spectral threshold and open-history law — Lean record

- **ID:** ULF-ALM-2
- **Stage:** 3-formalized
- **Status:** [LEAN-CERTIFIED] [ROUTE-INDEPENDENT MECHANISM] [NOT RH]
- **Paper card:**
  `2-fully-proven/universal-law-field/autopoietic-law-mechanics/collective-repair-spectral-threshold-and-open-history-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveCollectiveRepairThreshold`

## Certified mechanism

Lean certifies one closed law cell in which:

1. two conservative repairs leave semantic reach surjective;
2. neither repair alone supports a nonzero feasible circulation;
3. below threshold every feasible zero-boundary history vanishes and a fixed strict progress
   separator exists;
4. at threshold a nonzero repair-only ray appears;
5. above threshold a canonical full-support positive carrier appears and no strict progress
   separator can exist;
6. the symmetric inverse response has exact amplitude `1/epsilon`;
7. visible interaction remains period two in every chamber;
8. positive execution histories have zero semantic boundary and unbounded size, so their cost
   cannot descend to an endpoint potential.

This is a mechanism theorem, not a claim that recurrence causes viability, that the cell is an
autocatalytic network, or that any source selects the threshold.

## Significant declarations

- `collectiveRepairBoundary_surjective`
- `collectiveRepairBoundary_eq_zero_iff`
- `collectiveRepair_left_alone_nonviable`
- `collectiveRepair_right_alone_nonviable`
- `collectiveRepair_subcritical_no_feasible_cycle`
- `collectiveRepair_subcritical_strict_progress`
- `collectiveRepair_critical_feasible_kernel_ray`
- `collectiveRepairCarrier_boundary_zero`
- `collectiveRepairCarrier_full_support`
- `collectiveRepair_no_strict_progress`
- `collectiveRepairInteraction_symmetric`
- `collectiveRepair_symmetric_amplification`
- `collectiveRepair_symmetric_amplification_unique`
- `collectiveRepairSwap_period_two`
- `collectiveRepairHistory_unbounded`
- `collectiveRepairUnitCost_not_endpoint_integrable`
- `collectiveRepairThresholdMechanism_unconditional`

## Verification

Direct foreground elaboration and leaf build pass. The module is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`. Axiom prints on significant declarations and
the unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`. No
computational certificate or project-specific hypothesis occurs. Final foreground umbrella build
passes with 11,587 jobs. Full formal lint reports no target error; unrelated unwired modules keep
the repository-wide lint exit nonzero.
