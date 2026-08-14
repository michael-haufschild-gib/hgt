# Return-excised cross-recurrence capacity law -- Lean formalization

- **ID:** return-excised-cross-recurrence-capacity-law-formalized
- **Stage:** 3 -- formalized in Lean 4
- **Status:** [LEAN-PROVED] [WIRED] [LEAF-BUILT] [AXIOMS-AUDITED]
- **Date:** 2026-08-14
- **Paper proof:** ../3-formalized/return-excised-cross-recurrence-capacity-law.md
- **Lean module:** formal/GaloisForLFunctions/HTGeometry/StaticShortcutCrossRecurrenceCapacityLaw.lean
- **Umbrella:** formal/GaloisForLFunctions/HTGeometry.lean

## Formalized results

Module defines:

- selectorDiagonalRecurrenceEnergy: unavoidable self-memory;
- selectorCrossRecurrenceEnergy: ordered distinct-time pairs reusing one selected channel;
- selectorCrossLoad: corresponding distinct-pair channel load.

It proves:

- selectorRecurrenceEnergy_eq_diagonal_add_cross;
- selectorLoadEnergy_eq_diagonal_add_cross;
- selectorCapacity_forces_crossRecurrence;
- selectorCrossRecurrenceEnergy_le_coherence_mul_crossLoad;
- selectorCoherenceGap_mul_load_le_diagonal;
- selectorMass_sq_le_capacity_mul_diagonal_of_coherence;
- selectorOccupiedChannels_gt_of_coherenceBudget_lt;
- selectorCard_sq_le_capacity_mul_card_of_coherence.

Capstone inequality is

\[
 \eta^2W^2-BK D_{\rm self}\le BK R_{\rm cross}.
\]

Coherence form is

\[
 (\eta^2-B\mu)W^2\le BK(D-\mu)\sum_jw_j^2.
\]

Both preserve complete selected history and same-channel pair multiplicities.

## Verification

Commands ran from formal/ with one foreground process at a time:

- lake env lean /tmp/hgt_selector_cross_recurrence.lean
- lake env lean GaloisForLFunctions/HTGeometry/StaticShortcutCrossRecurrenceCapacityLaw.lean
- lake build GaloisForLFunctions.HTGeometry.StaticShortcutCrossRecurrenceCapacityLaw
- lake env lean /tmp/hgt_selector_cross_axioms.lean

Results:

- scratch theorem development passed;
- direct production-module check passed;
- leaf-only build passed: Built GaloisForLFunctions.HTGeometry.StaticShortcutCrossRecurrenceCapacityLaw;
- no full or umbrella build ran;
- module is wired directly after StaticShortcutRecurrenceChannelProductionLaw;
- no sorry, admit, project axiom, opaque, or unsafe declaration occurs.

Axiom audit for all headline declarations reports only:

- propext;
- Classical.choice;
- Quot.sound.

## Exact boundary

Formalization removes diagonal false positive from selector-resolved source problem. It does not
prove a local-Hamiltonian bound on cross recurrence. Uniform pairwise coherence is a sufficient
hypothesis inside an unconditional implication; no manuscript may assert ordinary local
Hamiltonians satisfy it until that separate theorem is proved in Lean.

It also does not prove Brown-linear growth. Against exponentially growing circuit-channel
capacity, finite deterministic history counting alone is too weak. Live frontier remains a
quenched, growing-replica or incidence-action estimate for one ordinary static local Hamiltonian,
uniform over complete approximate shallow-circuit selector class.

