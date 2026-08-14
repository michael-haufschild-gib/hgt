# Observer-channel recurrence–production dichotomy law — Lean formalization

- **ID:** `observer-channel-recurrence-production-dichotomy-law-formalized`
- **Stage:** 3 -- formalized in Lean 4
- **Status:** `[LEAN-PROVED] [UNIVERSAL] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-14
- **Paper proof:**
  `../2-fully-proven/observer-channel-recurrence-production-dichotomy-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/StaticShortcutRecurrenceChannelProductionLaw.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`

## Formalized result

The module proves unconditionally for arbitrary finite sample/channel types and every real Hilbert
space:

1. channel loads partition total history weight exactly;
2. selector recurrence energy is nonnegative;
3. total history mass squared is at most occupied-channel count times load energy;
4. `eta^2 W^2 <= B M R`, the recurrence-or-channel-production law;
5. its bounded-capacity form and strict capacity-violation contrapositive;
6. nonnegative metric separation makes channel labels injective in preparation-memory space;
7. the separated strict contrapositive simultaneously certifies distinct memories and `M>K`;
8. fresh identity channels saturate the occupancy inequality;
9. the two-memory static-flow capstone writes `R` as the exact same-target stationary recurrence
   kernel after completed-sector removal.

## Main declarations

```text
selectorOccupiedChannels
ObserverChannelsSeparated
observerChannelsSeparated_injective
sum_selectorChannelWeight_eq_sum
selectorRecurrenceEnergy_nonneg
selectorTotalWeight_sq_le_occupied_mul_load
selectorRecurrence_or_channelProduction
selectorMass_sq_le_capacity_mul_recurrence
selectorOccupiedChannels_gt_of_recurrenceBudget_lt
separatedSelectorOccupiedChannels_gt_of_recurrenceBudget_lt
selectorIdentity_unitWeight_occupancy_saturation
adaptive_shortcuts_force_recurrence_or_channelProduction
```

## Verification

Scratch and repository checks:

```text
lake env lean /tmp/hgt_channel_production.lean
lake env lean GaloisForLFunctions/HTGeometry/StaticShortcutRecurrenceChannelProductionLaw.lean
```

Module-only build:

```text
lake build GaloisForLFunctions.HTGeometry.StaticShortcutRecurrenceChannelProductionLaw
```

All exited `0`; the module-only build completed successfully. `#print axioms` for occupancy,
dichotomy, capacity, strict contrapositive, sharpness and static-flow capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`. No forbidden proof declaration occurs. Module is
wired adjacent to its selector parent; no umbrella/full build was run.

## Scientific status

This is a stronger deterministic spine than the failed scalar source route. It proves recurrence
and observer-channel production are complementary resources of every selected history. It does not
supply the quenched strict budget inequality for ordinary local Hamiltonians, identify resolution
channel count with a gate-set circuit lower bound, or prove Brown growth/plateau/recurrence rates.
Its elementary ingredients are classical and external application priority is unverified. The
master paper remains below Nature acceptance threshold.
