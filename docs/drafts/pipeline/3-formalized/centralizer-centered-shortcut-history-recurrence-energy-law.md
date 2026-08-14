# Centralizer-centered shortcut-history recurrence-energy law — Lean formalization

- **ID:** `centralizer-centered-shortcut-history-recurrence-energy-law-formalized`
- **Stage:** 3 -- formalized in Lean 4
- **Status:** `[LEAN-PROVED] [BRIDGE] [APPLICATION NOVELTY UNVERIFIED]`
- **Date:** 2026-08-14
- **Paper proof:**
  `../2-fully-proven/centralizer-centered-shortcut-history-recurrence-energy-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/StaticShortcutRecurrenceEnergyLaw.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`

## Formalized frontier

The module proves unconditionally:

1. weighted history Gram energy is exactly a squared Hilbert norm;
2. total fixed-probe alignment is bounded by probe norm squared times that energy;
3. this universal Hilbert inequality is sharp for every history;
4. a unitary-flow Gram matrix is exactly one stationary recurrence kernel on time differences;
5. changing the shortcut target adaptively at every sampled time still produces one fixed
   preparation memory after uniform target averaging;
6. uniform target frame energy is exactly the normalized sum of every target Gram entry;
7. subtracting the self-adjoint idempotent universal sector subtracts its squared norm exactly;
8. adaptive shortcut-history mass is bounded by centralizer-conditioned target frame energy times
   centralizer-centered source recurrence energy.

Items 3, 6, and 8 machine-check the exact research boundary.  Pure Hilbert geometry cannot remove
the Cauchy square.  The only scale-sensitive target invariant left by the proof is average replica
frame energy, not minimum endpoint separation.  The source invariant is weighted recurrence
energy, not minimum spectral gap.

## Main declarations

```text
weightedRecurrenceEnergy_eq_norm_sq
weightedAlignment_sq_le_recurrenceEnergy
weightedAlignment_sq_eq_recurrenceEnergy_of_historyProbe
inner_unitaryFlow_eq_recurrenceKernel
weightedRecurrenceEnergy_flow_eq_kernel
threshold_sq_le_weightedRecurrenceEnergy
finitePreparationFrameEnergy
finitePreparationFrameEnergy_eq_pairAverage
preparationMemory_norm_sq_eq_frameEnergy_sub_universal
adaptive_shortcuts_force_recurrence_energy
```

## Verification

Exact module contents were copied to `/tmp/hgt_static_shortcut_full.lean` and checked in the
foreground with one process:

```text
lake env lean /tmp/hgt_static_shortcut_full.lean
```

Result: exit code `0`, no errors.  `#print axioms` for the seven substantive identities and the
adaptive product law reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration occurs in the module.  No
project-wide build was run.  Module is wired into the `HTGeometry` umbrella.

## Honest boundary

This formalization does not prove Brown--Susskind first onset.  It proves the exact factorization
that a successful proof must close.  Remaining growing-replica tasks are:

```text
return/carrier-excised occupied heap-image frame energy = O(1 / intrinsic capacity),
quenched centralizer-centered recurrence energy is small on the required static-H time window.
```

Both must hold at scales strong enough for complete circuit union.  Literature priority for their
composition remains unverified, so this bridge is not yet a paper headline.
