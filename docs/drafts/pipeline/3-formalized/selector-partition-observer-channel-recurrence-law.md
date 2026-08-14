# Selector-partition observer-channel recurrence law — Lean formalization

- **ID:** `selector-partition-observer-channel-recurrence-law-formalized`
- **Stage:** 3 -- formalized in Lean 4
- **Status:** `[LEAN-PROVED] [BRIDGE] [FALSE-FRONTIER-CORRECTION] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-14
- **Paper proof:**
  `../2-fully-proven/selector-partition-observer-channel-recurrence-law.md`
- **Failed route:**
  `../5-failed/scalar-centralizer-recurrence-energy-as-brown-onset-provider.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/StaticShortcutSelectorPartitionLaw.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`

## Formalized result

For arbitrary finite sample and channel types in every real Hilbert space, the module proves
unconditionally:

1. exact masking, load, memory and recurrence energies for an adaptive selected-channel history;
2. the channel-specific observer--spectral law

   ```text
   sum_c eta_c^2 W_c^2 <= sum_c ||q_c||^2 ||V_c||^2;
   ```

3. its uniform-margin and uniform-target-norm corollary;
4. exact expansion of selector recurrence into same-channel temporal pairs;
5. exact stationary-kernel form for every unitary flow;
6. constant selector recovers full scalar recurrence energy;
7. injective selector removes every off-diagonal pair and leaves exactly
   `||z||^2 sum_j w_j^2`;
8. identity selection with self-target memories saturates the observer--spectral inequality for
   arbitrary vectors and weights—orthogonality and spectral phase separation are unnecessary;
9. the target-specific two-memory capstone: every adaptive collision above its completed static
   baseline forces the channel-resolved stationary recurrence inequality with no uniform target
   average and no inverse-dictionary attenuation.

## Main declarations

```text
selectorMaskedWeight
selectorChannelWeight
selectorChannelMemory
selectorLoadEnergy
selectorRecurrenceEnergy
selectorMargins_sq_load_le_recurrenceEnergy
selectorThreshold_sq_load_le_recurrenceEnergy
selectorRecurrenceEnergy_eq_pairSum
selectorRecurrenceEnergy_flow_eq_kernel
selectorRecurrenceEnergy_const
selectorRecurrenceEnergy_injective
selectorRecurrenceEnergy_flow_injective
selectorIdentity_selfTarget_saturation
adaptive_selected_shortcuts_force_channel_recurrence
```

## New frontier knowledge

The former source-side objective was mathematically impossible. Scalar recurrence energy measures
reuse of one observer channel; it cannot penalize a history that spends each sample on a new
channel. The formal saturation theorem proves this is not looseness in averaging, a poor spectral
invariant, or a missing dephasing estimate. It is an exact representation obstruction.

Correct Brown first-onset target is therefore not “prove stronger scalar source decay.” It is one
of the following genuinely selector-resolved statements for an ordinary one-draw static local
Hamiltonian:

1. cross-incidence anti-concentration after return/carrier removal, strong enough for complete
   approximate circuit union; or
2. high-probability production of occupied observer-resolution channels faster than shallow
   circuit capacity, together with control of same-channel reuse.

Their exact deterministic coupling is formalized in
`StaticShortcutRecurrenceChannelProductionLaw.lean`: `eta^2 W^2 <= B M_sigma R_sigma`, with a
strict capacity contrapositive and a separation premise preventing duplicate-label inflation.

## Verification

Foreground scratch checks:

```text
lake env lean /tmp/hgt_selector_partition.lean
lake env lean /tmp/hgt_selector_saturation.lean
```

Repository check and module-only audit:

```text
lake env lean GaloisForLFunctions/HTGeometry/StaticShortcutSelectorPartitionLaw.lean
lake build GaloisForLFunctions.HTGeometry.StaticShortcutSelectorPartitionLaw
```

All exited `0`; module build completed successfully. `#print axioms` on the principal inequality,
pair identity, injective law, fresh-channel saturation and two-memory capstone reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration occurs in the module. It is
wired directly after its scalar parent in the `HTGeometry` umbrella. No umbrella/full build was
run.

## Honest boundary

These are exact universal Hilbert-space laws and a rigorous correction of the proof architecture.
They do not prove channel production for a local-Hamiltonian ensemble, circuit complexity growth,
plateau density, low-complexity recurrence scale, black-hole interior growth, holography, or
gravitational dynamics. Direct sums, finite partition identities and Cauchy--Schwarz are classical;
external priority for this application has not been established. The master paper remains below
Nature acceptance threshold.
