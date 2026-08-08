# Quenched shortcut–annular equivalence — Lean certificate

- **ID:** `quenched-shortcut-annular-equivalence-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `quenched-shortcut-annular-equivalence.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/QuenchedShortcutAnnularEquivalence.lean`, imported by
`GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `oneParameterRayOrbit_smul` — for `a ≠ 0` the ray orbit through `a • y` is the ray orbit
   through `y`: the two parameter rays sweep the same set.  `completedRayOrbit_smul` closes it,
   and `orbitFunctional_smul` states the consequence — every quantity read off the completed
   orbit, in particular `I = -log ν(E)`, is radially scale invariant.  This is `(10)`, proved
   rather than assumed, and it needs no Haar measure on the orbit closure: the rarity functional
   is an arbitrary function of the completed orbit set.
2. `linear_generator_homogeneous` — `(9)`: a linear generator makes the observable homogeneous.
3. `timeEvent_eq_preimage_smul` — combining 1 and 2, the resolved shortcut event at time `t` is
   the dilated preimage `t⁻¹ · S_B` of the fixed unit-time shortcut set `resolvedShortcutSet`.
4. `lintegral_gaussianWeight_preimage_smul` — the Gaussian dilation identity, from the Haar
   scaling law `Measure.map_addHaar_smul`.  `gaussianMass_resolvedShortcut_timeEvent` is the
   card's boxed `(4)`.
5. `measure_inter_closedBall_le_lintegral` and `measure_inter_closedBall_le_of_lintegral_le` —
   `(5)`: a probability bound gives `vol(S_B ∩ B_t) ≤ e^{1/2} t^m P`.
   `measure_resolvedShortcut_inter_closedBall_le` states it for the shortcut set.
6. `dyadicShell`, `iUnion_dyadicShell`, `gaussianWeightAt_le_on_dyadicShell`,
   `lintegral_gaussianWeightAt_le_tsum`, `lintegral_gaussianWeight_preimage_smul_le_tsum` — `(7)`:
   the shells cover the space, the Gaussian weight on the `j`th shell is at most `e^{1/2 - 4^j/2}`
   (the `e^{1/2}` is the enlarged universal constant that absorbs the inner ball), and summing
   transfers any annular volume bound with the same exponent.
   `gaussianMass_resolvedShortcut_le_tsum` states it for the shortcut set.

The resolved volume-growth law `(8)` is **not** present in any form, as the card's formal target
requires: nothing in the module assumes a growth rate for `vol(S_B ∩ B_R)`.

## Design notes

Every measure statement is made in `ℝ≥0∞` with `∫⁻`, so no integrability side condition and no
measurability hypothesis on the rarity functional `I` enters — the hostile audit's first bullet is
answered by construction rather than by a Cesàro approximation argument.  The coefficient space is
an arbitrary finite-dimensional real normed space carrying an additive Haar measure; `m` is
`Module.finrank ℝ V`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/QuenchedShortcutAnnularEquivalence.lean` — clean.
- `lake build GaloisForLFunctions.HTGeometry.QuenchedShortcutAnnularEquivalence` — succeeds.
- `#print axioms` on all twelve theorems: `[propext, Classical.choice, Quot.sound]` only.
