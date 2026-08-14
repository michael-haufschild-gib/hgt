# Observer–spectral frame-energy reciprocity (2026-08-14)

## Advance

Created/strengthened `formal/GaloisForLFunctions/HTGeometry/StaticShortcutRecurrenceEnergyLaw.lean`.

Unconditional declarations:
- `weightedMemorySum`
- `weightedAlignment`
- `weightedRecurrenceEnergy`
- `weightedAlignment_eq_inner_sum`
- `weightedRecurrenceEnergy_eq_norm_sq`
- `weightedAlignment_sq_le_recurrenceEnergy`
- `weightedAlignment_sq_eq_recurrenceEnergy_of_historyProbe`
- `inner_unitaryFlow_eq_recurrenceKernel`
- `weightedRecurrenceEnergy_flow_eq_kernel`
- `threshold_sq_le_weightedRecurrenceEnergy`
- `finitePreparationFrameEnergy`
- `finitePreparationFrameEnergy_eq_pairAverage`
- `preparationMemory_norm_sq_eq_frameEnergy_sub_universal`
- `adaptive_shortcuts_force_recurrence_energy`

Main law: after subtracting completed centralizer sector, a finite weighted history of adaptively chosen shortcuts satisfies
`
(eta sum_j w_j)^2 <= F_Pi(Y) sum_{i,j} w_i w_j
  <x-Px,U(t_j-t_i)(x-Px)>
`
where `F_Pi(Y)=||finitePreparationMoment Y||^2-||Pi x||^2=||preparationMemory||^2>=0`.
Also
`
||finitePreparationMoment Y||^2
= |Y|^{-2} sum_{k,l}<y_k,y_l>.
`

Thus changing target selectors vanishes before temporal estimate. Target side is conditioned average frame overlap; source side is one stationary centralizer-centered recurrence kernel.

## Conjecture loop

- C0 pointwise monotone memory flux: falsified by finite rotations/recurrence.
- C1 one-time Cauchy: true but insignificant.
- C2 adaptive histories force recurrence Gram energy: proved and Lean formalized.
- C3 improve quadratic loss by pure Hilbert geometry: sharply falsified. For every weighted history, choosing probe equal to weighted history sum saturates Cauchy exactly.
- C4 recover capacity using minimum endpoint separation: retired as wrong invariant. Exact aggregate replacement is conditioned target frame energy, i.e. average pair overlap. No minimum endpoint gap or minimum spectral gap appears.

## Scale audit

This does NOT prove Brown first onset. It precisely factorizes open core into two growing-replica estimates after common return/carrier removal:
1. occupied heap-image conditioned frame energy `F_Pi(Y)=O(1/intrinsic capacity)`;
2. quenched upper bound for centralizer-centered recurrence energy of ordinary one-draw time-independent local Hamiltonians, strong enough for complete circuit union.

If (1) holds, Cauchy loses one capacity factor, not its square. Pure Hilbert geometry cannot prove (1); bounded-dependence heap/preparation structure must.

## Verification

Exact source copied to `/tmp/hgt_static_shortcut_full.lean`.
`lake env lean /tmp/hgt_static_shortcut_full.lean` passed in foreground.
`#print axioms` for seven substantive theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
No sorry/admit/axiom/opaque/unsafe in module. No project/full build run after user directive.
Umbrella already imports module at `formal/GaloisForLFunctions/HTGeometry.lean`.

Cards:
- `docs/drafts/pipeline/2-fully-proven/centralizer-centered-shortcut-history-recurrence-energy-law.md`
- `docs/drafts/pipeline/3-formalized/centralizer-centered-shortcut-history-recurrence-energy-law.md`
- master log appended at `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.

## Literature boundary

Positive-definite unitary kernels, Gram identities, and Cauchy are classical. Candidate novelty is adaptive two-memory/centralizer/frame-energy factorization; external priority remains unverified. No manuscript-headline claim yet.

Related memory: `mem:quantum_recurrence/local_circuit_heap_capacity_2026_08_13`.
