# The local de Bruijn–Newman constant

- **ID:** local-de-bruijn-newman
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #30
- **Statement:** With `Λ_X = inf{s ≥ 0 : ∀ s' ≥ s, every zero z of H_{s'} with |Re z − X| ≤ 1 is
  real}`: `Λ = sup_X Λ_X`; RH iff `Λ_X = 0` for every `X`; for every `ε > 0` and large `X`,
  `Λ_X ≤ (2/3 + ε)/log((X − 1)/2π)`; and there are `c > 0`, `X₀` such that a zero `ρ` of `ξ` with
  `Im ρ ≥ X₀`, `Re ρ ≠ ½` gives `Λ_{Im ρ} ≥ c (Re ρ − ½)²/log Im ρ`.

## Lean
Module `RHTower/Heat/TheLocalDeBruijnNewmanConstant.lean` (namespace `RHTower.DeBruijn`):
`localRealTimes`, `localNewmanConstant`, `mem_localRealTimes_of_newmanConstant_le`,
`localNewmanConstant_nonneg`, `localNewmanConstant_le_newmanConstant`,
`le_localNewmanConstant_of_nonreal`, `newmanConstant_eq_iSup_localNewmanConstant`,
`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`,
`eventually_localNewmanConstant_le_twoThirds`, `exists_le_localNewmanConstant_of_offLine_zero`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
`Λ` itself is local-real (every zero of `H_{s'}`, `s' ≥ Λ`, is real), so `Λ_X ≤ Λ`. If
`sup_X Λ_X < s < Λ`, then `s` is not real-rooted, so some zero `z` of `H_s` is nonreal, and every
admissible `s₀` for the window about `Re z` exceeds `s`: `Λ_{Re z} ≥ s`, a contradiction. RH iff
`Λ = 0` (`riemannHypothesis_iff_newmanConstant_eq_zero`). Upper bound: for `s = (2/3 + ε)/log((X − 1)/2π)`
and `s' ≥ s`, either `s' ≥ 1/8 > Λ` or the reality horizon `2π e^{(2/3+ε)/s'} ≤ 2π e^{(2/3+ε)/s} = X − 1`
lies below the window, so its zeros are real (`riemannHeat_zeros_real_twoThirds`). Lower bound: the
zero `z = −i(ρ − ½)` of `H_0` has `Re z = Im ρ`, `|Im z| = d`; up to heat `c d²/log X` a nonreal zero of
`H_t` stays within `d/2` (`exists_nonreal_riemannHeat_zero_at_uniform_depth_scale`), inside the window.

## What it changes (B)
The de Bruijn flow has the same local pincer as the slice heat: `c depth²/log X ≤ Λ_X ≤ (2/3 + ε)/log X`,
with the upper end set by Weyl's exponent (sharp for size plus positive kernel, #22) and the lower end
by the depth. `Λ_X → 0`, so `Λ` is attained over bounded heights. Closing the de Bruijn pincer is the
same problem as for the slice (depth bounds); with Lindelöf the upper end is `½/log X` (#23).

## Log
- 2026-10-31 — created; proved; formalized.
