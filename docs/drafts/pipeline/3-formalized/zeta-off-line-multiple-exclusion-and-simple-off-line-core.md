# Off-line multiple zeros are charged twice: the simple off-line core of three quarters

- **ID:** g75-offline-multiple-exclusion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/rh/cross-route-producers-and-frontiers/seventy-five-percent-loop-2026-10-25.md`
- **Statement:** For `ζ`, unconditionally, for every `ε > 0` and all large `T`:
  `(2/3 − ε)N(T,2T) + M_off(T,2T) ≤ N₀ˢ(T,2T)`, hence `S_off + 2M_off ≤ (1/3 + ε)N`,
  `M_off ≤ (1/6 + ε)N`, and either `N₀(T,2T) ≥ (3/4)N(T,2T)` or `S_off(T,2T) ≥ (1/6 − ε)N(T,2T)`.
  Here `M_off` counts off-line zeros of multiplicity `≥ 2` with multiplicity, `S_off` counts simple
  off-line zeros, `N₀` counts critical zeros with multiplicity. At the Montgomery–Taylor constant
  `HD(1) = 0.6725…`: `(HD(1) − ε)N + M_off ≤ N₀ˢ`, `S_off + 2M_off ≤ (1 − HD(1) + ε)N`, and either
  `N₀ ≥ (3/4)N` or `S_off ≥ (HD(1) − 1/2 − ε)N` (`HD(1) − 1/2 = 0.1725…`).

## Paper proof
The `c = 2` multiplicity-aware rank–trace step of Alpöge–Furman gives, on the block data of
`𝒵(I′)`, `4 tr Â − ‖Â‖_F² ≤ 3s₁ + 4s₂ + 4p`. Writing `N = s₁ + 2s₂ + 2p + E` (multiplicity excess
`E ≥ 0`), this is `4 tr Â − ‖Â‖_F² − 2N + 2E ≤ s₁`. An off-line zero of multiplicity `m ≥ 2` adds
`m − 1 ≥ m/2` to `E`, so `M_off(I′) ≤ 2E`. The tail perturbation `Â → Ĝ`, the window passage
`I′ → (T,2T]` (`M_off` is monotone in the window, `s₁(I′) ≤ N₀ˢ(T,2T) + N_II`) and the unchanged
moments `tr Ĝ ≥ (1 − δ)N`, `‖Ĝ‖_F² ≤ (κ(λ) + δ)N` give `(H(λ) − ε)N ≤ N₀ˢ − M_off`; `λ → 1⁻` gives
`2/3`. The census `N = N₀ + S_off + M_off` and `N₀ˢ ≤ N₀` give the corollaries.

## Lean
Module `formal/GaloisForLFunctions/RHTower/Zeta23OffLineMultipleExclusion.lean` (wired in
`RHTower.lean`): `two_thirds_add_offLineMultipleMass_le_N0simple`,
`offLineMultipleMass_le_one_sixth`, `offLineSimple_add_two_offLineMultiple_le_one_third`,
`three_quarters_or_simple_offLine`; block law `blockOffLineMultipleMass_add_le`, seam
`seamA_mult2_offLineMultiple`. Montgomery–Taylor companion
`formal/GaloisForLFunctions/RHTower/Zeta23OffLineMultipleExclusionMontgomeryTaylor.lean`:
`HD_one_add_offLineMultipleMass_le_N0simple`,
`offLineSimple_add_two_offLineMultiple_le_one_sub_HD_one`, `three_quarters_or_simple_offLine_HD_one`
(the excess seam run through Theorem D's endgame). The `c = 3` census
`formal/GaloisForLFunctions/RHTower/Zeta23SimpleOrCriticalCensus.lean`: an off-line pair of
multiplicity `m` uses `10m − 9 ≥ (11/2)m` of the `c = 3` budget (`c3_budget_add_offLineMultipleMass_le`),
so `(GD(1) − ε)N ≤ N − (11/8)M_off` (`GD_one_le_N_sub_offLineMultipleMass`) and at least
`((3 + 8GD(1))/11 − ε)N ≈ 0.881N` zero copies are simple or on the critical line
(`simple_or_critical_dyadic`). The optimal level
`formal/GaloisForLFunctions/RHTower/Zeta23SimpleOrCriticalOptimal.lean`: at `c = 2 + √2` a simple
off-line pair costs exactly `2c − 1` per copy (`c² = 2(2c − 1)`) and a multiple one leaves
`(3/2 + √2)` per copy unused, so `2c tr Â − ‖Â‖² ≤ (2c − 1)N − (3/2 + √2)M_off`
(`sqrtTwo_budget_le`), `(3/2 + √2)M_off ≤ (1 − HD(1) + ε)N` (`sqrtTwo_offLineMultipleMass_le`), and at
least `1 − (1 − HD(1))/(3/2 + √2) − ε = 0.8876…` of the zero copies are simple or critical
(`simple_or_critical_optimal`; cumulative `simple_or_critical_optimal_cumulative`): Lamzouri's constant, the optimum of the `c`-family
(`max_c (2c − 1 − c²/4)` subject to `c² ≤ 2(2c − 1)`, `levelGap_le`; the trace-aware mixture bound
`(1 − α²)/(3 − α) ≤ 6 − 4√2 = (3/2 + √2)⁻¹`, `mixture_le`, `six_sub_four_sqrt_two_eq`). The same budget runs through Theorem D for
`L(s, χ)`: for every primitive `χ` mod `q > 1`, at least `0.8876…` of the zero copies of `L(s, χ)` are
simple or critical (`Zeta23DirichletSimpleOrCriticalOptimal.lean`,
`simple_or_critical_optimal_dirichlet`), and `≥ 0.8042…` of its zero ordinates are critical
(`critical_ordinates_dirichlet`); the off-line multiple exclusion holds for `L(s, χ)` too:
`(HD(1) − ε)N_χ + M_off(χ) ≤ N₀ˢ(χ)` (`HD_one_add_offLineMultipleMass_le_N0simple_dirichlet`). Localization
`formal/GaloisForLFunctions/RHTower/Zeta23SimpleOffLineNearLine.lean`: by reflection, zero copies at
displacement `> d` are at most `2/d` times the right off-line moment (`offLineFarMass_le`); the dyadic
moment `≤ (67/1000)T` gives at most `N/A` copies beyond `A/log T` (`eventually_offLineFarMass_le`), so
either `N₀ ≥ (3/4)N` or at least `(HD(1) − 1/2 − 1/A − ε)N` simple off-line zeros lie within `A/log T`
of the line (`three_quarters_or_simple_offLine_near_line`); at `A = 4`, at least `3/4` of the zero
copies lie within `4/log T` of the line (`three_quarters_within_four_div_log`). Ordinate census
`formal/GaloisForLFunctions/RHTower/Zeta23CriticalOrdinateCensus.lean`: a non-critical ordinate
carries an off-line zero and its reflection, so `2·#ordinates + N₀ ≤ 2·#critical ordinates + N`
(`two_mul_card_ordinates_le`), and with `N₀ˢ ≥ (2/3 − ε)N` at least `(4/5 − ε)` of the zero
ordinates in `(T, 2T]` carry a critical zero (`four_fifths_critical_ordinates`); at the
Montgomery–Taylor constant `2HD(1)/(1 + HD(1)) − ε = 0.8042…` (`critical_ordinates_montgomeryTaylor`,
with `HD_one_le_one`); cumulative over `(0, T]`: `four_fifths_critical_ordinates_cumulative`.
Axioms: `propext, Classical.choice, Quot.sound`.

## What it shows
The three-quarters problem is a bound on simple off-line zeros: `S_off < (HD(1) − 1/2)N` suffices,
against the unconditional `S_off ≤ (1 − HD(1))N`.
Counted by ordinate, the same certificate already gives `4/5 > 3/4`: the three-quarters problem for
zero copies is exactly the charge of `2` per off-line ordinate.
Off-line multiple zeros cost twice in the certificate, so the extremal configuration of the
two-thirds theorem consists of simple off-line pairs, which the continuity barrier makes
indistinguishable from on-line double zeros.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`; axioms standard

## Log
- 2026-10-25 — proved and formalized.
