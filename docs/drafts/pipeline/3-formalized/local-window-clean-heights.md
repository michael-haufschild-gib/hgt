# Clean heights in every window `[T, T + T^{24/25}]`

- **ID:** local-window-clean-heights
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** loop card `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, rows 128–129. Localizes MUST-641 (tail law) and MUST-644 (θ = 1/9 gate).
- **Statement:** For all large `T` and every `T^{24/25} ≤ H ≤ T`, the window moment `Σ_{T+1<Im ρ≤T+H−1} m_ρ(Re ρ − ½)⁺` is at most `(11/50)H`. On `[T + 3/2, T + H − 3/2]`, Laguerre with vertical monotonicity, all-order slice positivity and the Speiser clean-height condition each hold on measure `≥ (14/25)H − 3`.

## Goal
Every RH receiver in this family (LA, WD slices, Speiser) is a statement at every height. The global density versions (MUST-618/638/644) control `[0, V]` as a whole. They allow the bad heights to fill whole windows of length `≍ V`. This card removes that possibility for windows of length `T^{24/25}`.

## Gates
- [x] 0 → 1 in-progress: high-block audit (row 128). The `ε·a` loss of the dyadic law is only the taper `2(c+ε)a^{19/20}`.
- [x] 1 → 2 fully-proven: window Littlewood + window Riemann–von Mangoldt (`O(log T)` remainder, corpus `exists_xiZeroCount_routeKSmoothRVMCount_log_remainder`) + reflection half-count.
- [x] 2 → 3 formalized: `ZetaLocalWindowTail`, `XiLocalWindowDensity`. `lake env lean` clean, `--old` builds, standard axioms, 0 collisions, wired in `RHTower.lean`.
- [ ] 3 → 4: not planned.

## Proof outline
1. `exists_highBlock_bound_of_mainTerm_deep_window`: `∫_a^v ‖ζΨ(½−d+iτ)‖² ≤ (c+ε)(v − a + 2a^{19/20})`. This is the deep high block with its last absorption step removed. The old dyadic statement is now a corollary.
2. `exists_window_littlewood`: take admissible heights `T₁ ∈ (T, T+1)` and `T₂ ∈ (T+H−1, T+H)`, where `ζΨ` is zero-free on the horizontal edges. With `d = R/log T₂`, Littlewood on `[½ − d, 15/2] × [T₁, T₂]` and the reflection bridge give `2π(dΔN + Δtail_d) ≤ (Δ/2) log(Msq/Δ) + C + K(log T₂ + log N⁵)`.
3. `window_bounds_of_littlewood`: the scalar steps are as follows.
   - The taper is `≤ (η/8)Δ` because `T^{19/20} = T^{−1/100}·T^{24/25}`.
   - Riemann–von Mangoldt gives `2πdΔN ≥ Δ(R − η/16) − 4πC_RR`.
   - The additive terms are `≤ (η/8)Δ`.
   - Hence `4π·tail ≤ (log c − 2R + η)H`. Since at most half the window zeros lie right of the line, `4π·moment ≤ (log c − R + η)H`.
4. `volume_xiShadow_inter_Icc_le_windowTail`: the shadow measure in a window is at most twice the window moment.

## Limits
- The window exponent `24/25` comes from the taper `u^{95}` of the deep pair error. Lowering it requires re-deriving the dual off-diagonal with a shorter taper. The natural floor of mean-square methods is `T^{1/2+θ}`.
- The window moment constant is `≈ 0.21` rather than `7/50`, because the two-thirds proportion of simple critical zeros (Zeta23) is a dyadic statement and does not localize.
- Density only: nothing is said at every height.

## Log
- 2026-10-01: rows 128–129. Formalized and audited. STATUS MUST-651.
- 2026-10-01: row 131. The Hadamard sign window area `≥ (7/25)H − 3/2` (`eventually_volume_hadamardSign_window_ge`) is added to `XiLocalWindowDensity`. STATUS MUST-651 addendum.
