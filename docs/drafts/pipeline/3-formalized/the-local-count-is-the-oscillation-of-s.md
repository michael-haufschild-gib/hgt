# The local zero count is the oscillation of `S`

- **ID:** local-count-oscillation-s
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #8; `reboot-final.md` WP-A1
- **Statement:** A set of zero copies with ordinates in `(t, t + H]` has at most
  `(H/2π) log(t + H) + S(t + H) − S(t)` elements. For `T₀ ≥ 2πe`: the local count
  `N(t + H) − N(t) ≤ C(H log(t + H) + 1)` (all `t ≥ T₀`, `H ≥ 0`) implies
  `S(t + H) − S(t) ≤ C(H log(t + H) + 1)`; conversely the bound for `S` gives the local count with
  `C + 1/(2π)`.

## Lean
`SquareRootThreshold/TheLocalCountIsTheOscillationOfS.lean` (namespace `RHTower`):
`card_le_window_main_add_oscillation`, `routeKSmoothRVMCount_mono_of_base_le`,
`rvmRemainder_oscillation_le_of_window_le`, `window_le_of_rvmRemainder_oscillation_le`. Axioms:
`propext`, `Classical.choice`, `Quot.sound`.

## Paper proof
`N = M + S` by definition. `card F ≤ N(t + H) − N(t)` (`card_le_xiZeroCount_sub`),
`M(t + H) − M(t) ≤ (H/2π) log(t + H)` (convexity of `u log u`), and `M` is nondecreasing beyond `2πe`.

## What it changes
WP-A1 asks which remainder bound the scale-`δ` count needs. Answer, as a theorem: exactly a
one-sided short-scale oscillation bound `S(t + H) − S(t) ≪ H log t + 1` for `H ∈ [δ, 1]`. The heat
detection law (`heat-detection-from-the-local-zero-configuration.md`) needs it at every scale in
`[δ, 1]` around `t`; the corpus has the unit scale only (`exists_xiZeroCount_window_le`) and
`S` unbounded (`rvmRemainder_unbounded`). For the lag family the relevant count is the off-line one
(`OffLineCopiesLocallyBounded`), which this equivalence does not reach.

## Log
- 2026-10-31 — created; proved; formalized.
