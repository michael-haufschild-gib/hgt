# Near-line occupancy and clustering: the proportion hierarchy

- **ID:** NLAB
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.5.1 (B20), §2.5.3 (B21)
- **Statement:** (A) critical-line proportion `→ 1` implies `100%` critical-scale clustering, hence
  all eight forms of `(L)`; (B) a unit-window model with simple critical proportion `→ 1` in every
  window and depth tails `≪_r e^{−ra}V` for every `r > 0` satisfies `(L)` and violates `(D_win)`.

## Goal
Place B20 and B21 relative to the two unconditional input families of the corpus (critical-line
proportions; exponential near-line depth tails). B20 is a proportion statement; B21 is not.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below)
- [ ] 2 → 3  formalized

## Paper proof
**(A).** For `a > 0` the zeros with `Re ρ ≥ ½ + a` are off the line, so
`offLineCountBeyond a V ≤ N(V) − N₀(V) = N(V)(1 − N₀(V)/N(V))`. By Riemann–von Mangoldt
`N(V) ≤ 2V log V` for large `V`. Hence `offLineCountBeyond(κ/log V, V)/(V log V) ≤ 2(1 − N₀/N) → 0`,
which is item 5 of `criticalClustering_logMean_mollifier_hecke_tfae`.

**(B).** Window `m ≥ 256`: `2b_m − 2` simple critical zeros, `b_m = ⌊log m/4π⌋ + 1`, and one pair
`½ ± d_m + i(·)`, `d_m = √(log log m)/log m`. Put `u = √(log log V)`; for `m ∈ [V, 2V]`,
`u/(2 log V) ≤ d_m ≤ 2u/log V`.
- Proportion: `(2b_m − 2)/(2b_m) → 1`.
- Depth tail, every `r > 0`: for `1 ≤ a ≤ 2u` the left side is `≤ 2π(2u/log V)(2V)`, and
  `u e^{ra} ≤ e^{(2r+1)u} ≤ e^{u²} = log V` once `u ≥ 2r + 1`; for `a > 2u` it is `0`.
- `(L)`: `V⁻¹Σ d_m ≤ 4u/log V ≤ 4/u → 0`. Clustering: `≤ 2` off-line zeros per window.
- `¬(D_win)`: for fixed `A`, `d_m ≥ u/(2 log V) ≥ A/log V` once `u ≥ 2A`: every window is bad.
  `¬(D_zero)` follows since `(D_zero) ⇒ (D_win)` in every model.

## Route verdicts (conjecture loop)
1. Disc argument: count `≪ V L I(½+A/L)/A`; the floor
   `exists_eventually_integral_normSq_zetaMollified_rightShift_ge_of_lt_one` keeps `I ≥ c(θ,a) > 0`
   for `θ < 1`: closed.
2. Explicit-formula detector of length `T^κ`: a depth-`A/L` zero has amplification `e^{κA}` on a halo
   of width `≍ A/L`; the mean-value budget gives `#bad ≪ T L poly(A) e^{−2κA}`, i.e. the double-log
   threshold `(log log V)/(2κ)`. Planck-spaced deep multipoles cancel the signal for `κ ≤ 1`.
   B21 needs depth decay at rate `≍ log log V`, i.e. length `T^{c log log T}`; (B) shows no fixed rate
   suffices.
3. `ζM` self-duality identity `\bar M − χM = χM\bar g − \bar M g`: equivalent to `ζ = e^{−iϑ}Z`;
   INSIGNIFICANT.
4. B20 beyond `θ → ∞`: only a lower-tail law of `|ζΨ|` (`JensenSecondMomentSaturation`) or
   proportion `→ 1` (A).

## Log
- 2026-11-05 — created in 1-in-progress; paper proof of (A), (B)
