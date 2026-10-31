# The local heat threshold has Selberg's exponential tail

- **ID:** local-heat-threshold-exponential-tail
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #24
- **Statement:** There are `A, K ≥ 0` such that for all large `U`, at heights
  `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)`, for every `2 ≤ κ ≤ L/2 − 2` (`L = log U`):
  `|{t ∈ [T₁ + ½, T₂ − ½] : λ_t > κ²/(3L²)}| ≤ A(T₂ − T₁)e^{−κ/2400} + K L²`.
  Corollary: for every `κ > 0`, eventually
  `|{t ∈ [U/4 + 2, U/2 − 2] : λ_t > κ/log U}| ≤ A U exp(−√(3κ log U)/2400) + K log² U`.
  Mean value: `∫_{U/4+2}^{U/2−2} λ_t dt ≤ C U/log² U` for all large `U`.

## Lean
Module `RHTower/Heat/TheLocalHeatThresholdHasAnExponentialTail.lean` (namespace `RHTower.DeBruijn`):
`exists_shadow_of_lt_localHeatThreshold`, `exists_volume_localHeatThreshold_gt_le_exp`,
`eventually_volume_localHeatThreshold_gt_le_exp`, `le_add_sum_layers`, `setIntegral_le_layers`,
`sum_layer_exp_le`, `layer_sum_le`, `exists_integral_localHeatThreshold_le`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
If `λ_t > κ²/(3L²)`, the cone-defect bound (`localHeatThreshold_le_of_cone`: every zero copy with
`(Im z)² ≤ (Re z − t)² + 3λ` forces `λ_t ≤ λ`) gives a zero copy `z = −i(ρ − ½)` with
`(Re ρ − ½)² > (Im ρ − t)² + κ²/L²`. Hence `|Re ρ − ½| > κ/L` and `|t − Im ρ| < |Re ρ − ½|`: `t` is in
the `κ`-shadow. The `κ`-shadow has measure `≤ A(T₂ − T₁)e^{−κ/2400} + KL²`
(`exists_speiserShadow_exponential_density`, from Selberg's near-line density through the tail
moment). For the corollary take `κ = √(3κ' L)`, which lies in `[2, L/2 − 2]` for large `L`, and use
`[U/4 + 2, U/2 − 2] ⊆ [T₁ + ½, T₂ − ½]`, `T₂ − T₁ ≤ U/4`.

Mean value. `λ_t` is lower semicontinuous, hence measurable, and `0 ≤ λ_t ≤ λ_WD < 1/12`. With
`λ_j = (j + 2)²/(3L²)` for `j ≤ N = ⌊L/2 − 4⌋`, `λ_{N+1} = 1/12`, monotone, the pointwise layer bound
`x ≤ λ_0 + Σ_{j ≤ N} [λ_j < x](λ_{j+1} − λ_j)` integrates to
`∫ λ_t ≤ λ_0 ΔT + Σ_j (λ_{j+1} − λ_j)(AΔT e^{−(j+2)/2400} + KL²)`. Here `λ_{j+1} − λ_j = (2j + 5)/(3L²)` for
`j < N` and `Σ_j (2j + 5)e^{−(j+2)/2400} ≤ 18 · 2400³` (`e^y ≥ y³/6`, telescoping); the top layer has
weight `≤ 1/12` and `e^{−(N+2)/2400} ≤ e^{−L/9600} ≤ L^{−2}`; the `KL²` terms total `≤ KL²/12 ≤ U/L²`.

## What it changes (B)
`λ_t` is a depth² gauge in distribution as well as pointwise: it inherits the exponential depth law
of the zeros. Typical heights have `λ_t ≍ 1/log² t`; the rate-`κ/log t` failures, which the pincer
`[depth²/200, 2/3 + ε]` allows at every height, occupy measure `U·exp(−c√(κ log U))`. This quantifies
`eventually_volume_localHeatThreshold_gt_le` (`o(U)`) and the corpus a.e. repair at
`c/log² U` (exceptional proportion `≪ e^{−c'√c}` by the first statement with `κ ≍ √c`). On average
`λ_t log t ≪ 1/log t`: the mean heat rate tends to `0`, while at an off-line ordinate the rate is
`≥ depth²/200`.

## Log
- 2026-10-31 — created; proved; formalized.
