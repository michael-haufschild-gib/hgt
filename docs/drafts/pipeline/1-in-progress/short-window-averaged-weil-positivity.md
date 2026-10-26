# Averaged Weil positivity on windows of length Γ^θ (Q1 / B3.7)

- **ID:** short-window-averaged-weil-positivity
- **Stage:** 1-in-progress
- **Type:** THEOREM (in progress)
- **Source:** `docs/reports/review-2510/hard-obstacles-summary.md` Q1, B3.7, milestone (1).
- **Statement:** There are `κ₀, c₀, C₀ > 0` and `Γ₀` such that for `Γ ≥ Γ₀`, `Γ^{199/200} ≤ H ≤ Γ/4`,
  `0 ≤ A ≤ κ₀ log Γ` and real `F₀ ∈ C²_c([−A, A])`:
  `(1/H) ∫_Γ^{Γ+H} [Q(F₀ cos γ·) + Q(F₀ sin γ·)] dγ ≥ c₀ log Γ ‖F₀‖² − (error) N(F₀)²`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Paper proof (plan)
The dyadic proof (`exists_logarithmic_aperture_frequencyAverage_quadrature_pos`) uses the window
only through four inputs; each has a short-window form.
1. *Selberg near-line density on short windows.* The mollified mean-square chain
   (`integral_normSq_zetaTwoLength_rightShift_le`) holds for every `[T₁,T₂] ⊂ [U/4,U/2]` with
   `T₂ − T₁ ≥ e^{99L/100}`; only the final choice of admissible heights is dyadic. Choosing admissible
   heights in `(B, B+1)` and `(B+H−1, B+H)` gives
   `2π(a/L)·#{Re ρ ≥ ½ + 2a/L, Im ρ ∈ [T₁,T₂]} ≤ (T₂−T₁) A e^{−a/1200} + K L` for every
   `[B, B+H] ⊂ [U/4, U/2]`, `H ≥ U^{99/100} + 2`. Dyadic shells in `v` give the weighted count.
2. *RvM on short windows.* `exists_xiPosZeroCount_window_bounds`: the core `(Γ + H/4, Γ + H/2]`
   carries `≥ c H log Γ` zeros.
3. *Per-zero core bound.* For core ordinates, `∫_window ‖F̂(depthSum)‖² ≥ 2π‖F₀‖² − O(e^A N²/H²)`.
4. *Local shell absorption on `[Γ−H, Γ+2H]`.* Shallow zeros (depth `≤ C₂/log Γ`) by the local count
   `O(H log Γ)`; deep zeros by step 1 with `U = 3Γ`; the far zeros by Lorentz decay
   `(1+D²)^{−2}`, total `O(e^A N² log Γ/H²)`.
Assembly as in the dyadic case with `1/Γ` replaced by `1/H`.

## Log
- 2026-10-25: inputs located; File A (`RHTower/SelbergShortWindowNearLineDensity.lean`) first.
