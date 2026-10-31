import GaloisForLFunctions.RHTower.Heat.HeatUniformDepthZeroDensity
import GaloisForLFunctions.RHTower.Heat.TheHeatCountGrowthLadder

/-!
# The heat-count ladder at inverse-logarithmic heat

Write `N(t)` for the number of nonreal zeros of `H_t` (`nonrealZeroCount`). Zero copies of `ξ` at
depth `|β − ½| ≥ d` with ordinates in `[X, 2X]` persist as nonreal zeros of `H_t` up to the heat
time `t = c d²/log X`, with `c` independent of `d`
(`exists_card_deep_le_heat_count_at_uniform_depth_scale`). Growth laws for `N(t)` transfer through
this time:

* **Window bound** (`exists_deep_window_bound_at_inverse_log_heat`):
  `#F ≤ C log X · N(c d²/log X)`, uniformly in `0 < d ≤ ½`.
* **Exponential envelope**
  (`stretchedExponential_deep_density_of_nonrealZeroCount_at_inverse_log_heat`):
  `N(t) ≤ exp(A t^{−a})` gives `#F ≤ C log X · exp(A (log X/(c d²))^a)`.
* **Subcritical growth** (`subpower_deep_density_of_nonrealZeroCount_lt_one`): for `a < 1` and
  fixed depth, `#F ≤ X^ε` eventually, for every `ε > 0`.
* **Polynomial growth** (`polylog_deep_density_of_polynomial_nonrealZeroCount_uniform`):
  `N(t) ≤ A t^{−a}` gives `#F ≤ C A log X · (log X/(c d²))^a`, uniformly in the depth.

At the persistence time `δ²/(C log⁴ X)` of `TheHeatCountGrowthLadder` the same transfer has
exponent `4a` and needs `a < 1/4`. Here the exponent is `a`; at `a = 1`, `exp(A/t)` at
`t ≍ 1/log X` is already a power of `X`.
-/

open Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- **Window bound at inverse-logarithmic heat.** There are `c, C > 0` such that for large `X`,
every depth `0 < d ≤ ½` and every finite set `F` of zero copies with ordinates in `[X, 2X]` and
`|β − ½| ≥ d`: `#F ≤ C log X · N(c d²/log X)`. -/
theorem exists_deep_window_bound_at_inverse_log_heat :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
        0 < c * d ^ 2 / Real.log X ∧
        ∀ F : Finset XiZeroCopy,
          (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
            d ≤ |(q.1 : ℂ).re - 1 / 2|) →
          (F.card : ℝ) ≤ C * Real.log X * nonrealZeroCount (c * d ^ 2 / Real.log X) := by
  obtain ⟨c, C, hc, hC, X₀, hX₀, hbound⟩ := exists_card_deep_le_heat_count_at_uniform_depth_scale
  refine ⟨c, C, hc, hC, X₀, hX₀, fun X hX d hd hd2 => ?_⟩
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have ht : 0 < c * d ^ 2 / Real.log X := by positivity
  exact ⟨ht, fun F hF => hbound X hX d hd hd2 _ ht (by rw [div_mul_cancel₀ _ hL.ne']) F hF⟩

/-- The inverse-logarithmic time lies below any prescribed positive time, uniformly in the
depth `d ≤ ½`, once `log X ≥ c/t₀`. -/
theorem inverse_log_heat_le {c t₀ d X : ℝ} (hc : 0 < c) (ht₀ : 0 < t₀) (hd2 : d ≤ 1 / 2)
    (hd : 0 < d) (hX : c / t₀ ≤ Real.log X) (hL : 0 < Real.log X) :
    c * d ^ 2 / Real.log X ≤ t₀ := by
  rw [div_le_iff₀ hL]
  rw [div_le_iff₀ ht₀] at hX
  have hd1 : d ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_of_le_one_right hc.le hd1]

/-- **Exponential envelope.** If `N(t) ≤ exp(A t^{−a})` for `0 < t ≤ t₀`, there are `c, C > 0`
such that for large `X`, every depth `0 < d ≤ ½` and every deep window `F` at depth `d`:
`#F ≤ C log X · exp(A (log X/(c d²))^a)`. -/
theorem stretchedExponential_deep_density_of_nonrealZeroCount_at_inverse_log_heat
    {A a t₀ : ℝ} (ht₀ : 0 < t₀)
    (hN : ∀ t : ℝ, 0 < t → t ≤ t₀ →
      (nonrealZeroCount t : ℝ) ≤ Real.exp (A * t ^ (-a))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ∀ F : Finset XiZeroCopy,
        (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
          d ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ C * Real.log X * Real.exp (A * (Real.log X / (c * d ^ 2)) ^ a) := by
  obtain ⟨c, C, hc, hC, X₀, hX₀, hbound⟩ := exists_deep_window_bound_at_inverse_log_heat
  refine ⟨c, C, hc, hC, max X₀ (Real.exp (c / t₀)), fun X hX d hd hd2 F hF => ?_⟩
  have hX₀X : X₀ ≤ X := (le_max_left _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hLt : c / t₀ ≤ Real.log X := by
    rw [← Real.log_exp (c / t₀)]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hX)
  obtain ⟨ht, hcount⟩ := hbound X hX₀X d hd hd2
  calc (F.card : ℝ) ≤ C * Real.log X * nonrealZeroCount (c * d ^ 2 / Real.log X) := hcount F hF
    _ ≤ C * Real.log X * Real.exp (A * (c * d ^ 2 / Real.log X) ^ (-a)) :=
        mul_le_mul_of_nonneg_left (hN _ ht (inverse_log_heat_le hc ht₀ hd2 hd hLt hL))
          (by positivity)
    _ = C * Real.log X * Real.exp (A * (Real.log X / (c * d ^ 2)) ^ a) := by
        rw [Real.rpow_neg ht.le, ← Real.inv_rpow ht.le, inv_div]

/-- **Subcritical heat-count growth forces subpower deep density.** If `N(t) ≤ exp(A t^{−a})` for
`0 < t ≤ t₀` with `a < 1`, then for every fixed depth `0 < δ ≤ ½` and every `ε > 0`, eventually
every deep window at depth `δ` in `[X, 2X]` has at most `X^ε` copies. -/
theorem subpower_deep_density_of_nonrealZeroCount_lt_one
    {A a t₀ : ℝ} (ha : a < 1) (ht₀ : 0 < t₀)
    (hN : ∀ t : ℝ, 0 < t → t ≤ t₀ →
      (nonrealZeroCount t : ℝ) ≤ Real.exp (A * t ^ (-a)))
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ F : Finset XiZeroCopy,
        (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
          δ ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ X ^ ε := by
  obtain ⟨c, C, hc, hC, X₀, hbound⟩ :=
    stretchedExponential_deep_density_of_nonrealZeroCount_at_inverse_log_heat ht₀ hN
  intro ε hε
  have hsub := eventually_log_mul_exp_rpow_le_rpow (C := C) (K := A * (1 / (c * δ ^ 2)) ^ a)
    hC.le ha hε
  filter_upwards [hsub, eventually_ge_atTop X₀, eventually_gt_atTop (1 : ℝ)] with X hXsub hX hX1
    F hF
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX1.le
  refine (hbound X hX δ hδ hδ2 F hF).trans (le_of_eq_of_le ?_ hXsub)
  rw [div_eq_mul_one_div (Real.log X), Real.mul_rpow hL (by positivity)]
  ring_nf

/-- **Polynomial heat-count growth forces polylogarithmic deep density, uniformly in the depth.**
If `N(t) ≤ A t^{−a}` for `0 < t ≤ t₀`, there are `c, C > 0` such that for large `X`, every depth
`0 < d ≤ ½` and every deep window `F` at depth `d`: `#F ≤ C A log X · (log X/(c d²))^a`. -/
theorem polylog_deep_density_of_polynomial_nonrealZeroCount_uniform
    {A a t₀ : ℝ} (ht₀ : 0 < t₀)
    (hN : ∀ t : ℝ, 0 < t → t ≤ t₀ → (nonrealZeroCount t : ℝ) ≤ A * t ^ (-a)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ∀ F : Finset XiZeroCopy,
        (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
          d ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ C * A * Real.log X * (Real.log X / (c * d ^ 2)) ^ a := by
  obtain ⟨c, C, hc, hC, X₀, hX₀, hbound⟩ := exists_deep_window_bound_at_inverse_log_heat
  refine ⟨c, C, hc, hC, max X₀ (Real.exp (c / t₀)), fun X hX d hd hd2 F hF => ?_⟩
  have hX₀X : X₀ ≤ X := (le_max_left _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hLt : c / t₀ ≤ Real.log X := by
    rw [← Real.log_exp (c / t₀)]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hX)
  obtain ⟨ht, hcount⟩ := hbound X hX₀X d hd hd2
  calc (F.card : ℝ) ≤ C * Real.log X * nonrealZeroCount (c * d ^ 2 / Real.log X) := hcount F hF
    _ ≤ C * Real.log X * (A * (c * d ^ 2 / Real.log X) ^ (-a)) :=
        mul_le_mul_of_nonneg_left (hN _ ht (inverse_log_heat_le hc ht₀ hd2 hd hLt hL))
          (by positivity)
    _ = C * A * Real.log X * (Real.log X / (c * d ^ 2)) ^ a := by
        rw [Real.rpow_neg ht.le, ← Real.inv_rpow ht.le, inv_div]
        ring

end

end RHTower.DeBruijn
