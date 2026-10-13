import GaloisForLFunctions.RHTower.CosDilationCumulativeExcursionRigidity

/-!
# Symmetric Collar Annihilation Laws and Inversion-Folded Window Identities for Blind Cores

Let `f : ℝ → ℝ` be a continuous blind core supported in `[α, β] ⊂ (0, ∞)` (`0 < α ≤ β`) with
`Ψ_f(0) = 0` (`cosDilationKernel f 0 = 0`) and `Ψ_f(n) = 0` for all `n ≥ 2`.

In `CosDilationCumulativeExcursionRigidity` we established the general symmetric window unfolding
(`cosDilationKernel_one_mul_sin_div_pi_eq_intervalIntegral`): for any `c ∈ [0, 1/2]` with
`c ≤ α / β` and `β / α ≤ 3 - c`,
`Ψ_f(1) * sin(2π c) / π = (∫ r in (1 - c)..(1 + c), A_f(r) dr) + (∫ r in (2 - c)..(2 + c), A_f(r) dr)`.

Since `sin(2π (1/2 - c)) = sin(π - 2π c) = sin(2π c)`, applying this unfolding simultaneously at
`c` and at `1/2 - c` (whenever `c ∈ [0, 1/4]`, `1/2 - c ≤ α / β`, and `β / α ≤ 5/2 + c`) equates
the two window sums and cancels their inner cores `[1 - c, 1 + c]` and `[2 - c, 2 + c]`, yielding:

* **Reflected window unfolding at `1/2 - c`**
  (`cosDilationKernel_one_mul_sin_div_pi_eq_half_sub_intervalIntegral`):
  `Ψ_f(1) * sin(2π c) / π = (∫ r in (1/2 + c)..(3/2 - c), A_f(r) dr) + (∫ r in (3/2 + c)..(5/2 - c), A_f(r) dr)`.
* **Four-collar annihilation law** (`dilationAutocorr_four_collar_sum_eq_zero`):
  `(∫ r in (1/2 + c)..(1 - c), A_f(r) dr) + (∫ r in (1 + c)..(3/2 - c), A_f(r) dr) + (∫ r in (3/2 + c)..(2 - c), A_f(r) dr) + (∫ r in (2 + c)..(5/2 - c), A_f(r) dr) = 0`.
* **Three-collar annihilation law when `β / α ≤ 2 + c`**
  (`dilationAutocorr_three_collar_sum_eq_zero_of_le_two_add`):
  when `β / α ≤ 2 + c`, the fourth collar `[2 + c, 5/2 - c]` lies outside the support of `A_f`, so
  `(∫ r in (1/2 + c)..(1 - c), A_f(r) dr) + (∫ r in (1 + c)..(3/2 - c), A_f(r) dr) + (∫ r in (3/2 + c)..(2 - c), A_f(r) dr) = 0`.
* **Sixth/third-period collar annihilation (`c = 1/6`)**
  (`dilationAutocorr_sixth_third_four_collar_eq_zero`,
  `dilationAutocorr_sixth_third_three_collar_eq_zero`):
  specializing to `c = 1/6` gives four-collar annihilation for all `β ≤ (8/3) α` and three-collar
  annihilation for all `β ≤ (13/6) α`.
* **Support-adapted three-collar annihilation for `2α ≤ β ≤ (9/4)α`**
  (`dilationAutocorr_support_adapted_three_collar_eq_zero`):
  setting `c = β / α - 2 ∈ [0, 1/4]` uses `(β - 2α)(2β - α) ≥ 0` to verify `1/2 - c ≤ α / β`
  automatically and kills the fourth collar identically across `[2α, (9/4)α]`.
* **Inversion-folded right-half-line window law**
  (`cosDilationKernel_one_mul_sin_div_pi_add_logPrimCore_eq`):
  combining the window unfolding with the Cycle 7 inversion-dual identity folds the left-half-line
  term `∫ r in 0..(1 - c), A_f(r) dr` onto `(1 - c)⁻¹ > 1`, expressing
  `Ψ_f(1) * sin(2π c) / π + (1 - c) * A_{logPrimCore f}(1 - c)` purely in terms of cumulative
  integrals on the right half-line `[1, ∞)`.
-/

open MeasureTheory Set Real

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### Reflected window unfolding and the four-collar / three-collar annihilation laws -/

/-- **Reflected symmetric window unfolding at `1/2 - c`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0` and any
`c ∈ [0, 1/4]` satisfying `1/2 - c ≤ α / β` and `β / α ≤ 5/2 + c`,
`Ψ_f(1) * sin(2π c) / π = (∫ r in (1/2 + c)..(3/2 - c), A_f(r) dr) + (∫ r in (3/2 + c)..(5/2 - c), A_f(r) dr)`. -/
theorem cosDilationKernel_one_mul_sin_div_pi_eq_half_sub_intervalIntegral
    (hf : Continuous f) {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hc0 : 0 ≤ c) (hc_quarter : c ≤ 1 / 4)
    (hc_lo : 1 / 2 - c ≤ α / β) (hc_hi : β / α ≤ 5 / 2 + c) :
    cosDilationKernel f 1 * Real.sin (2 * π * c) / π =
      (∫ r in (1 / 2 + c)..(3 / 2 - c), dilationAutocorr f r) +
        (∫ r in (3 / 2 + c)..(5 / 2 - c), dilationAutocorr f r) := by
  have hc'_0 : 0 ≤ 1 / 2 - c := by linarith
  have hc'_half : 1 / 2 - c ≤ 1 / 2 := by linarith
  have hc'_hi : β / α ≤ 3 - (1 / 2 - c) := by linarith
  have hUnfold := cosDilationKernel_one_mul_sin_div_pi_eq_intervalIntegral
    hf hα hαβ hsupp h0 hblind hc'_0 hc'_half hc_lo hc'_hi
  have h_sin : Real.sin (2 * π * (1 / 2 - c)) = Real.sin (2 * π * c) := by
    rw [show 2 * π * (1 / 2 - c) = π - 2 * π * c by ring, Real.sin_pi_sub]
  rw [h_sin] at hUnfold
  rw [hUnfold]
  have h1 : (1 : ℝ) - (1 / 2 - c) = 1 / 2 + c := by ring
  have h2 : (1 : ℝ) + (1 / 2 - c) = 3 / 2 - c := by ring
  have h3 : (2 : ℝ) - (1 / 2 - c) = 3 / 2 + c := by ring
  have h4 : (2 : ℝ) + (1 / 2 - c) = 5 / 2 - c := by ring
  rw [h1, h2, h3, h4]

/-- **Four-collar annihilation law for blind cores.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0` and any
`c ∈ [0, 1/4]` satisfying `1/2 - c ≤ α / β` and `β / α ≤ 5/2 + c`,
`(∫ r in (1/2 + c)..(1 - c), A_f(r) dr) + (∫ r in (1 + c)..(3/2 - c), A_f(r) dr) + (∫ r in (3/2 + c)..(2 - c), A_f(r) dr) + (∫ r in (2 + c)..(5/2 - c), A_f(r) dr) = 0`. -/
theorem dilationAutocorr_four_collar_sum_eq_zero
    (hf : Continuous f) {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hc0 : 0 ≤ c) (hc_quarter : c ≤ 1 / 4)
    (hc_lo : 1 / 2 - c ≤ α / β) (hc_hi : β / α ≤ 5 / 2 + c) :
    (∫ r in (1 / 2 + c)..(1 - c), dilationAutocorr f r) +
      (∫ r in (1 + c)..(3 / 2 - c), dilationAutocorr f r) +
      (∫ r in (3 / 2 + c)..(2 - c), dilationAutocorr f r) +
      (∫ r in (2 + c)..(5 / 2 - c), dilationAutocorr f r) = 0 := by
  have h1 := cosDilationKernel_one_mul_sin_div_pi_eq_intervalIntegral
    hf hα hαβ hsupp h0 hblind hc0 (by linarith) (by linarith) (by linarith)
  have h2 := cosDilationKernel_one_mul_sin_div_pi_eq_half_sub_intervalIntegral
    hf hα hαβ hsupp h0 hblind hc0 hc_quarter hc_lo hc_hi
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have h_split1a := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) (1 / 2 + c) (1 - c))
    (hA_cont.intervalIntegrable (μ := volume) (1 - c) (1 + c))
  have h_split1b := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) (1 / 2 + c) (1 + c))
    (hA_cont.intervalIntegrable (μ := volume) (1 + c) (3 / 2 - c))
  have h_split2a := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) (3 / 2 + c) (2 - c))
    (hA_cont.intervalIntegrable (μ := volume) (2 - c) (2 + c))
  have h_split2b := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) (3 / 2 + c) (2 + c))
    (hA_cont.intervalIntegrable (μ := volume) (2 + c) (5 / 2 - c))
  linarith

/-- **Three-collar annihilation law when `β / α ≤ 2 + c`.**
If in addition `β / α ≤ 2 + c`, the fourth collar `[2 + c, 5/2 - c]` lies outside `(α/β, β/α)`
and vanishes identically, leaving
`(∫ r in (1/2 + c)..(1 - c), A_f(r) dr) + (∫ r in (1 + c)..(3/2 - c), A_f(r) dr) + (∫ r in (3/2 + c)..(2 - c), A_f(r) dr) = 0`. -/
theorem dilationAutocorr_three_collar_sum_eq_zero_of_le_two_add
    (hf : Continuous f) {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hc0 : 0 ≤ c) (hc_quarter : c ≤ 1 / 4)
    (hc_lo : 1 / 2 - c ≤ α / β) (hc_hi : β / α ≤ 2 + c) :
    (∫ r in (1 / 2 + c)..(1 - c), dilationAutocorr f r) +
      (∫ r in (1 + c)..(3 / 2 - c), dilationAutocorr f r) +
      (∫ r in (3 / 2 + c)..(2 - c), dilationAutocorr f r) = 0 := by
  have h4 := dilationAutocorr_four_collar_sum_eq_zero
    hf hα hαβ hsupp h0 hblind hc0 hc_quarter hc_lo (by linarith)
  have h_fourth_zero : ∫ r in (2 + c)..(5 / 2 - c), dilationAutocorr f r = 0 := by
    have h_zero : ∀ r ∈ uIcc (2 + c) (5 / 2 - c), dilationAutocorr f r = 0 := by
      intro r hr
      rw [uIcc_of_le (by linarith)] at hr
      refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun hmem => ?_
      linarith [hmem.2, hr.1]
    rw [intervalIntegral.integral_congr h_zero, intervalIntegral.integral_zero]
  linarith

/-! ### Specializations at `c = 1/6` and the support-adapted parameter `c = β / α - 2` -/

/-- **Sixth/third-period four-collar annihilation (`c = 1/6`, `β ≤ (8/3) α`).** -/
theorem dilationAutocorr_sixth_third_four_collar_eq_zero
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 8 / 3 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    (∫ r in (2 / 3 : ℝ)..(5 / 6), dilationAutocorr f r) +
      (∫ r in (7 / 6 : ℝ)..(4 / 3), dilationAutocorr f r) +
      (∫ r in (5 / 3 : ℝ)..(11 / 6), dilationAutocorr f r) +
      (∫ r in (13 / 6 : ℝ)..(7 / 3), dilationAutocorr f r) = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 8 / 3 := (div_le_iff₀ hα).mpr hβ
  have hlo : 3 / 8 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have h := dilationAutocorr_four_collar_sum_eq_zero (c := 1 / 6)
    hf hα hαβ hsupp h0 hblind (by norm_num) (by norm_num) (by linarith) (by linarith)
  norm_num at h
  exact h

/-- **Sixth/third-period three-collar annihilation (`c = 1/6`, `β ≤ (13/6) α`).** -/
theorem dilationAutocorr_sixth_third_three_collar_eq_zero
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 13 / 6 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    (∫ r in (2 / 3 : ℝ)..(5 / 6), dilationAutocorr f r) +
      (∫ r in (7 / 6 : ℝ)..(4 / 3), dilationAutocorr f r) +
      (∫ r in (5 / 3 : ℝ)..(11 / 6), dilationAutocorr f r) = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 13 / 6 := (div_le_iff₀ hα).mpr hβ
  have hlo : 6 / 13 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have h := dilationAutocorr_three_collar_sum_eq_zero_of_le_two_add (c := 1 / 6)
    hf hα hαβ hsupp h0 hblind (by norm_num) (by norm_num) (by linarith) (by linarith)
  norm_num at h
  exact h

/-- **Support-adapted three-collar annihilation for `2α ≤ β ≤ (9/4)α`.**
Setting `c = β / α - 2 ∈ [0, 1/4]` automatically satisfies `1/2 - c ≤ α / β` because
`(β - 2α)(2β - α) ≥ 0`, and makes `2 + c = β / α`, so
`(∫ r in (β/α - 3/2)..(3 - β/α), A_f(r) dr) + (∫ r in (β/α - 1)..(7/2 - β/α), A_f(r) dr) + (∫ r in (β/α - 1/2)..(4 - β/α), A_f(r) dr) = 0`. -/
theorem dilationAutocorr_support_adapted_three_collar_eq_zero
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hβ_lo : 2 * α ≤ β) (hβ_hi : β ≤ 9 / 4 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    (∫ r in (β / α - 3 / 2)..(3 - β / α), dilationAutocorr f r) +
      (∫ r in (β / α - 1)..(7 / 2 - β / α), dilationAutocorr f r) +
      (∫ r in (β / α - 1 / 2)..(4 - β / α), dilationAutocorr f r) = 0 := by
  have hαβ : α ≤ β := by linarith
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hc0 : 0 ≤ β / α - 2 := by
    have : 2 ≤ β / α := (le_div_iff₀ hα).mpr hβ_lo
    linarith
  have hc_quarter : β / α - 2 ≤ 1 / 4 := by
    have : β / α ≤ 9 / 4 := (div_le_iff₀ hα).mpr hβ_hi
    linarith
  have hc_lo : 1 / 2 - (β / α - 2) ≤ α / β := by
    rw [le_div_iff₀ hβ0]
    have h_quad : 0 ≤ (β - 2 * α) * (2 * β - α) :=
      mul_nonneg (by linarith) (by linarith)
    have h_div : (5 / 2 - β / α) * β = 5 / 2 * β - β ^ 2 / α := by ring
    have h_ineq : (5 / 2 - β / α) * β * α ≤ α * α := by
      have h_eq : (5 / 2 - β / α) * β * α = 5 / 2 * α * β - β * (β / α * α) := by ring
      rw [h_eq, div_mul_cancel₀ β hα.ne']
      linarith
    exact le_of_mul_le_mul_right (by linarith) hα
  have h := dilationAutocorr_three_collar_sum_eq_zero_of_le_two_add (c := β / α - 2)
    hf hα hαβ hsupp h0 hblind hc0 hc_quarter hc_lo (by linarith)
  have e1 : (1 / 2 : ℝ) + (β / α - 2) = β / α - 3 / 2 := by ring
  have e2 : (1 : ℝ) - (β / α - 2) = 3 - β / α := by ring
  have e3 : (1 : ℝ) + (β / α - 2) = β / α - 1 := by ring
  have e4 : (3 / 2 : ℝ) - (β / α - 2) = 7 / 2 - β / α := by ring
  have e5 : (3 / 2 : ℝ) + (β / α - 2) = β / α - 1 / 2 := by ring
  have e6 : (2 : ℝ) - (β / α - 2) = 4 - β / α := by ring
  rw [e1, e2, e3, e4, e5, e6] at h
  exact h

/-! ### Inversion-folded right-half-line window identity -/

/-- **Inversion-folded right-half-line window identity.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `c ∈ [0, 1/2]` satisfying `c ≤ α / β` and `β / α ≤ 3 - c`,
`Ψ_f(1) * sin(2π c) / π + (1 - c) * A_{logPrimCore f}(1 - c) = (∫ r in 0..(1 + c), A_f(r) dr) + (1 - c) * (∫ r in 0..(1 - c)⁻¹, A_f(r) dr) + (∫ r in (2 - c)..(2 + c), A_f(r) dr)`. -/
theorem cosDilationKernel_one_mul_sin_div_pi_add_logPrimCore_eq
    (hf : Continuous f) {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hc0 : 0 ≤ c) (hc_half : c ≤ 1 / 2) (hc_lo : c ≤ α / β) (hc_hi : β / α ≤ 3 - c) :
    cosDilationKernel f 1 * Real.sin (2 * π * c) / π +
        (1 - c) * dilationAutocorr (logPrimCore f) (1 - c) =
      (∫ r in (0 : ℝ)..(1 + c), dilationAutocorr f r) +
        (1 - c) * (∫ r in (0 : ℝ)..(1 - c)⁻¹, dilationAutocorr f r) +
        (∫ r in (2 - c)..(2 + c), dilationAutocorr f r) := by
  have h0 : cosDilationKernel f 0 = 0 := cosDilationKernel_zero_of_integral_eq_zero hmean
  have hUnfold := cosDilationKernel_one_mul_sin_div_pi_eq_intervalIntegral
    hf hα hαβ hsupp h0 hblind hc0 hc_half hc_lo hc_hi
  have h1mc_pos : 0 < 1 - c := by linarith
  have hDual := intervalIntegral_dilationAutocorr_add_inv_eq
    hf hα hαβ hsupp hmean h1mc_pos
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have h_split := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) 0 (1 - c))
    (hA_cont.intervalIntegrable (μ := volume) (1 - c) (1 + c))
  linarith

end

end RHTower
