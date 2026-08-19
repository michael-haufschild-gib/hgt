import GaloisForLFunctions.HTGeometry.ArchimedeanPowerIndependence

/-!
# `log t` and the descending powers are independent at every order

`three_term_expansion_eq_zero` handles the scales `1, log t, 1/t` modulo `O(t^{-2})`.  Reading a
ladder of arbitrary length needs the same statement with `M` descending powers instead of one, and
that is what this module supplies: `log t` is unbounded while every power term is bounded on
`t ≥ 1`, so the logarithmic coefficient dies first, and `power_expansion_eq_zero` finishes.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- **The logarithm and the descending powers are independent modulo the next power.** -/
theorem log_power_expansion_eq_zero (M : ℕ) (b : ℂ) (a : ℕ → ℂ) (K R : ℝ)
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ‖b * ((Real.log t : ℝ) : ℂ) + ∑ m ∈ Finset.range (M + 1), a m / (((t : ℝ) : ℂ)) ^ m‖
        ≤ K / t ^ (M + 1)) :
    b = 0 ∧ ∀ m ∈ Finset.range (M + 1), a m = 0 := by
  have hK0 : 0 ≤ K := by
    set t0 : ℝ := max R 1 with ht0def
    have ht01 : (1 : ℝ) ≤ t0 := le_max_right _ _
    have hpos : (0 : ℝ) < t0 ^ (M + 1) := by positivity
    have hb := h t0 (le_max_left _ _) ht01
    have hnn := norm_nonneg
      (b * ((Real.log t0 : ℝ) : ℂ) + ∑ m ∈ Finset.range (M + 1), a m / (((t0 : ℝ) : ℂ)) ^ m)
    have hle : (0 : ℝ) ≤ K / t0 ^ (M + 1) := le_trans hnn hb
    rw [le_div_iff₀ hpos] at hle
    linarith
  set S : ℝ := ∑ m ∈ Finset.range (M + 1), ‖a m‖ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the power part is bounded on `t ≥ 1`
  have hpow : ∀ t : ℝ, 1 ≤ t →
      ‖∑ m ∈ Finset.range (M + 1), a m / (((t : ℝ) : ℂ)) ^ m‖ ≤ S := by
    intro t ht1
    have ht0 : (0 : ℝ) < t := by linarith
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun m _ => ?_
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hpm : (1 : ℝ) ≤ t ^ m := one_le_pow₀ ht1
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (a m)]
  -- the logarithmic coefficient is bounded, hence zero
  have hbound : ∀ t : ℝ, R ≤ t → 1 ≤ t → ‖b‖ * Real.log t ≤ K + S := by
    intro t hR ht1
    have ht0 : (0 : ℝ) < t := by linarith
    have hbt : ‖b * ((Real.log t : ℝ) : ℂ)‖ = ‖b‖ * Real.log t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1)]
    have hid : b * ((Real.log t : ℝ) : ℂ)
        = (b * ((Real.log t : ℝ) : ℂ)
            + ∑ m ∈ Finset.range (M + 1), a m / (((t : ℝ) : ℂ)) ^ m)
          - ∑ m ∈ Finset.range (M + 1), a m / (((t : ℝ) : ℂ)) ^ m := by ring
    have hstep := norm_sub_le
      (b * ((Real.log t : ℝ) : ℂ)
        + ∑ m ∈ Finset.range (M + 1), a m / (((t : ℝ) : ℂ)) ^ m)
      (∑ m ∈ Finset.range (M + 1), a m / (((t : ℝ) : ℂ)) ^ m)
    rw [← hid] at hstep
    rw [hbt] at hstep
    have hKt : K / t ^ (M + 1) ≤ K := by
      have hpm : (1 : ℝ) ≤ t ^ (M + 1) := one_le_pow₀ ht1
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hK0]
    linarith [h t hR ht1, hpow t ht1, hstep, hKt]
  have hb0 : b = 0 := by
    by_contra hb
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    set t : ℝ := max (max R 1) (Real.exp ((K + S + 1) / ‖b‖)) with htdef
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right R 1) (le_max_left _ _)
    have htR : R ≤ t := le_trans (le_max_left R 1) (le_max_left _ _)
    have ht0 : (0 : ℝ) < t := by linarith
    have hlogt : (K + S + 1) / ‖b‖ ≤ Real.log t :=
      (Real.le_log_iff_exp_le ht0).mpr (le_max_right _ _)
    rw [div_le_iff₀ hbpos] at hlogt
    linarith [hbound t htR ht1]
  refine ⟨hb0, ?_⟩
  refine power_expansion_eq_zero M a K R fun t hR ht1 => ?_
  have := h t hR ht1
  rw [hb0] at this
  simpa using this

end

end GaloisForLFunctions.HTGeometry
