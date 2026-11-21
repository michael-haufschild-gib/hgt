import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Logarithmic entropy scale at an occupation boundary

For an occupation of order `t^n`, the singular binary-entropy term
has order `t^n * (-log t)`. The coefficient remains valid when the
scaled occupation tends to zero.
-/

open Set Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

private theorem eventually_small_positive :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 := by
  have h₁ : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, h₁] with t ht hlt
  exact ⟨ht, hlt⟩

theorem tendsto_neg_log_right : Tendsto (fun t : ℝ => -Real.log t) (𝓝[>] 0) atTop :=
  tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

theorem tendsto_inv_neg_log_right :
    Tendsto (fun t : ℝ => (-Real.log t)⁻¹) (𝓝[>] 0) (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_neg_log_right

/-- A derivative at zero gives the right difference-quotient limit. -/
theorem tendsto_right_difference_quotient {f : ℝ → ℝ} {d : ℝ} (h : HasDerivAt f d 0) :
    Tendsto (fun t : ℝ => (f t - f 0) / t) (𝓝[>] 0) (𝓝 d) := by
  have hs : Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ :=
    fun _ ht => mem_compl_singleton_iff.mpr (mem_Ioi.mp ht).ne'
  have hlim := (hasDerivAt_iff_tendsto_slope.mp h).mono_left (nhdsWithin_mono _ hs)
  have he : slope f 0 = fun t : ℝ => (f t - f 0) / t := by
    funext t
    rw [slope_def_field, sub_zero]
  rwa [he] at hlim

/-- A finite right derivative contributes zero on the logarithmic scale. -/
theorem tendsto_right_log_scaled_difference_of_deriv {f : ℝ → ℝ} {d : ℝ}
    (h : HasDerivAt f d 0) :
    Tendsto (fun t : ℝ => (f t - f 0) / (t * -Real.log t)) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => ((f t - f 0) / t) * (-Real.log t)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_right_difference_quotient h).mul tendsto_inv_neg_log_right
  refine hp.congr' ?_
  filter_upwards [eventually_small_positive] with t ht
  have hl : 0 < -Real.log t := neg_pos.mpr (Real.log_neg ht.1 ht.2)
  field_simp [ht.1.ne', hl.ne']

/-- A binary entropy with occupation asymptotic to a multiple of
`t^n` has logarithmic coefficient `n` times that multiple. -/
theorem tendsto_binEntropy_div_pow_mul_neg_log (p : ℝ → ℝ) (n : ℕ) {a : ℝ}
    (hbox : ∀ᶠ t in 𝓝[>] (0 : ℝ), p t ∈ Icc (0 : ℝ) 1)
    (hscale : Tendsto (fun t : ℝ => p t / t ^ n) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => Real.binEntropy (p t) / (t ^ n * -Real.log t))
      (𝓝[>] 0) (𝓝 ((n : ℝ) * a)) := by
  let r (t : ℝ) := p t / t ^ n
  let L (t : ℝ) := -Real.log t
  let R (t : ℝ) := Real.negMulLog (1 - p t) / (t ^ n * L t)
  have hL : Tendsto (fun t : ℝ => (L t)⁻¹) (𝓝[>] 0) (𝓝 0) := tendsto_inv_neg_log_right
  have hRbound (t : ℝ) (ht : 0 < t) (ht₁ : t < 1) (hp : p t ∈ Icc (0 : ℝ) 1) :
      0 ≤ R t ∧ R t ≤ r t * (L t)⁻¹ := by
    have hpow : 0 < t ^ n := pow_pos ht n
    have hl : 0 < L t := neg_pos.mpr (Real.log_neg ht ht₁)
    have hp₀ : 0 ≤ 1 - p t := sub_nonneg.mpr hp.2
    have hp₁ : 1 - p t ≤ 1 := sub_le_self _ hp.1
    constructor
    · exact div_nonneg (Real.negMulLog_nonneg hp₀ hp₁) (mul_pos hpow hl).le
    · have hen := Real.negMulLog_le_one_sub_self hp₀
      rw [sub_sub_cancel] at hen
      calc
        _ ≤ p t / (t ^ n * L t) := div_le_div_of_nonneg_right hen (mul_pos hpow hl).le
        _ = _ := by
          dsimp only [r]
          field_simp [hpow.ne', hl.ne']
  have hR : Tendsto R (𝓝[>] 0) (𝓝 0) := by
    have hup : Tendsto (fun t : ℝ => r t * (L t)⁻¹) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hscale.mul hL
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_small_positive, hbox] with t ht hp
      exact (hRbound t ht.1 ht.2 hp).1
    · filter_upwards [eventually_small_positive, hbox] with t ht hp
      exact (hRbound t ht.1 ht.2 hp).2
  have hlog : Tendsto (fun t : ℝ => Real.negMulLog (r t) * (L t)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => Real.negMulLog (r t)) (𝓝[>] 0)
        (𝓝 (Real.negMulLog a)) :=
      Real.continuous_negMulLog.continuousAt.tendsto.comp hscale
    simpa only [mul_zero] using hc.mul hL
  have hmain : Tendsto (fun t : ℝ => (n : ℝ) * r t + Real.negMulLog (r t) * (L t)⁻¹ + R t)
      (𝓝[>] 0) (𝓝 ((n : ℝ) * a)) := by
    simpa only [add_zero] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (n : ℝ)) (𝓝[>] 0) (𝓝 (n : ℝ))).mul
        hscale).add hlog).add hR
  refine hmain.congr' ?_
  filter_upwards [eventually_small_positive] with t ht
  have hpow : 0 < t ^ n := pow_pos ht.1 n
  have hl : 0 < L t := neg_pos.mpr (Real.log_neg ht.1 ht.2)
  have hr : p t = r t * t ^ n := (div_mul_cancel₀ _ hpow.ne').symm
  have hpLog : Real.negMulLog (t ^ n) = t ^ n * ((n : ℝ) * L t) := by
    unfold Real.negMulLog L
    rw [Real.log_pow]
    ring
  have hsplit : Real.negMulLog (p t) =
      t ^ n * (Real.negMulLog (r t) + (n : ℝ) * r t * L t) := by
    calc
      Real.negMulLog (p t) = Real.negMulLog (r t * t ^ n) := congrArg _ hr
      _ = _ := by rw [Real.negMulLog_mul, hpLog]; ring
  change (n : ℝ) * r t + Real.negMulLog (r t) * (L t)⁻¹ + R t =
    Real.binEntropy (p t) / (t ^ n * L t)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hsplit, add_div]
  change _ + R t = _ + R t
  apply congrArg (fun z : ℝ => z + R t)
  field_simp [hpow.ne', hl.ne']
  ring

/-- A strictly positive logarithmic energy-loss coefficient makes the
ordinary right difference quotient diverge to minus infinity. -/
theorem tendsto_right_slope_atBot_of_log_loss {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun t : ℝ => (f 0 - f t) / (t * -Real.log t)) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => (f t - f 0) / t) (𝓝[>] 0) atBot := by
  have hp := Tendsto.pos_mul_atTop ha h tendsto_neg_log_right
  refine (tendsto_neg_atTop_atBot.comp hp).congr' ?_
  filter_upwards [eventually_small_positive] with t ht
  have hl : Real.log t ≠ 0 := (Real.log_neg ht.1 ht.2).ne
  change -((f 0 - f t) / (t * -Real.log t) * -Real.log t) = (f t - f 0) / t
  field_simp [ht.1.ne', hl]
  ring

#print axioms tendsto_binEntropy_div_pow_mul_neg_log
#print axioms tendsto_right_log_scaled_difference_of_deriv
#print axioms tendsto_right_slope_atBot_of_log_loss

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
