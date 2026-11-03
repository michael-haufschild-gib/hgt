import GaloisForLFunctions.ArithmeticCriticalityTheory.FoldedSourceOriginJumpMomentLaw

/-!
# The origin charge of a folded window

For a compact C¹ profile vanishing at zero, the folded source has boundary value
`−2 Φ(0) ∫ M dm`. Compact support supplies every decay bound in the origin law.
A continuous additive correction must pay this exact charge at zero; a correction
strictly above it gives local positivity. Nonzero nonnegative profiles have a
strictly positive charge, so corrections vanishing near zero cannot repair them.
-/

noncomputable section
open MeasureTheory Set Filter Topology RHTower
namespace GaloisForLFunctions.ArithmeticCriticalityTheory

private theorem compact_exp_bound {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C * Real.exp (-(8 * |x|)) := by
  have hc : Continuous (fun x : ℝ => f x * Real.exp (8 * |x|)) :=
    hf.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  have hs : HasCompactSupport (fun x : ℝ => f x * Real.exp (8 * |x|)) :=
    hfc.mul_right
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : |f x| * Real.exp (8 * |x|) ≤ max C 0 := by
    have h := (hC x).trans (le_max_left C 0)
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h
  calc
    |f x| = (|f x| * Real.exp (8 * |x|)) * Real.exp (-(8 * |x|)) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le

private theorem compact_profile_decay {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M)
    (hMc : HasCompactSupport M) :
    ∃ C : ℝ, (∀ y, |M y| ≤ C * Real.exp (-(8 * |y|))) ∧
      (∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) := by
  obtain ⟨C, _, hC⟩ := compact_exp_bound hM.continuous hMc
  obtain ⟨D, _, hD⟩ := compact_exp_bound (hM.continuous_deriv le_rfl) hMc.deriv
  refine ⟨max C D, fun y => (hC y).trans ?_, fun y => (hD y).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- The exact boundary value of a corrected folded source on a compact window. -/
theorem tendsto_corrected_foldedSource_of_compactSupport {M b : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (hMc : HasCompactSupport M) (hM0 : M 0 = 0)
    (hb : ContinuousAt b 0) :
    Tendsto (fun x => foldedGenerator (fun y => M y / riemannKernelReal y) x + b x -
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x))
      (𝓝[>] 0) (𝓝 (b 0 - 2 * riemannKernelReal 0 * jumpMeasureMoment M)) := by
  obtain ⟨C, hC, hC'⟩ := compact_profile_decay hM hMc
  have h := ((tendsto_foldedSource_div_nhdsGT_zero hM hM0 hC hC').mul
    ((continuous_riemannKernelReal.tendsto 0).mono_left nhdsWithin_le_nhds)).add
    (hb.tendsto.mono_left nhdsWithin_le_nhds)
  have he : -(2 * jumpMeasureMoment M) * riemannKernelReal 0 + b 0 =
      b 0 - 2 * riemannKernelReal 0 * jumpMeasureMoment M := by ring
  rw [he] at h
  refine h.congr fun x => ?_
  rw [div_mul_cancel₀ _ (riemannKernelReal_pos x).ne']
  ring

/-- A continuous correction of a folded supersolution must pay its origin charge. -/
theorem folded_origin_charge_le_correction {M b : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (hMc : HasCompactSupport M) (hM0 : M 0 = 0)
    (hb : ContinuousAt b 0) {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ x ∈ Ioo 0 δ,
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) ≤
        foldedGenerator (fun y => M y / riemannKernelReal y) x + b x) :
    2 * riemannKernelReal 0 * jumpMeasureMoment M ≤ b 0 := by
  have h := tendsto_corrected_foldedSource_of_compactSupport hM hMc hM0 hb
  have hn : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 ≤
      foldedGenerator (fun y => M y / riemannKernelReal y) x + b x -
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    exact sub_nonneg.mpr (hs x hx)
  exact sub_nonneg.mp (ge_of_tendsto h hn)

/-- Strict overpayment of the boundary charge gives a strict local supersolution. -/
theorem exists_origin_window_corrected_foldedSource_pos {M b : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (hMc : HasCompactSupport M) (hM0 : M 0 = 0)
    (hb : ContinuousAt b 0)
    (hpay : 2 * riemannKernelReal 0 * jumpMeasureMoment M < b 0) :
    ∃ δ > 0, ∀ x ∈ Ioo 0 δ,
      riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) <
        foldedGenerator (fun y => M y / riemannKernelReal y) x + b x := by
  have h := (tendsto_corrected_foldedSource_of_compactSupport hM hMc hM0 hb).eventually
    (lt_mem_nhds (sub_pos.mpr hpay))
  obtain ⟨δ, hδ, hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  exact ⟨δ, hδ, fun x hx => sub_pos.mp (hs hx)⟩

/-- Strict underpayment leaves a strict local subsolution. -/
theorem exists_origin_window_corrected_foldedSource_neg {M b : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (hMc : HasCompactSupport M) (hM0 : M 0 = 0)
    (hb : ContinuousAt b 0)
    (hpay : b 0 < 2 * riemannKernelReal 0 * jumpMeasureMoment M) :
    ∃ δ > 0, ∀ x ∈ Ioo 0 δ,
      foldedGenerator (fun y => M y / riemannKernelReal y) x + b x <
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) := by
  have h := (tendsto_corrected_foldedSource_of_compactSupport hM hMc hM0 hb).eventually
    (gt_mem_nhds (sub_neg.mpr hpay))
  obtain ⟨δ, hδ, hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  exact ⟨δ, hδ, fun x hx => sub_neg.mp (hs hx)⟩

/-- Every nonzero nonnegative compact profile vanishing at zero has positive origin charge. -/
theorem compact_folded_origin_charge_pos {M : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (hMc : HasCompactSupport M) (hM0 : M 0 = 0)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {y₀ : ℝ} (hy₀ : 0 < y₀) (hpos : 0 < M y₀) :
    0 < 2 * riemannKernelReal 0 * jumpMeasureMoment M := by
  obtain ⟨C, _, hC'⟩ := compact_profile_decay hM hMc
  exact mul_pos (mul_pos (by norm_num) (riemannKernelReal_pos 0))
    (jumpMeasureMoment_pos hM hM0 hC' hnn hy₀ hpos)

/-- Corrections with zero origin value cannot repair a positive compact folded profile. -/
theorem compact_positive_profile_origin_failure {M b : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (hMc : HasCompactSupport M) (hM0 : M 0 = 0)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {y₀ : ℝ} (hy₀ : 0 < y₀) (hpos : 0 < M y₀)
    (hb : ContinuousAt b 0) (hb0 : b 0 = 0) :
    ∃ δ > 0, ∀ x ∈ Ioo 0 δ,
      foldedGenerator (fun y => M y / riemannKernelReal y) x + b x <
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) := by
  apply exists_origin_window_corrected_foldedSource_neg hM hMc hM0 hb
  rw [hb0]
  exact compact_folded_origin_charge_pos hM hMc hM0 hnn hy₀ hpos

end GaloisForLFunctions.ArithmeticCriticalityTheory

#print axioms GaloisForLFunctions.ArithmeticCriticalityTheory.tendsto_corrected_foldedSource_of_compactSupport
#print axioms GaloisForLFunctions.ArithmeticCriticalityTheory.folded_origin_charge_le_correction
#print axioms GaloisForLFunctions.ArithmeticCriticalityTheory.exists_origin_window_corrected_foldedSource_pos
#print axioms GaloisForLFunctions.ArithmeticCriticalityTheory.exists_origin_window_corrected_foldedSource_neg
#print axioms GaloisForLFunctions.ArithmeticCriticalityTheory.compact_positive_profile_origin_failure
