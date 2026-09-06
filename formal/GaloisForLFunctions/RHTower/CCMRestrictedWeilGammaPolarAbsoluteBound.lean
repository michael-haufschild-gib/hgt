import GaloisForLFunctions.RHTower.CCMRestrictedWeilGammaPolarBoundary

/-!
# Absolute mass of the pole-profile Gamma jump

The negative part of the exact positive-pole jump is confined to the forward
endpoint interval and bounded there by one. Combining that lower bound with the
already evaluated signed integral controls the absolute mass by the universal
core mass, the forward distance, and the two logarithmic boundary tails.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower
private theorem base_jump_ge_neg_one {h : ℝ} (hh : 0 < h) :
    -1 ≤ ccmGammaTranslationDensity h *
      (2 - Real.exp (h/2) - Real.exp (-(h/2))) := by
  let t := Real.exp (-(h/2))
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hepos : Real.exp (h/2) = t⁻¹ := by
    dsimp [t]
    rw [← Real.exp_neg]
    congr 1
    ring
  have he4 : Real.exp (-(2*h)) = t ^ 4 := by
    dsimp [t]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hden : 0 < (1+t)*(1+t^2) := by positivity
  have hneq : 1-t^4 ≠ 0 := by
    have hlt : t^4 < 1 := by nlinarith [sq_nonneg (t^2), mul_pos ht (sub_pos.mpr ht1)]
    linarith
  have hid : ccmGammaTranslationDensity h * (2 - Real.exp (h/2) - Real.exp (-(h/2))) =
      -(1-t)/((1+t)*(1+t^2)) := by
    unfold ccmGammaTranslationDensity
    rw [hepos, he4]
    change t/(1-t^4)*(2-t⁻¹-t) = _
    field_simp
    ring
  rw [hid]
  apply (le_div_iff₀ hden).mpr
  nlinarith [sq_nonneg t, mul_nonneg ht.le (sq_nonneg t)]

/-- Only the forward endpoint interval can carry a negative pole jump, with magnitude at most one. -/
theorem ccmGammaPolarJumpKernel_lower_bound (R L : ℝ) {h : ℝ} (hh : 0 < h) :
    -(Ioc (0:ℝ) R).indicator (fun _ => (1:ℝ)) h ≤ ccmGammaPolarJumpKernel R L h := by
  have hρ := (ccmGammaTranslationDensity_pos hh).le
  have hm : Real.exp (-(h/2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  by_cases hR : h ≤ R
  · rw [indicator_of_mem (show h ∈ Ioc (0:ℝ) R from ⟨hh,hR⟩)]
    have hb := base_jump_ge_neg_one hh
    unfold ccmGammaPolarJumpKernel
    by_cases hL : h ≤ L
    · simpa only [hR, hL, if_true] using hb
    · simp only [hR, hL, if_true, if_false, sub_zero]
      nlinarith [Real.exp_pos (-(h/2))]
  · rw [indicator_of_notMem (show h ∉ Ioc (0:ℝ) R from fun hx => hR hx.2), neg_zero]
    unfold ccmGammaPolarJumpKernel
    by_cases hL : h ≤ L
    · simp only [hR, hL, if_false, if_true, sub_zero]
      exact mul_nonneg hρ (by linarith)
    · simp only [hR, hL, if_false, sub_zero]
      positivity

/-- Absolute jump mass has an explicit endpoint bound, with no cancellation hidden in the norm. -/
theorem integral_abs_ccmGammaPolarJumpKernel_le {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    (∫ h in Ioi (0:ℝ), |ccmGammaPolarJumpKernel R L h|) ≤
      -(Complex.digamma ((1/4:ℝ):ℂ)).re - Real.eulerMascheroniConstant - Real.log 2 + R +
        ccmGammaPolarBoundary R L := by
  let q : ℝ → ℝ := (Ioc (0:ℝ) R).indicator (fun _ => (1:ℝ))
  have hqi : IntegrableOn q (Ioi (0:ℝ)) := by
    rw [integrableOn_indicator_iff measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioi_self)]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  have hqm : (∫ h in Ioi (0:ℝ), q h) = R := by
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr Ioc_subset_Ioi_self]
    simp [hR.le]
  have hj := integrableOn_ccmGammaPolarJumpKernel hR hL
  have hle : (∫ h in Ioi (0:ℝ), |ccmGammaPolarJumpKernel R L h|) ≤
      ∫ h in Ioi (0:ℝ), (ccmGammaPolarJumpKernel R L h + 2*q h) := by
    apply integral_mono_ae hj.abs (hj.add (hqi.const_mul 2))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hb := ccmGammaPolarJumpKernel_lower_bound R L hh
    have hq : 0 ≤ q h := indicator_nonneg (fun _ _ => by norm_num) _
    change -(q h) ≤ ccmGammaPolarJumpKernel R L h at hb
    change |ccmGammaPolarJumpKernel R L h| ≤ ccmGammaPolarJumpKernel R L h + 2*q h
    apply abs_le.mpr
    constructor <;> linarith
  have ha := integral_add hj (hqi.const_mul 2)
  rw [ha, integral_const_mul, hqm, integral_ccmGammaPolarJumpKernel hR hL] at hle
  norm_num at hle ⊢
  linarith
end RHTower
