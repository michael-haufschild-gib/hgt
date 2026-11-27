import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Gaussian domination of Lebesgue occupation on a finite time record -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

private theorem density_on_unit_interval {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    1/8 ≤ gaussianPDFReal 0 1 x := by
  have hs : √(2*π) ≤ 4 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith only [pi_lt_four]⟩
  have hinv : 1/4 ≤ (√(2*π))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hs
  have hx' := (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr (abs_le.mpr hx)
  rw [sq_abs] at hx'
  have he : 1/2 ≤ exp (-x^2/2) := by
    linarith only [hx',Real.add_one_le_exp (-x^2/2)]
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one,mul_one,sub_zero]
  exact (show (1/8:ℝ)=1/4*(1/2) by norm_num).le.trans
    (mul_le_mul hinv he (by norm_num) (by positivity))

/-- Standard Gaussian observation at scale T dominates physical duration
on [-T,T], with a constant independent of T and of the recorded event. -/
theorem volume_window_le_gaussian {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hs : MeasurableSet S)
    (hsub : S ⊆ Icc (-T) T) :
    volume.real S ≤ 8*T*(gaussianReal 0 1).real ((T * ·) ⁻¹' S) := by
  let A := (T * ·) ⁻¹' S
  have hA : MeasurableSet A := hs.preimage (measurable_const.mul measurable_id)
  have hb : A ⊆ Icc (-1:ℝ) 1 := by
    intro x hx
    obtain ⟨hl,hr⟩ := hsub hx
    exact ⟨(le_of_mul_le_mul_left (by simpa only [mul_neg_one] using hl) hT),
      le_of_mul_le_mul_left (by simpa only [mul_one] using hr) hT⟩
  have hfin : volume A ≠ ⊤ := ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hb)
  have hi := setIntegral_mono_on (integrableOn_const hfin : IntegrableOn (fun _ : ℝ => (1/8:ℝ)) A)
    (integrable_gaussianPDFReal 0 1).integrableOn hA (fun x hx => density_on_unit_interval (hb hx))
  rw [setIntegral_const,smul_eq_mul] at hi
  have he : (gaussianReal 0 1).real A=∫ x in A, gaussianPDFReal 0 1 x := by
    rw [Measure.real,gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg hA (fun x _ => gaussianPDFReal_nonneg 0 1 x))]
  have hscale : volume.real A=T⁻¹*volume.real S := by
    rw [Measure.real,Real.volume_preimage_mul_left hT.ne',ENNReal.toReal_mul,abs_of_pos (inv_pos.mpr hT),
      ENNReal.toReal_ofReal (inv_nonneg.mpr hT.le)]
    rfl
  change volume.real S ≤ 8*T*(gaussianReal 0 1).real A
  have h := mul_le_mul_of_nonneg_left (show volume.real A ≤ 8*(gaussianReal 0 1).real A by
    rw [he]; linarith only [hi]) hT.le
  rw [hscale,←mul_assoc,mul_inv_cancel₀ hT.ne',one_mul] at h
  linarith only [h]

#print axioms volume_window_le_gaussian
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
