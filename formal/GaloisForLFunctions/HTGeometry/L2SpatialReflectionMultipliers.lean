import GaloisForLFunctions.HTGeometry.KleinGordonFieldMild
import GaloisForLFunctions.RHTower.L2FourierReflection

/-! Spatial reflection of bounded multipliers and the genuine Klein–Gordon propagator. -/
open MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section

private theorem reflection_ae (f : FourierRealL2) :
    l2Reflection f =ᵐ[volume] (fun x : ℝ => f (-x)) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- Even spatial multipliers commute with the actual L² reflection. -/
theorem lpBoundedMulCLM_reflection {φ : ℝ → ℂ} (hφ : Measurable φ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ x, ‖φ x‖ ≤ C) (he : ∀ x, φ (-x) = φ x) (f : FourierRealL2) :
    lpBoundedMulCLM hφ hC hb (l2Reflection f) = l2Reflection (lpBoundedMulCLM hφ hC hb f) := by
  apply Lp.ext
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (lpBoundedMulCLM_coeFn (p := 2) (μ := volume) hφ hC hb f)
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) hφ hC hb (l2Reflection f),
    reflection_ae (lpBoundedMulCLM hφ hC hb f),reflection_ae f,hn] with x hl hr hf hn
  rw [hl,hr,hf,hn,he]

/-- The corpus Fourier operator respects spatial reflection with its original normalization. -/
theorem fourierL2_reflection (f : FourierRealL2) :
    fourierL2 ℝ (l2Reflection f) = l2Reflection (fourierL2 ℝ f) := l2_fourier_reflection f

/-- Inverse Fourier synthesis respects the same spatial reflection. -/
theorem fourierL2inv_reflection (f : FourierRealL2) :
    fourierL2inv ℝ (l2Reflection f) = l2Reflection (fourierL2inv ℝ f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change fourierL2 ℝ (fourierL2inv ℝ (l2Reflection f)) =
    fourierL2 ℝ (l2Reflection (fourierL2inv ℝ f))
  rw [fourierL2_reflection,fourierL2_fourierL2inv,fourierL2_fourierL2inv]

/-- Every bounded even Fourier symbol preserves the exact odd spatial subspace. -/
theorem fourierMulCLM_reflection {φ : ℝ → ℂ} (hφ : Measurable φ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ x, ‖φ x‖ ≤ C) (he : ∀ x, φ (-x) = φ x) (f : FourierRealL2) :
    fourierMulCLM hφ hC hb (l2Reflection f) = l2Reflection (fourierMulCLM hφ hC hb f) := by
  rw [fourierMulCLM_apply,fourierL2_reflection,lpBoundedMulCLM_reflection hφ C hC hb he,
    fourierL2inv_reflection]
  rfl

/-- The actual half-order sine propagator preserves spatial oddness. -/
theorem kgSinFreqOp_reflection (t : ℝ) (f : FourierRealL2) :
    kgSinFreqOp t (l2Reflection f) = l2Reflection (kgSinFreqOp t f) := by
  rw [kgSinFreqOp_eq]
  apply fourierMulCLM_reflection
  intro x
  simp [kgSinOverFreq,kgFreq]

end
end GaloisForLFunctions.HTGeometry
