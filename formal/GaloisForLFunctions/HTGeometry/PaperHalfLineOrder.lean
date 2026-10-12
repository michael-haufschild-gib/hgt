import GaloisForLFunctions.HTGeometry.PaperHalfLineSpectrum
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # Exact order of full continuous half-line multiplication

Positivity, even after arbitrary compact correction, is exactly pointwise
positivity of the full real symbol on the physical half-line.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Set

private abbrev H := Lp ℂ 2 halfLineMeasure

variable {ψ : ℝ → ℝ} (hψ : Continuous ψ) {C : ℝ}
  (hC : 0 ≤ C) (hbound : ∀ x, ‖(ψ x : ℂ)‖ ≤ C)

theorem paperHalfLineRealMul_selfAdjoint : IsSelfAdjoint
    (lpBoundedMulCLM (p := 2) (μ := halfLineMeasure)
      (Complex.continuous_ofReal.comp hψ).measurable hC hbound) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact lpBoundedMulCLM_inner_general _ _ _ (fun x => by simp)

theorem paperHalfLineRealMul_positive_iff :
    (lpBoundedMulCLM (p := 2) (μ := halfLineMeasure)
      (Complex.continuous_ofReal.comp hψ).measurable hC hbound).IsPositive ↔
        ∀ x ≥ 0, 0 ≤ ψ x := by
  let A : H →L[ℂ] H := lpBoundedMulCLM
    (Complex.continuous_ofReal.comp hψ).measurable hC hbound
  have hA (f : H) : (A f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (ψ x : ℂ) * f x :=
    lpBoundedMulCLM_coeFn _ _ _ f
  change A.IsPositive ↔ _
  constructor
  · intro hp x hx
    have hz := paperHalfLine_nonneg_value_mem_spectrum
      (Complex.continuous_ofReal.comp hψ) hA hx
    have hzR : ψ x ∈ spectrum ℝ A := spectrum.of_algebraMap_mem ℂ hz
    exact SpectrumRestricts.nnreal_iff.mp hp.spectrumRestricts (ψ x) hzR
  · intro hp
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨paperHalfLineRealMul_selfAdjoint hψ hC hbound, fun f => ?_⟩
    change 0 ≤ (inner ℂ (A f) f).re
    rw [L2.inner_def, ← RCLike.re_eq_complex_re,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) (A f) f)]
    apply integral_nonneg_of_ae
    filter_upwards [hA f, ae_restrict_mem measurableSet_Ici] with x hx hpos
    rw [hx]
    simp only [RCLike.re_eq_complex_re]
    rw [RCLike.inner_apply', map_mul, Complex.conj_ofReal, mul_assoc,
      ← Complex.normSq_eq_conj_mul_self]
    simpa using mul_nonneg (hp x hpos) (Complex.normSq_nonneg (f x))

theorem paperHalfLineRealMul_compact_positive_iff :
    (∃ K : compactOperatorStarAlgebra H,
      (lpBoundedMulCLM (p := 2) (μ := halfLineMeasure)
        (Complex.continuous_ofReal.comp hψ).measurable hC hbound + K.1).IsPositive) ↔
          ∀ x ≥ 0, 0 ≤ ψ x := by
  rw [paperHalfLine_exists_compact_positive_iff
    (lpBoundedMulCLM_coeFn _ _ _) (paperHalfLineRealMul_selfAdjoint hψ hC hbound),
    paperHalfLineRealMul_positive_iff hψ hC hbound]

end
end GaloisForLFunctions.HTGeometry
