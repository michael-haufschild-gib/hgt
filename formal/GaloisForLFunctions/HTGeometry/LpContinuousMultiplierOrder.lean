import GaloisForLFunctions.HTGeometry.ContinuousLpMultiplierSpectrum
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # The exact order of a continuous real multiplication symbol -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

private abbrev H := Lp ℂ 2 (volume : Measure ℝ)

variable {ψ : ℝ → ℝ} (hψ : Continuous ψ) {C : ℝ}
  (hC : 0 ≤ C) (hbound : ∀ x, ‖(ψ x : ℂ)‖ ≤ C)

theorem lpBoundedRealMul_selfAdjoint : IsSelfAdjoint
    (lpBoundedMulCLM (p := 2) (μ := volume)
      (Complex.continuous_ofReal.comp hψ).measurable hC hbound) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact lpBoundedMulCLM_inner_general _ _ _ (fun x => by simp)

theorem lpBoundedRealMul_positive_iff :
    (lpBoundedMulCLM (p := 2) (μ := volume)
      (Complex.continuous_ofReal.comp hψ).measurable hC hbound).IsPositive ↔
        ∀ x, 0 ≤ ψ x := by
  let T : H →L[ℂ] H := lpBoundedMulCLM
    (Complex.continuous_ofReal.comp hψ).measurable hC hbound
  have hT (f : H) : (T f : ℝ → ℂ) =ᵐ[volume] fun x => (ψ x : ℂ) * f x :=
    lpBoundedMulCLM_coeFn _ _ _ f
  change T.IsPositive ↔ _
  constructor
  · intro hp x
    have hx := value_mem_spectrum_of_ae_mul_continuous
      (Complex.continuous_ofReal.comp hψ) hT x
    have hxR : ψ x ∈ spectrum ℝ T := spectrum.of_algebraMap_mem ℂ hx
    exact SpectrumRestricts.nnreal_iff.mp hp.spectrumRestricts (ψ x) hxR
  · intro hp
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨lpBoundedRealMul_selfAdjoint hψ hC hbound, fun f => ?_⟩
    change 0 ≤ (inner ℂ (T f) f).re
    rw [L2.inner_def, ← RCLike.re_eq_complex_re,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) (T f) f)]
    apply integral_nonneg_of_ae
    filter_upwards [hT f] with x hx
    rw [hx]
    simp only [RCLike.re_eq_complex_re]
    rw [RCLike.inner_apply', map_mul, Complex.conj_ofReal, mul_assoc,
      ← Complex.normSq_eq_conj_mul_self]
    simpa using mul_nonneg (hp x) (Complex.normSq_nonneg (f x))

end
end GaloisForLFunctions.HTGeometry
