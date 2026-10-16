import GaloisForLFunctions.RHTower.PaperThetaCutFactorLefschetz
import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionWeilTrace
import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionFredholm

/-! # Whole-source convolution fixed by native theta current factors

The native cut factors determine the unique bounded extension of every
original source convolution. That extension is trace class, and its
complete resonant blocks admit the unconditional Fredholm repair.
-/

noncomputable section
open Complex MeasureTheory ContinuousLinearMap

namespace RHTower.PaperThetaEndpoint

theorem cutFactorHilbert_convolution_existsUnique (g : DeningerMeyerStrongLogTarget) :
    ∃! T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert,
      ∀ q, T (deningerMeyerHasseHilbertLM (cutFactorClass q)) =
        deningerMeyerHasseHilbertLM
          (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) (cutFactorClass q)) := by
  refine ⟨deningerMeyerHilbertConvolution g,
    fun q => deningerMeyerHilbertConvolution_source g _, ?_⟩
  intro T hT
  exact cutFactorHilbert_operator_ext (fun q => (hT q).trans
    (deningerMeyerHilbertConvolution_source g _).symm)

/-- Native factors fix the actual whole-line average, with full source admission discharged. -/
theorem cutFactorHilbert_convolution_integral (g : DeningerMeyerStrongLogTarget)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseHilbertLM
      (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) (cutFactorClass q)) =
      ∫ t : ℝ, g.val t • deningerMeyerHasseHilbertLM
        (deningerMeyerStrongLogCohomologyFlow t (cutFactorClass q)) := by
  rw [← deningerMeyerHilbertConvolution_source, deningerMeyerHilbertConvolution_apply]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerHilbertFlow_source]

/-- Every original source has a uniquely determined native trace operator and a bounded repair. -/
theorem cutFactorHilbert_convolution_trace_repair (g : DeningerMeyerStrongLogTarget) :
    (∃! T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert,
      (∀ q, T (deningerMeyerHasseHilbertLM (cutFactorClass q)) =
        deningerMeyerHasseHilbertLM
          (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) (cutFactorClass q))) ∧
      MemSchattenClass 1 T) ∧
    (∀ f : DeningerArithmeticJetHilbert,
      ∃! x, deningerMeyerConvolutionFredholmRepair g x = f) := by
  constructor
  · refine ⟨deningerMeyerHilbertConvolution g,
      ⟨fun q => deningerMeyerHilbertConvolution_source g _,
        deningerMeyerHilbertConvolution_memSchattenClass_one g⟩, ?_⟩
    intro T hT
    exact (cutFactorHilbert_convolution_existsUnique g).unique hT.1
      (fun q => deningerMeyerHilbertConvolution_source g _)
  · exact deningerMeyerConvolutionFredholm_existsUnique g

end RHTower.PaperThetaEndpoint
