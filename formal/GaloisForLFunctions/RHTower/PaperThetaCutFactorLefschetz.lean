import GaloisForLFunctions.RHTower.DeningerMeyerFlowLefschetz
import GaloisForLFunctions.RHTower.PaperThetaCutHasseCompletion

/-! # Native theta cut factors determine the actual arithmetic flow trace

The literal factors of the RN cut-current identity determine the full Meyer
flow and every compact smooth time average. The latter has an unconditional
trace-class realization with the complete prime/Gamma Lefschetz formula.
The construction retains all Hasse slots; totality of native factors supplies
uniqueness on the entire Hilbert carrier.
-/

noncomputable section
open Complex Set Topology MeasureTheory ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

namespace RHTower.PaperThetaEndpoint

/-- Equality on literal cut-current factors determines a bounded operator. -/
theorem cutFactorHilbert_operator_ext
    {A B : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert}
    (h : ∀ q, A (deningerMeyerHasseHilbertLM (cutFactorClass q)) =
      B (deningerMeyerHasseHilbertLM (cutFactorClass q))) : A = B := by
  have hs : cutFactorHilbertSpan ≤ (A-B).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    change A _ - B _ = 0
    exact sub_eq_zero.mpr (h q)
  apply ContinuousLinearMap.ext
  intro x
  have hz := closure_minimal hs (A-B).isClosed_ker (cutFactorHilbertSpan_dense x)
  change A x - B x = 0 at hz
  exact sub_eq_zero.mp hz

/-- Every original dilation has a unique bounded realization from native current factors. -/
theorem cutFactorHilbert_flow_existsUnique (t : ℝ) :
    ∃! U : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert,
      ∀ q, U (deningerMeyerHasseHilbertLM (cutFactorClass q)) =
        deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyFlow t (cutFactorClass q)) := by
  refine ⟨deningerMeyerHilbertFlow t, fun q => deningerMeyerHilbertFlow_source t _, ?_⟩
  intro U hU
  exact cutFactorHilbert_operator_ext (fun q => (hU q).trans
    (deningerMeyerHilbertFlow_source t (cutFactorClass q)).symm)

/-- Native factors admit a unique compact-time average on the whole source completion. -/
theorem cutFactorHilbert_smoothing_existsUnique (φ : DeningerTimeTestFunction) :
    ∃! T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert,
      ∀ q, T (deningerMeyerHasseHilbertLM (cutFactorClass q)) =
        ∫ t : ℝ, (φ t : ℂ) • deningerMeyerHasseHilbertLM
          (deningerMeyerStrongLogCohomologyFlow t (cutFactorClass q)) := by
  refine ⟨deningerMeyerFlowSmoothing φ, fun q => deningerMeyerFlowSmoothing_source φ _, ?_⟩
  intro T hT
  exact cutFactorHilbert_operator_ext (fun q => (hT q).trans
    (deningerMeyerFlowSmoothing_source φ (cutFactorClass q)).symm)

/-- Unconditional source-native trace realization, fixed by the literal RN current factors. -/
theorem cutFactorHilbert_lefschetz_existsUnique (φ : DeningerTimeTestFunction) :
    ∃! T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert,
      (∀ q, T (deningerMeyerHasseHilbertLM (cutFactorClass q)) =
        ∫ t : ℝ, (φ t : ℂ) • deningerMeyerHasseHilbertLM
          (deningerMeyerStrongLogCohomologyFlow t (cutFactorClass q))) ∧
      MemSchattenClass 1 T ∧
      deningerTimeTestLaplace φ 0 - opTrace T + deningerTimeTestLaplace φ 1 =
        (∑' n : DeningerPrimePowerIndex,
          (deningerPrimePowerWeight n : ℂ)*(φ (deningerPrimePowerTime n) : ℂ)) +
        ∫ t : ℝ, (φ t : ℂ)*deningerArchimedeanLefschetzDensity t := by
  refine ⟨deningerMeyerFlowSmoothing φ,
    ⟨fun q => deningerMeyerFlowSmoothing_source φ _,
      deningerMeyerFlowSmoothing_memSchattenClass_one φ, deningerMeyerSourceFlowLefschetz φ⟩, ?_⟩
  intro T hT
  exact cutFactorHilbert_operator_ext (fun q => (hT.1 q).trans
    (deningerMeyerFlowSmoothing_source φ (cutFactorClass q)).symm)

end RHTower.PaperThetaEndpoint
