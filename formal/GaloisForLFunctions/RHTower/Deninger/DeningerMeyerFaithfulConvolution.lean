import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionTraceClass

/-! # A faithful trace-class algebra of literal Meyer classes

The first column of each complete Hasse block recovers all original jets.
Global Xi synthesis therefore identifies the operator kernel with the
actual Poisson boundary, before descending the convolution representation.
-/

noncomputable section
open Complex ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem deningerMeyerHilbertConvolution_first_column (g : DeningerMeyerStrongLogTarget)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertConvolution g
      (lp.single 2 ⟨q.1, ⟨0, xiSupportMultiplicity_pos q.1⟩⟩ 1) q =
        deningerMeyerHasseMoment g q.2.val (q.1 : ℂ) := by
  classical
  rw [deningerMeyerHilbertConvolution_jets, Finset.sum_eq_single q.2.val]
  · have he : deningerHasseLower q q.2.val =
        ⟨q.1, ⟨0, xiSupportMultiplicity_pos q.1⟩⟩ := by
      simp [deningerHasseLower]
    rw [he, lp.single_apply_self, mul_one]
  · intro k hk hkj
    have hn : deningerHasseLower q k ≠
        ⟨q.1, ⟨0, xiSupportMultiplicity_pos q.1⟩⟩ := by
      intro he
      have hj := congrArg (fun r : DeningerArithmeticJetCoordinate => r.2.val) he
      change q.2.val-k = 0 at hj
      have hk' := Finset.mem_range.mp hk
      omega
    rw [lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 _ (1 : ℂ) hn,
      mul_zero]
  · simp

/-- Equality of full operators is exactly equality of original cohomology classes. -/
theorem deningerMeyerHilbertConvolution_eq_iff (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution g = deningerMeyerHilbertConvolution h ↔
      (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = Submodule.Quotient.mk h := by
  refine ⟨fun he => ?_, deningerMeyerHilbertConvolution_congr⟩
  apply deningerMeyerHasseHilbertLM_injective
  apply lp.ext
  funext q
  change deningerMeyerHasseMoment g q.2.val q.1 = deningerMeyerHasseMoment h q.2.val q.1
  rw [← deningerMeyerHilbertConvolution_first_column g q,
    ← deningerMeyerHilbertConvolution_first_column h q, he]

def deningerMeyerConvolutionRepresentation (u : DeningerMeyerStrongLogCohomology) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  Quotient.lift deningerMeyerHilbertConvolution
    (fun _ _ h => deningerMeyerHilbertConvolution_congr (Quotient.sound h)) u

@[simp] theorem deningerMeyerConvolutionRepresentation_mk (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerConvolutionRepresentation (Submodule.Quotient.mk g) =
      deningerMeyerHilbertConvolution g := rfl

theorem deningerMeyerConvolutionRepresentation_injective :
    Function.Injective deningerMeyerConvolutionRepresentation := by
  intro u v
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h => exact (deningerMeyerHilbertConvolution_eq_iff g h).mp

theorem deningerMeyerConvolutionRepresentation_add (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerConvolutionRepresentation (u+v) =
      deningerMeyerConvolutionRepresentation u + deningerMeyerConvolutionRepresentation v := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h => exact deningerMeyerHilbertConvolution_add g h

theorem deningerMeyerConvolutionRepresentation_smul (c : ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerConvolutionRepresentation (c • u) = c • deningerMeyerConvolutionRepresentation u := by
  induction u using Submodule.Quotient.induction_on with
  | H g => exact deningerMeyerHilbertConvolution_smul c g

def deningerMeyerConvolutionRepresentationLM :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      (DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert) where
  toFun := deningerMeyerConvolutionRepresentation
  map_add' := deningerMeyerConvolutionRepresentation_add
  map_smul' := deningerMeyerConvolutionRepresentation_smul

theorem deningerMeyerConvolutionRepresentation_mul (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerConvolutionRepresentation (deningerMeyerCohomologyConvolution u v) =
      (deningerMeyerConvolutionRepresentation u).comp (deningerMeyerConvolutionRepresentation v) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h => exact deningerMeyerHilbertConvolution_mul g h

theorem deningerMeyerConvolutionRepresentation_traceClass (u : DeningerMeyerStrongLogCohomology) :
    MemSchattenClass 1 (deningerMeyerConvolutionRepresentation u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g => exact deningerMeyerHilbertConvolution_memSchattenClass_one g

theorem deningerMeyerHilbertConvolution_eq_zero_iff (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution g = 0 ↔
      g ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  change deningerMeyerConvolutionRepresentationLM (Submodule.Quotient.mk g) = 0 ↔ _
  rw [← deningerMeyerConvolutionRepresentationLM.map_zero]
  change deningerMeyerConvolutionRepresentation (Submodule.Quotient.mk g) =
    deningerMeyerConvolutionRepresentation 0 ↔ _
  rw [deningerMeyerConvolutionRepresentation_injective.eq_iff]
  exact Submodule.Quotient.mk_eq_zero _

end RHTower
