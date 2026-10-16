import GaloisForLFunctions.RHTower.DeningerMeyerOriginalConvolutionInverse
import GaloisForLFunctions.RHTower.PaperThetaConvolutionGauge

/-! # Native theta solving for arbitrary original convolution symbols

The original-source Fredholm inverse preserves every full native packet.
Transport through the faithful spatial comparison gives actual compact AC
solutions for all source symbols, including symbols with resonant zeros.
-/

noncomputable section
open Complex Set
namespace RHTower.PaperThetaEndpoint

private theorem convolution_zero_packet (g : DeningerMeyerStrongLogTarget)
    (rho : XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology)
    (hu : ∀ j, deningerMeyerXiSupportJetEvaluationLM rho j u = 0)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j
      (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) u) = 0 := by
  have hz : deningerMeyerHasseHilbertLM
      (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) u) ⟨rho, j⟩ = 0 := by
    rw [← deningerMeyerHilbertConvolution_source, deningerMeyerHilbertConvolution_jets]
    apply Finset.sum_eq_zero
    intro k _
    have he : deningerMeyerHasseHilbertLM u (deningerHasseLower ⟨rho, j⟩ k) = 0 := by
      change deningerMeyerXiSupportJetEvaluationLM rho _ u / _ = 0
      rw [hu, zero_div]
    rw [he, mul_zero]
  have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  change deningerMeyerXiSupportJetEvaluationLM rho j
    (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) u) /
      (j.val.factorial : ℂ) = 0 at hz
  apply (div_left_inj' hf).mp
  simpa only [zero_div] using hz

theorem meyerFiniteUnitConvolution_mem (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    u.val+deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) u.val ∈
      LinearMap.range (meyerFiniteHedenmalmSynthesis S) := by
  apply (mem_meyerFiniteHedenmalmRange_iff S _).mpr
  intro rho hrho j
  have hu := (mem_meyerFiniteHedenmalmRange_iff S u.val).mp u.property rho hrho
  rw [map_add, hu j, convolution_zero_packet g rho u.val hu j, add_zero]

theorem meyerFiniteConvolutionInverse_mem (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    deningerMeyerOriginalConvolutionInverse g u.val ∈
      LinearMap.range (meyerFiniteHedenmalmSynthesis S) :=
  meyerFiniteUnitConvolution_mem S (deningerMeyerConvolutionInverseKernel g) u

theorem meyerFiniteConvolutionRepair_mem (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    deningerMeyerOriginalConvolutionRepair g u.val ∈
      LinearMap.range (meyerFiniteHedenmalmSynthesis S) := by
  obtain ⟨b, hb, _⟩ := exists_deningerMeyerConvolutionRepairSource g
  have he : deningerMeyerOriginalConvolutionRepair g u.val =
      u.val+deningerMeyerCohomologyConvolution (Submodule.Quotient.mk b) u.val := by
    apply deningerMeyerHasseHilbertLM_injective
    rw [deningerMeyerOriginalConvolutionRepair_hilbert, ← hb]
    change deningerMeyerHasseHilbertLM u.val+
      deningerMeyerHilbertConvolution b (deningerMeyerHasseHilbertLM u.val) = _
    rw [deningerMeyerHilbertConvolution_source, map_add]
  rw [he]
  exact meyerFiniteUnitConvolution_mem S b u

def meyerFiniteConvolutionRepairEquiv (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) :
    LinearMap.range (meyerFiniteHedenmalmSynthesis S) ≃ₗ[ℂ]
      LinearMap.range (meyerFiniteHedenmalmSynthesis S) where
  toFun u := ⟨deningerMeyerOriginalConvolutionRepair g u.val, meyerFiniteConvolutionRepair_mem S g u⟩
  invFun u := ⟨deningerMeyerOriginalConvolutionInverse g u.val, meyerFiniteConvolutionInverse_mem S g u⟩
  left_inv u := Subtype.ext (deningerMeyerOriginalConvolutionInverse_left g u.val)
  right_inv u := Subtype.ext (deningerMeyerOriginalConvolutionInverse_right g u.val)
  map_add' u v := Subtype.ext ((deningerMeyerOriginalConvolutionRepair g).map_add u.val v.val)
  map_smul' c u := Subtype.ext ((deningerMeyerOriginalConvolutionRepair g).map_smul c u.val)

/-- Actual native realization of the complete full-multiplicity repair. -/
def thetaFiniteConvolutionRepairEquiv (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) :
    LinearMap.range (thetaFiniteSynthesis S) ≃ₗ[ℂ] LinearMap.range (thetaFiniteSynthesis S) :=
  (meyerThetaFiniteEquiv S).symm.trans
    ((meyerFiniteConvolutionRepairEquiv S g).trans (meyerThetaFiniteEquiv S))

theorem thetaFiniteConvolutionRepair_original (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (u : LinearMap.range (thetaFiniteSynthesis S)) :
    ((meyerThetaFiniteEquiv S).symm (thetaFiniteConvolutionRepairEquiv S g u)).val =
      deningerMeyerOriginalConvolutionRepair g ((meyerThetaFiniteEquiv S).symm u).val := by
  simp only [thetaFiniteConvolutionRepairEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rfl

/-- Every forcing in every admitted native packet has a unique compact AC
solution for the repaired arbitrary source symbol. -/
theorem thetaConvolutionFredholm_existsUnique_admitted (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (f : LinearMap.range (thetaFiniteSynthesis S)) :
    ∃! u : LinearMap.range (thetaFiniteSynthesis S),
      (thetaFiniteConvolutionRepairEquiv S g u).val.val = f.val.val ∧
        AbsolutelyContinuousOnInterval (thetaFiniteCompactRepresentative S u) 0 1 := by
  refine ⟨(thetaFiniteConvolutionRepairEquiv S g).symm f, ?_, ?_⟩
  · exact ⟨congrArg (fun u => u.val.val) ((thetaFiniteConvolutionRepairEquiv S g).apply_symm_apply f),
      absolutelyContinuousOnInterval_thetaFiniteCompactRepresentative S _⟩
  · intro u hu
    apply (thetaFiniteConvolutionRepairEquiv S g).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (Subtype.ext hu.1)

end RHTower.PaperThetaEndpoint
