import GaloisForLFunctions.RHTower.DeningerMeyerStripBezout
import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionRepairSource
import GaloisForLFunctions.RHTower.DeningerMeyerFaithfulConvolution

/-! # Spectral invariance of the repaired original convolution algebra

The bounded Fredholm inverse is itself identity plus convolution by an
original all-weight Meyer source. All denominator zeros are removed inside
the admitted source class, before descending through the actual Poisson ideal.
-/

open Complex
namespace RHTower
noncomputable section

theorem deningerMeyerXi_entireRegular : DeningerEntireMellinRegular xi := by
  have he : deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogSumLM deningerMeyerXiCapSource) = xi :=
    funext deningerMeyerXiCapSource_mellin
  rw [← he]
  exact deningerMeyerStrongLogMellin_entireRegular _

/-- The only obstruction to source-class inversion is an actual common Xi zero. -/
theorem exists_deningerMeyerSourceQuasiInverse (g : DeningerMeyerStrongLogTarget)
    (hcop : ∀ rho : XiDivisorSupport, 1+deningerMeyerStrongLogMellin g (rho : ℂ) ≠ 0) :
    ∃ h : DeningerMeyerStrongLogTarget,
      g+h+deningerMeyerSourceConvolution g h ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  obtain ⟨K, H, hK, hH, he⟩ := exists_deningerMeyerStripBezout
    (deningerMeyerStrongLogMellin_entireRegular g) deningerMeyerXi_entireRegular (by
      intro z hz hxi
      exact hcop ⟨z, mem_xi_divisor_support_of_eq_zero hxi⟩ hz)
  let h := deningerMeyerInverseMellinSource K hK
  refine ⟨h, deningerMeyerXiDivision_has_cap _ hH.differentiable.neg ?_⟩
  intro z
  change deningerMeyerStrongLogMellinLM z (g+h+deningerMeyerSourceConvolution g h) = xi z*(-H z)
  rw [map_add, map_add]
  change deningerMeyerStrongLogMellin g z+deningerMeyerStrongLogMellin h z+
    deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g h) z = xi z*(-H z)
  rw [deningerMeyerSourceConvolution_mellin]
  simp only [h, deningerMeyerInverseMellinSource_mellin]
  linear_combination he z

theorem deningerMeyerSourceQuasiInverse_hilbert (g h : DeningerMeyerStrongLogTarget)
    (he : g+h+deningerMeyerSourceConvolution g h ∈ LinearMap.range deningerMeyerStrongLogSumLM)
    (x : DeningerArithmeticJetHilbert) :
    (1+deningerMeyerHilbertConvolution g) (x+deningerMeyerHilbertConvolution h x) = x := by
  have hz := (deningerMeyerHilbertConvolution_eq_zero_iff _).mpr he
  rw [deningerMeyerHilbertConvolution_add, deningerMeyerHilbertConvolution_add,
    deningerMeyerHilbertConvolution_mul] at hz
  have hx := congrArg (fun T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert => T x) hz
  change deningerMeyerHilbertConvolution g x+deningerMeyerHilbertConvolution h x+
    deningerMeyerHilbertConvolution g (deningerMeyerHilbertConvolution h x) = 0 at hx
  change x+deningerMeyerHilbertConvolution h x+
    deningerMeyerHilbertConvolution g (x+deningerMeyerHilbertConvolution h x) = x
  rw [map_add]
  calc x+deningerMeyerHilbertConvolution h x+
      (deningerMeyerHilbertConvolution g x+
        deningerMeyerHilbertConvolution g (deningerMeyerHilbertConvolution h x)) =
        x+(deningerMeyerHilbertConvolution g x+deningerMeyerHilbertConvolution h x+
          deningerMeyerHilbertConvolution g (deningerMeyerHilbertConvolution h x)) := by abel
    _ = x := by rw [hx, add_zero]

/-- Unconditional original-source realization of every complete Fredholm inverse. -/
theorem exists_deningerMeyerConvolutionFredholmInverse_source
    (g : DeningerMeyerStrongLogTarget) :
    ∃ h : DeningerMeyerStrongLogTarget,
      deningerMeyerConvolutionFredholmInverse g = 1+deningerMeyerHilbertConvolution h := by
  obtain ⟨b, hb, hcop⟩ := exists_deningerMeyerConvolutionRepairSource g
  obtain ⟨h, hh⟩ := exists_deningerMeyerSourceQuasiInverse b hcop
  refine ⟨h, ContinuousLinearMap.ext fun x => ?_⟩
  have hx : deningerMeyerConvolutionFredholmRepair g (x+deningerMeyerHilbertConvolution h x) = x := by
    rw [← hb]
    exact deningerMeyerSourceQuasiInverse_hilbert b h hh x
  calc deningerMeyerConvolutionFredholmInverse g x =
      deningerMeyerConvolutionFredholmInverse g
        (deningerMeyerConvolutionFredholmRepair g (x+deningerMeyerHilbertConvolution h x)) := by rw [hx]
    _ = x+deningerMeyerHilbertConvolution h x := deningerMeyerConvolutionFredholmInverse_left g _

/-- One actual all-weight kernel for the repaired inverse. Its cohomology
class is intrinsic, by faithfulness of the convolution representation. -/
def deningerMeyerConvolutionInverseKernel (g : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  Classical.choose (exists_deningerMeyerConvolutionFredholmInverse_source g)

theorem deningerMeyerConvolutionInverseKernel_spec (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerConvolutionFredholmInverse g =
      1+deningerMeyerHilbertConvolution (deningerMeyerConvolutionInverseKernel g) :=
  Classical.choose_spec (exists_deningerMeyerConvolutionFredholmInverse_source g)

theorem deningerMeyerConvolutionFredholmInverse_source
    (g : DeningerMeyerStrongLogTarget) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerConvolutionFredholmInverse g (deningerMeyerHasseHilbertLM u) =
      deningerMeyerHasseHilbertLM
        (u+deningerMeyerCohomologyConvolution
          (Submodule.Quotient.mk (deningerMeyerConvolutionInverseKernel g)) u) := by
  rw [deningerMeyerConvolutionInverseKernel_spec]
  change deningerMeyerHasseHilbertLM u+
    deningerMeyerHilbertConvolution (deningerMeyerConvolutionInverseKernel g)
      (deningerMeyerHasseHilbertLM u) = _
  rw [deningerMeyerHilbertConvolution_source, map_add]

end
end RHTower
