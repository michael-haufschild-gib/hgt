import GaloisForLFunctions.RHTower.DeningerMeyerFredholmXi
import GaloisForLFunctions.RHTower.PaperThetaConfluentCurrent

/-! # The native theta gluing threshold is the actual Meyer spectral rank

The full algebraic multiplicity of the source resolvent equals the number
of admitted lower theta parameter orders. The next order is discontinuous
at every finite cut. This identifies RN's native gluing filtration with
the full, possibly nonsemisimple HF Fredholm multiplicity.
-/

noncomputable section
open Complex Set

namespace RHTower

def deningerMeyerHasseSpectralRank (rho : XiDivisorSupport) : ℕ :=
  Module.finrank ℂ (Module.End.maxGenEigenspace
    (deningerMeyerHasseResolvent : DeningerArithmeticJetHilbert →ₗ[ℂ]
      DeningerArithmeticJetHilbert) (xiSpectralPointSupport rho)⁻¹)

theorem deningerMeyerHasseSpectralRank_eq (rho : XiDivisorSupport) :
    deningerMeyerHasseSpectralRank rho = xiSupportMultiplicity rho := by
  have h := deningerMeyerHasseResolvent_algebraicMultiplicity rho
  rw [XiC_analyticOrderAt_support] at h
  exact_mod_cast h.symm

namespace PaperThetaEndpoint

/-- Every order below the source's full generalized spectral rank is an
actual uncut absolutely continuous theta mode. -/
theorem absolutelyContinuousOnInterval_below_meyerSpectralRank
    (rho : XiDivisorSupport) (j : Fin (deningerMeyerHasseSpectralRank rho)) :
    AbsolutelyContinuousOnInterval
      (closedParameterJet j.val (xiSpectralPointSupport rho)) 0 1 := by
  apply absolutelyContinuousOnInterval_divisor_closedParameterJet rho
    ⟨j.val, by simpa only [deningerMeyerHasseSpectralRank_eq] using j.isLt⟩

/-- At the full spectral rank the actual native mode fails to glue,
at every interior cut. -/
theorem not_continuousAt_meyerSpectralRank_cut
    (rho : XiDivisorSupport) (c : Ioo (0 : ℝ) 1) :
    ¬ ContinuousAt (cutQuantileParameterJet (deningerMeyerHasseSpectralRank rho)
      (xiSpectralPointSupport rho) c) c.val := by
  rw [deningerMeyerHasseSpectralRank_eq]
  exact not_continuousAt_terminal_cutQuantileParameterJet rho c

end PaperThetaEndpoint
end RHTower
