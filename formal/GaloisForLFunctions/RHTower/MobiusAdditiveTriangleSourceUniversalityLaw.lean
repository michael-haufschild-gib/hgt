import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangle
import GaloisForLFunctions.RHTower.MobiusLaplaceHedenmalmSimplicityUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusLaplacePolylogSharpCoefficientLaw
import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceUniversalityLaw

/-!
# Additive Möbius triangle source universality

A one-sided linear upper bound on cumulative additive Möbius self-convolution first controls the
square of the discrete Möbius--Laplace transform.  The resulting exact half-power source estimate
then enters both the Hedenmalm simplicity phase and the reconstructed reciprocal-square source
phase.  At each critical zeta zero it also bounds the top local coefficient by the same retained
Möbius--Laplace constant.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- Simultaneous half-decay, Hedenmalm simplicity, reciprocal-square source reconstruction, and
sharp local zeta-coefficient realization supplied by one additive-triangle upper bound. -/
def MobiusAdditiveTriangleSourceUniversalCertificate (C delta : ℝ) : Prop :=
  0 ≤ C ∧
  0 < delta ∧
  (∀ x : ℝ, 0 < x → x < delta →
    ‖mobiusDiscreteLaplaceTransform x‖ ≤
      C * mobiusLaplaceHalfPolylogKernel 0 x) ∧
  XiHedenmalmRHSimplicityUniversalCertificate ∧
  XiReciprocalSquareSourceUniversalCertificate ∧
  ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
    ∃ p : ℂ → ℂ,
      AnalyticAt ℂ p rho ∧ p rho ≠ 0 ∧
      riemannZeta =ᶠ[𝓝 rho] (fun z : ℂ => (z - rho) * p z) ∧
      ‖Complex.Gamma rho / p rho‖ ≤ C

/-- **Additive Möbius triangle source universality law.** A one-sided linear bound on the
cumulative additive Möbius triangle supplies one retained half-decay witness which simultaneously
forces the full Hedenmalm RH--simplicity certificate, the full reciprocal-square source
certificate, and the sharp coefficient cap at every critical zeta zero. -/
theorem mobiusAdditiveTriangleLinearUpperBound_implies_sourceUniversalCertificate
    (hupper : MobiusAdditiveTriangleLinearUpperBound) :
    ∃ C delta : ℝ, MobiusAdditiveTriangleSourceUniversalCertificate C delta := by
  have hpolylog : MobiusDiscreteLaplaceHalfPolylogDecay 0 :=
    mobiusAdditiveTriangleLinearUpperBound_implies_halfDecay hupper
  rcases hpolylog with ⟨C, delta, hC, hdelta, hsource⟩
  have hdecay : MobiusDiscreteLaplaceHalfDecay :=
    mobiusAdditiveTriangleLinearUpperBound_implies_discreteLaplaceHalfDecay hupper
  have hRH : RiemannHypothesis :=
    mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis hdecay
  have hreciprocal : XiReciprocalSquareSourceUniversalCertificate :=
    xiReciprocalSquareOperator_isSelfAdjoint_iff_sourceUniversalCertificate.1
      (xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis.2 hRH)
  refine ⟨C, delta, hC, hdelta, hsource,
    mobiusDiscreteLaplaceHalfDecay_implies_hendenmalmRHSimplicityUniversalCertificate hdecay,
    hreciprocal, ?_⟩
  intro rho hrho hzero
  have horder : analyticOrderAt riemannZeta rho = (1 : ℕ∞) :=
    analyticOrderAt_riemannZeta_eq_one_of_mobiusDiscreteLaplaceHalfDecay
      hdecay hrho hzero
  simpa using
    (exists_localFactor_with_Gamma_cap_of_halfPolylog_maximalOrder
      (q := 0) hC hdelta hsource hrho horder)

end

end RHTower
