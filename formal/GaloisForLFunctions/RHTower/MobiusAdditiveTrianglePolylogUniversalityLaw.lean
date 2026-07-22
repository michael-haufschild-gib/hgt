import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTrianglePolylog
import GaloisForLFunctions.RHTower.MobiusLaplacePolylogBoundaryMultiplicity
import GaloisForLFunctions.RHTower.MobiusLaplacePolylogSharpCoefficientLaw
import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceUniversalityLaw

/-!
# Additive Möbius triangle fixed-polylog source universality

A one-sided degree-`2q` logarithmic upper bound on cumulative additive Möbius
self-convolution forces degree-`q` half-polylog Möbius--Laplace decay.  One retained
source witness then controls zero location, critical-line multiplicity, the complete
reciprocal-square source phase, and the sharp local coefficient at maximal multiplicity.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- Simultaneous source estimate, RH, reciprocal-square realization, multiplicity cap, and
sharp maximal-order local coefficient supplied by one additive-triangle polylog bound. -/
def MobiusAdditiveTrianglePolylogSourceUniversalCertificate
    (q : ℕ) (C delta : ℝ) : Prop :=
  0 ≤ C ∧
  0 < delta ∧
  (∀ x : ℝ, 0 < x → x < delta →
    ‖mobiusDiscreteLaplaceTransform x‖ ≤
      C * mobiusLaplaceHalfPolylogKernel q x) ∧
  RiemannHypothesis ∧
  XiReciprocalSquareSourceUniversalCertificate ∧
  (∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
    (analyticOrderAt riemannZeta rho).toNat ≤ q + 1) ∧
  ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
    analyticOrderAt riemannZeta rho = ((q + 1 : ℕ) : ℕ∞) →
    ∃ p : ℂ → ℂ,
      AnalyticAt ℂ p rho ∧ p rho ≠ 0 ∧
      riemannZeta =ᶠ[𝓝 rho]
        (fun z : ℂ => (z - rho) ^ (q + 1) * p z) ∧
      ‖Complex.Gamma rho / p rho‖ ≤ C * (q.factorial : ℝ)

/-- **Additive Möbius triangle fixed-polylog universality law.** A one-sided
`N log(N)^(2q)` upper bound supplies one retained degree-`q` source witness which forces RH,
all reciprocal-square source charts, the critical-line multiplicity cap `q + 1`, and the sharp
`C q!` local coefficient cap whenever that multiplicity is attained. -/
theorem mobiusAdditiveTriangleLinearPolylogUpperBound_implies_sourceUniversalCertificate
    (q : ℕ) (hupper : MobiusAdditiveTriangleLinearPolylogUpperBound q) :
    ∃ C delta : ℝ,
      MobiusAdditiveTrianglePolylogSourceUniversalCertificate q C delta := by
  have hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q :=
    mobiusAdditiveTriangleLinearPolylogUpperBound_implies_halfPolylogDecay hupper
  rcases hdecay with ⟨C, delta, hC, hdelta, hsource⟩
  have hdecay' : MobiusDiscreteLaplaceHalfPolylogDecay q :=
    ⟨C, delta, hC, hdelta, hsource⟩
  have hboundary :=
    mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis_and_multiplicityCap
      hdecay'
  have hreciprocal : XiReciprocalSquareSourceUniversalCertificate :=
    xiReciprocalSquareOperator_isSelfAdjoint_iff_sourceUniversalCertificate.1
      (xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis.2 hboundary.1)
  refine ⟨C, delta, hC, hdelta, hsource, hboundary.1, hreciprocal,
    hboundary.2, ?_⟩
  intro rho hrho _ horder
  exact exists_localFactor_with_Gamma_cap_of_halfPolylog_maximalOrder
    hC hdelta hsource hrho horder

end

end RHTower
