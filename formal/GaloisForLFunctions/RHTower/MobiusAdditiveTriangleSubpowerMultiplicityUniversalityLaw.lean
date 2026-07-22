import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTrianglePolylog
import GaloisForLFunctions.RHTower.MobiusLaplaceSubpowerCriterion

/-!
# Additive-triangle subpower/multiplicity universality

A fixed degree-2q logarithmic loss in the additive Möbius triangle has two distinct analytic
closures. In the open half-plane it yields every strict half-power estimate, so the degree is
forgotten by Mellin continuation and RH. At the critical boundary the same degree remains visible
as the sharp zero-multiplicity cap q+1.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

def MobiusAdditiveTriangleSubpowerMultiplicityUniversalCertificate (q : ℕ) : Prop :=
  MobiusDiscreteLaplaceAllStrictHalfPowerDecay ∧
  AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf ∧
  MobiusLaplaceMellinContinuationWall ∧
  RiemannHypothesis ∧
  ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
    (analyticOrderAt riemannZeta rho).toNat ≤ q + 1

theorem mobiusAdditiveTriangleLinearPolylogUpperBound_implies_allStrictHalfPowerDecay
    {q : ℕ} (hupper : MobiusAdditiveTriangleLinearPolylogUpperBound q) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  have hhalf : MobiusDiscreteLaplaceHalfPolylogDecay q :=
    mobiusAdditiveTriangleLinearPolylogUpperBound_implies_halfPolylogDecay hupper
  intro b hb
  exact hhalf.isBigO_rpow hb

theorem mobiusAdditiveTriangleLinearPolylogUpperBound_implies_subpowerMultiplicityCertificate
    {q : ℕ} (hupper : MobiusAdditiveTriangleLinearPolylogUpperBound q) :
    MobiusAdditiveTriangleSubpowerMultiplicityUniversalCertificate q := by
  have hstrict : MobiusDiscreteLaplaceAllStrictHalfPowerDecay :=
    mobiusAdditiveTriangleLinearPolylogUpperBound_implies_allStrictHalfPowerDecay hupper
  have hanalytic :
      AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf :=
    analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_allStrictHalfPower hstrict
  have hwall : MobiusLaplaceMellinContinuationWall :=
    mobiusLaplaceMellinContinuationWall_of_allStrictHalfPower hstrict
  have hboundary :=
    mobiusAdditiveTriangleLinearPolylogUpperBound_implies_RH_and_multiplicityCap hupper
  exact ⟨hstrict, hanalytic, hwall, hboundary⟩

end

end RHTower
