import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.SchurTangent
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Effective spectral determinant to first order in inverse spin splitting -/
open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Substitution of u² and of zero in an auxiliary variable has the same first jet. -/
private theorem square_contact (F : ℂ × ℂ → ℂ) (hF : DifferentiableAt ℂ F (0,0)) :
    deriv (fun u : ℂ => F (u,u^2)) 0 = deriv (fun u : ℂ => F (u,0)) 0 := by
  have hsq : HasDerivAt (fun u : ℂ => u^2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0:ℂ))
  have hD : HasFDerivAt F (fderiv ℂ F (0,0)) ((0:ℂ),(0:ℂ)^2) := by simpa using hF.hasFDerivAt
  have hp : HasDerivAt (fun u : ℂ => (u,u^2)) (1,0) 0 := (hasDerivAt_id (0:ℂ)).prodMk hsq
  have hq : HasDerivAt (fun u : ℂ => (u,(0:ℂ))) (1,0) 0 :=
    (hasDerivAt_id (0:ℂ)).prodMk (hasDerivAt_const 0 (0:ℂ))
  have h₁ := hD.comp_hasDerivAt (0:ℂ) hp
  have h₂ := hF.hasFDerivAt.comp_hasDerivAt (f := fun u : ℂ => (u,(0:ℂ))) (0:ℂ) hq
  exact h₁.deriv.trans h₂.deriv.symm

/-- The normalized determinant on any analytic energy curve, to first order in u,
equals the old determinant with perturbation cuWV times the spectator determinant. -/
theorem splitDet_deriv (A : ℂ → Mat I) (hA : ∀ i j, AnalyticAt ℂ (fun t => A t i j) 0)
    (W V : Mat I) (b c : ℂ) (hbc : b*c=1) :
    deriv (fun t => splitDet (A t) W V b t) 0 =
      deriv (fun t => (A t - (c*t) • (W*V)).det * (b • 1 + t • A t).det) 0 := by
  let F (p : ℂ × ℂ) := (fromBlocks (A p.1-(c*p.1) • (W*V)) (-W)
    ((c*p.2) • (A p.1*V)) (b • (1 : Mat I)+p.1 • A p.1)).det
  have ha (i j : I) : AnalyticAt ℂ (fun p : ℂ × ℂ => A p.1 i j) (0,0) :=
    (hA i j).comp (f := fun p : ℂ × ℂ => p.1) (x := (0,0)) analyticAt_fst
  have hF : AnalyticAt ℂ F (0,0) := by
    apply analyticAt_matrix_det_parametric
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact (ha i j).sub ((analyticAt_const.mul analyticAt_fst).mul analyticAt_const)
      | inr j => exact analyticAt_const
    | inr i =>
      cases j with
      | inl j =>
        apply (analyticAt_const.mul analyticAt_snd).mul
        exact Finset.analyticAt_fun_sum _ (fun k _ => (ha i k).mul analyticAt_const)
      | inr j => exact analyticAt_const.add (analyticAt_fst.mul (ha i j))
  have h₁ : (fun t => splitDet (A t) W V b t) = fun t => F (t,t^2) := by
    funext t
    exact splitDet_normal_form _ _ _ b c t hbc
  have h₂ : (fun t => F (t,0)) = fun t => (A t - (c*t) • (W*V)).det * (b • 1+t • A t).det := by
    funext t
    simp only [F,mul_zero,zero_smul,det_fromBlocks_zero₂₁]
  rw [h₁,←h₂]
  exact square_contact F hF.differentiableAt

#print axioms splitDet_deriv
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
