import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.SchurTangent
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # The normalized characteristic root at infinite splitting -/
open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

def normalizedRelation (H W V : Mat I) (b : ℂ) (p : ℂ × ℂ) : ℂ :=
  splitDet (scalar I p.2-H) W V b p.1

theorem normalized_zero (H W V : Mat I) (b z : ℂ) :
    normalizedRelation H W V b (0,z)=H.charpoly.eval z * b^Fintype.card I := by
  simp only [normalizedRelation,splitDet,zero_smul,neg_zero,add_zero,det_fromBlocks_zero₂₁,det_smul,det_one,mul_one]
  rw [Matrix.eval_charpoly]

theorem normalized_analytic (H W V : Mat I) (b z : ℂ) :
    AnalyticAt ℂ (normalizedRelation H W V b) (0,z) := by
  have hentry (i j : I) : AnalyticAt ℂ (fun p : ℂ × ℂ => (scalar I p.2-H) i j) (0,z) := by
    by_cases hij : i=j
    · subst j; simpa [scalar_apply] using! (analyticAt_snd.sub (analyticAt_const (v := H i i)))
    · simp [scalar_apply,hij,analyticAt_const]
  apply analyticAt_matrix_det_parametric
  intro i j
  cases i with
  | inl i => cases j with
    | inl j => exact hentry i j
    | inr j => exact analyticAt_const
  | inr i => cases j with
    | inl j => exact (analyticAt_fst.mul analyticAt_const).neg
    | inr j => exact analyticAt_const.add (analyticAt_fst.mul (hentry i j))

theorem normalized_energy_partial (H W V : Mat I) (b z : ℂ) :
    fderiv ℂ (normalizedRelation H W V b) (0,z) (0,1) =
      H.charpoly.derivative.eval z * b^Fintype.card I := by
  have hd := (normalized_analytic H W V b z).differentiableAt.hasFDerivAt.comp_hasDerivAt (f := fun y : ℂ => ((0:ℂ),y)) z
    ((hasDerivAt_const z (0:ℂ)).prodMk (hasDerivAt_id z))
  have hp := (H.charpoly.hasDerivAt z).mul_const (b^Fintype.card I)
  exact hd.unique (hp.congr_of_eventuallyEq (Eventually.of_forall (normalized_zero H W V b)))

/-- Each old simple root continues analytically as the inverse splitting passes through zero. -/
theorem normalized_branch (H W V : Mat I) (b z : ℂ) (hb : b≠0)
    (hz : H.charpoly.eval z=0) (hs : H.charpoly.derivative.eval z≠0) :
    ∃ e : ℂ→ℂ, AnalyticAt ℂ e 0 ∧ e 0=z ∧
      ∀ᶠ u in 𝓝 0, splitDet (scalar I (e u)-H) W V b u=0 := by
  apply parametric_holo_implicit (normalized_analytic H W V b z)
  · rw [normalized_zero,hz,zero_mul]
  · rw [normalized_energy_partial]
    exact mul_ne_zero hs (pow_ne_zero _ hb)

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
