import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.RealDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Mixed real spectral derivatives depend only on the multiset of coordinates -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
noncomputable section
variable {n : ℕ}
private abbrev E := Fin n→ℝ

private def direction (i : Fin n) : Fin n → ℝ := Pi.single i 1

private theorem line_derivative (x : E) (i : Fin n) :
    HasDerivAt (realLine x i) (direction i) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hj : j=i
  · subst j
    simpa [realLine,direction] using (hasDerivAt_id (0:ℝ)).const_add (x i)
  · simpa [realLine,direction,hj,Pi.single_apply,Ne.symm hj] using (hasDerivAt_const (0:ℝ) (x j))

private theorem line_zero (x : E) (i : Fin n) : realLine x i 0=x := by
  ext j
  simp [realLine]

private theorem head_eq {g : E→ℝ} {x : E} (h : DifferentiableAt ℝ g x) (i : Fin n) :
    realMixed [i] g x=fderiv ℝ g x (direction i) := by
  have h' : HasFDerivAt g (fderiv ℝ g x) (realLine x i 0) := by
    rw [line_zero]
    exact h.hasFDerivAt
  exact (h'.comp_hasDerivAt 0 (line_derivative x i)).deriv

private theorem realMixed_analytic {g : E→ℝ} {x : E} (h : AnalyticAt ℝ g x) (w : List (Fin n)) :
    AnalyticAt ℝ (realMixed w g) x := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    let A := ContinuousLinearMap.apply ℝ ℝ (direction i)
    apply ((A.analyticAt _).comp ih.fderiv).congr
    exact ih.eventually_analyticAt.mono fun _ hy => (head_eq hy.differentiableAt i).symm

private theorem hessian_entry {g : E→ℝ} {x : E} (hg : AnalyticAt ℝ g x) (i j : Fin n) :
    realMixed [i,j] g x=fderiv ℝ (fderiv ℝ g) x (direction i) (direction j) := by
  let A := ContinuousLinearMap.apply ℝ ℝ (direction j)
  have he : realMixed [j] g =ᶠ[𝓝 x] A ∘ fderiv ℝ g :=
    hg.eventually_analyticAt.mono fun _ hy => head_eq hy.differentiableAt j
  have h := A.hasFDerivAt.comp x hg.fderiv.differentiableAt.hasFDerivAt
  change realMixed [i] (realMixed [j] g) x=_
  rw [head_eq (realMixed_analytic hg [j]).differentiableAt,he.fderiv_eq,h.fderiv]
  rfl

/-- Exchanging adjacent coordinates uses symmetry of the Hessian of the
remaining derivative. Taking further derivatives preserves the germ equality. -/
theorem realMixed_perm {w v : List (Fin n)} (hp : w.Perm v) {g : E→ℝ}
    {x : E} (hg : AnalyticAt ℝ g x) : realMixed w g x=realMixed v g x := by
  induction hp generalizing x with
  | nil => rfl
  | cons i h ih =>
    have ht : Tendsto (realLine x i) (𝓝 0) (𝓝 x) := by
      simpa only [line_zero] using (line_derivative x i).continuousAt.tendsto
    apply Filter.EventuallyEq.deriv_eq
    exact (ht.eventually hg.eventually_analyticAt).mono fun _ hy => ih hy
  | swap i j w =>
    let F := realMixed w g
    have hF := realMixed_analytic hg w
    change realMixed [j,i] F x=realMixed [i,j] F x
    rw [hessian_entry hF,hessian_entry hF]
    exact hF.contDiffAt.isSymmSndFDerivAt_of_omega _ _
  | trans _ _ ih₁ ih₂ => exact (ih₁ hg).trans (ih₂ hg)

end
end GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
