import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularScalarEquation

/-! Original hyperbolic Laplacian of a full smooth height field. -/
open Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMCuspProjection
open D4BMAngularSeries
noncomputable section

private theorem height_coord_deriv (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (i : Fin 2) (z : Fin 2 → ℝ) :
    coordDeriv i (fun w => f (w 1)) z = if i=1 then deriv f (z 1) else 0 := by
  have hd := (hf (z 1)).hasDerivAt.hasFDerivAt.comp z
    ((show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 1).hasFDerivAt)
  change HasFDerivAt (fun w : Fin 2 → ℝ => f (w 1)) _ z at hd
  rw [coordDeriv,hd.fderiv]
  fin_cases i <;> simp [ContinuousLinearMap.comp_apply]

/-- The literal hyperbolic Laplacian of any smooth height field. -/
theorem height_laplacian (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (z : Fin 2 → ℝ) :
    hyperbolicLaplacian (fun w => f (w 1)) z = (z 1:ℂ)^2*deriv (deriv f) (z 1) := by
  have h0 : coordDeriv 0 (fun w : Fin 2 → ℝ => f (w 1)) = fun _ => 0 := by
    funext w
    simpa using height_coord_deriv f (hf.differentiable (by simp)) 0 w
  have h1 : coordDeriv 1 (fun w : Fin 2 → ℝ => f (w 1)) = fun w => deriv f (w 1) := by
    funext w
    simpa using height_coord_deriv f (hf.differentiable (by simp)) 1 w
  rw [hyperbolicLaplacian,h0,h1,height_coord_deriv (deriv f)
    ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp))]
  simp [coordDeriv]

end
end RHTower.D4BMCuspProjection
