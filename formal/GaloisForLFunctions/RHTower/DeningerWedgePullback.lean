import GaloisForLFunctions.RHTower.DeningerStageKFormExact
import GaloisForLFunctions.RHTower.DeningerDlogWedge

/-!
# The generators pull back to constant forms

Along the exponential covering the exterior product of the logarithmic differentials becomes the
determinant in the chosen coordinates, a form with constant coefficients: the inverse coordinates in
its coefficient exactly cancel the diagonal of the derivative of the covering.  So the classes of
the generators are detected upstairs by constant forms, which is the starting point for separating
them in cohomology.

* `deningerExpPullback_dlogWedge` : the generator pulls back to the determinant form.
-/

namespace RHTower

open Complex

section WedgePullback

variable {r k : ℕ}

/-- **The exterior product of logarithmic differentials pulls back to the determinant form**, which
has constant coefficients. -/
theorem deningerExpPullback_dlogWedge (σ : Fin k → Fin r) (w : Fin r → ℂ) :
    deningerExpPullbackForm (deningerDlogWedge σ) w = deningerDetForm σ := by
  ext v
  show (deningerDlogWedge σ (deningerExpMap r w))
    (fun i => fderiv ℂ (deningerExpMap r) w (v i)) = deningerDetForm σ v
  rw [(deningerExpMap_hasFDerivAt w).fderiv]
  show (∏ j, ((deningerExpMap r w) (σ j))⁻¹) *
    deningerDetForm σ (fun i => deningerExpDeriv w (v i)) = deningerDetForm σ v
  rw [deningerDetForm_apply, deningerDetForm_apply]
  have hmat : (Matrix.of fun a b => (deningerExpDeriv w (v a)) (σ b)) =
      Matrix.of fun a b => Complex.exp (w (σ b)) * (v a (σ b)) := rfl
  rw [hmat, Matrix.det_mul_row]
  have hcancel : (∏ j, ((deningerExpMap r w) (σ j))⁻¹) * (∏ j, Complex.exp (w (σ j))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    have hterm : ∀ j : Fin k,
        ((deningerExpMap r w) (σ j))⁻¹ * Complex.exp (w (σ j)) = 1 := by
      intro j
      show (Complex.exp (w (σ j)))⁻¹ * Complex.exp (w (σ j)) = 1
      exact inv_mul_cancel₀ (Complex.exp_ne_zero _)
    rw [Finset.prod_congr rfl fun j _ => hterm j, Finset.prod_const_one]
  calc (∏ j, ((deningerExpMap r w) (σ j))⁻¹) *
        ((∏ j, Complex.exp (w (σ j))) * (Matrix.of fun a b => v a (σ b)).det)
      = ((∏ j, ((deningerExpMap r w) (σ j))⁻¹) * (∏ j, Complex.exp (w (σ j)))) *
        (Matrix.of fun a b => v a (σ b)).det := by ring
    _ = (Matrix.of fun a b => v a (σ b)).det := by rw [hcancel, one_mul]

end WedgePullback

end RHTower
