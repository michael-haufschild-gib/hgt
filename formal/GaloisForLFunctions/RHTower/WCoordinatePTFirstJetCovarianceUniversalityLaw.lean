import GaloisForLFunctions.HTGeometry.PTInvolution
import GaloisForLFunctions.RHTower.WCoordinate
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# W-coordinate PT first-jet covariance universality law

The Li/Bombieri--Lagarias coordinate conjugates the functional-equation involution
`sigma(z) = 1 - z` to inversion.  The scalar conjugacy extends to an exact first-jet law:
the reflected derivative is transported by the product of the Li-coordinate Jacobian and the
inversion Jacobian.  This holds for every scalar function differentiable at the transported point.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The Li coordinate has inverse-square derivative away from its pole. -/
theorem hasDerivAt_wCoordinate {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt wCoordinate (z⁻¹ ^ 2) z := by
  unfold wCoordinate
  simpa [inv_pow] using!
    (hasDerivAt_const (x := z) (c := (1 : ℂ))).sub (hasDerivAt_inv hz)

/-- The derivative weight at the reflected point factors into the Li-coordinate Jacobian and
the inversion Jacobian. -/
theorem wCoordinate_PT_derivativeWeight
    {z : ℂ} (hz0 : z ≠ 0) :
    (sigma z)⁻¹ ^ 2 = z⁻¹ ^ 2 * (wCoordinate z)⁻¹ ^ 2 := by
  unfold sigma wCoordinate
  field_simp
  ring

/-- **W-coordinate PT first-jet covariance universality law.**  Away from `0` and `1`, functional-
equation pullback of `f ∘ w` is inversion pullback in the `w` coordinate.  Its first derivative
acquires exactly the product of the `w`-Jacobian `z⁻²` and inversion weight `w(z)⁻²`, together with
the PT sign. -/
theorem wCoordinate_fePullback_firstJet
    (f : ℂ → ℂ) {z f' : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hf : HasDerivAt f f' ((wCoordinate z)⁻¹)) :
    fePullback (fun s => f (wCoordinate s)) z =
        f ((wCoordinate z)⁻¹) ∧
      HasDerivAt (fePullback (fun s => f (wCoordinate s)))
        (-(f' * z⁻¹ ^ 2 * (wCoordinate z)⁻¹ ^ 2)) z := by
  have hsigma0 : sigma z ≠ 0 := by
    unfold sigma
    exact sub_ne_zero.mpr hz1.symm
  have hcoord : wCoordinate (sigma z) = (wCoordinate z)⁻¹ :=
    wCoordinate_sigma_eq_inv z hz0 hz1
  have hinner : HasDerivAt (fun s => f (wCoordinate s))
      (f' * (sigma z)⁻¹ ^ 2) (sigma z) := by
    exact (hcoord ▸ hf).comp (sigma z) (hasDerivAt_wCoordinate hsigma0)
  refine ⟨by simp only [fePullback_apply, hcoord], ?_⟩
  have hpull := hasDerivAt_fePullback hinner
  rw [wCoordinate_PT_derivativeWeight hz0] at hpull
  simpa only [mul_assoc] using hpull

end

end GaloisForLFunctions
