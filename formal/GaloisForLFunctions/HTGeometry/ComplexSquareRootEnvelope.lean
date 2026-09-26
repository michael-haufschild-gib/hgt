import Mathlib.Analysis.RCLike.Sqrt

/-!
# A polynomial envelope for the complex square root

On the closed right half-plane the square-root norm is bounded by the norm
of the affine weight z+1. This gives a common polynomial envelope.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.ComplexSquareRootEnvelope

lemma sqrt_norm_sq (z : ℂ) : ‖Complex.sqrt z‖^2 = ‖z‖ := by
  have hh : Complex.sqrt z^2 = z := by
    simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow z 2
  simpa only [norm_pow] using congrArg norm hh

lemma sqrt_norm_le_add_one {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.sqrt z‖ ≤ ‖z+1‖ := by
  have hnorm : ‖z+1‖^2 = ‖z‖^2+2*z.re+1 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
    ring
  nlinarith [sqrt_norm_sq z, norm_nonneg (Complex.sqrt z), norm_nonneg (z+1),
    sq_nonneg (‖z‖-1/2)]

end GaloisForLFunctions.HTGeometry.ComplexSquareRootEnvelope
