import GaloisForLFunctions.RHTower.ThetaCuspRatioSlopeSeamSign
import GaloisForLFunctions.RHTower.ThetaCuspRatioIntegerIncidence
/-! # Positive tangent of the actual source slope on the admissible seam cone.

This sign holds uniformly for 5/4 ≤ k ≤ 19/15 and 0 ≤ J/U ≤ 1/3.
It does not establish the sign at positive distance from the seam. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

/-- The source slope has a strictly positive tangent on the complete admissible seam cone. -/
theorem thirdSlope_seam_tangent_pos {k z : ℝ} (hk0 : 5/4≤k) (hk1 : k≤19/15)
    (hz0 : 0≤z) (hz1 : z≤1/3) :
    0 < (eval (seamPoint (k:ℂ)) (pderiv Coord.U thirdSlope) +
      (z:ℂ)*eval (seamPoint (k:ℂ)) (pderiv Coord.J thirdSlope)).re := by
  have hp := seam_tangent_cone_pos hk0 hk1 hz0 hz1
  have he : (6:ℂ)^26*(eval (seamPoint (k:ℂ)) (pderiv Coord.U thirdSlope) +
      (z:ℂ)*eval (seamPoint (k:ℂ)) (pderiv Coord.J thirdSlope)) =
      ((alphaReal k+z*betaReal k:ℝ):ℂ) := by
    rw [mul_add,← mul_assoc, mul_comm ((6:ℂ)^26) (z:ℂ),mul_assoc,
      ← integerSlope_partial_eq,← integerSlope_partial_eq,
      seamSlopeAlpha_eq,seamSlopeBeta_eq,← alphaReal_eq,← betaReal_eq]
    push_cast
    rfl
  have hr := congrArg Complex.re he
  simp only [Complex.mul_re,← Complex.ofReal_ofNat,← Complex.ofReal_pow,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  rw [← hr] at hp
  exact (mul_pos_iff_of_pos_left (by positivity : (0:ℝ)<(6:ℝ)^26)).mp hp

end
end HTGeometry.ThetaRatioSource
