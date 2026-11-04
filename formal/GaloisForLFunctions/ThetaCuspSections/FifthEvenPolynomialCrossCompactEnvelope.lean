import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad

/-!
# A quartic load envelope before the profile zero

From theta scale eight to the quartic profile's double zero, the complete
compensation lies strictly above a negative quartic in the reflection scale.
The logarithmic derivative bound controls the full source; a decreasing
polynomial in the center gives the uniform scalar comparison.
-/

noncomputable section
open Matrix Set RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
open FifthCrossEnvelope FifthRemainder

private def compactLoss (S x : ℝ) : ℝ :=
  2*x*(1-2*x^2)^2*S+(1-2*x^2)*(14*x^2-3)

private theorem compactLoss_hasDerivAt (S x : ℝ) :
    HasDerivAt (compactLoss S)
      (-2*(1-2*x^2)*(10*x^2-1)*S+8*x*(5-14*x^2)) x := by
  have hp : HasDerivAt (fun y : ℝ => 1-2*y^2) (-4*x) x := by
    exact ((hasDerivAt_const x (1 : ℝ)).sub
      (((hasDerivAt_id x).pow 2).const_mul 2)).congr_deriv (by dsimp; ring)
  have hq : HasDerivAt (fun y : ℝ => 14*y^2-3) (28*x) x := by
    exact ((((hasDerivAt_id x).pow 2).const_mul 14).sub
      (hasDerivAt_const x (3 : ℝ))).congr_deriv (by dsimp; ring)
  have h := ((((hasDerivAt_id x).const_mul 2).mul (hp.pow 2)).mul
    (hasDerivAt_const x S)).add (hp.mul hq)
  exact h.congr_deriv (by dsimp; ring)

private theorem compactLoss_derivative_nonpos {S x : ℝ}
    (hS : 11 ≤ S) (hx : 7/15 ≤ x) (hx2 : x^2 ≤ 1/2) :
    -2*(1-2*x^2)*(10*x^2-1)*S+8*x*(5-14*x^2) ≤ 0 := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hxl := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7/15) hx
  have hp : 0 ≤ 1-2*x^2 := by linarith only [hx2]
  have ht : 0 ≤ 10*x^2-1 := by nlinarith only [hxl]
  have hS0 : 0 ≤ S := by linarith only [hS]
  by_cases hz : 5/14 ≤ x^2
  · have hn := mul_nonneg (mul_nonneg hp ht) hS0
    have hu := mul_nonpos_of_nonneg_of_nonpos hx0
      (show 5-14*x^2 ≤ 0 by linarith only [hz])
    nlinarith only [hn,hu]
  · have hp' : (2/7 : ℝ) ≤ 1-2*x^2 := by linarith only [lt_of_not_ge hz]
    have ht' : (53/45 : ℝ) ≤ 10*x^2-1 := by nlinarith only [hxl]
    have hprod := mul_le_mul hp' ht' (by norm_num : (0 : ℝ) ≤ 53/45) hp
    have hmain := mul_le_mul hprod hS (by norm_num : (0 : ℝ) ≤ 11) (mul_nonneg hp ht)
    have hxa := mul_le_mul_of_nonneg_right hx (by norm_num : (0 : ℝ) ≤ 7/15)
    have hcoef : 0 ≤ 14*(x^2+x*(7/15)+(7/15)^2)-5 := by
      nlinarith only [hxl,hxa]
    have hfact := mul_nonneg (sub_nonneg.mpr hx) hcoef
    have he : (7/15)*(5-14*(7/15)^2)-x*(5-14*x^2) =
        (x-7/15)*(14*(x^2+x*(7/15)+(7/15)^2)-5) := by ring
    rw [← he] at hfact
    nlinarith only [hmain,hfact]

end GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
