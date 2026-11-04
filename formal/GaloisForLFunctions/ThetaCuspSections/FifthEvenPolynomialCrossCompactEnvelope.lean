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

private theorem compact_center_lower {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) : 7/15 ≤ x := by
  have hc := EightCrossSource.center_scale
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one] at hc hq
  have he : Real.exp (2*EightCrossSource.center) ≤ Real.exp (2*x) := by
    by_contra h
    have hp := mul_pos Real.pi_pos (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hp,hc,hq]
  have h := Real.exp_le_exp.mp he
  linarith only [h,EightCrossSource.center_bounds.1]

private theorem compact_slope_bounds {q : ℝ} (hq : 8 ≤ q) :
    11 ≤ firstSlope q+1/100000 ∧
      firstSlope q+1/100000 ≤ 2*q-9/2+1/100000 := by
  have hd : 0 < 2*(2*q-3) := by linarith only [hq]
  have hl : 11 ≤ firstSlope q := by
    unfold firstSlope
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hq,sq_nonneg (q-8)]
  have hu : firstSlope q ≤ 2*q-9/2 := by
    unfold firstSlope
    apply (div_le_iff₀ hd).mpr
    nlinarith only []
  constructor <;> linarith only [hl,hu]

private theorem compact_quartic_gap {q : ℝ} (hq : 8 ≤ q) :
    ((61/100)*q-13/10)*(2*q-3)^2 < (3/20)*q^4 := by
  have he : (3/20)*q^4-((61/100)*q-13/10)*(2*q-3)^2 =
      469/50+(359/20)*(q-8)+(289/25)*(q-8)^2+
        (59/25)*(q-8)^3+(3/20)*(q-8)^4 := by ring
  have hu : 0 ≤ q-8 := sub_nonneg.mpr hq
  have hp2 : 0 ≤ (q-8)^2 := sq_nonneg _
  have hp3 : 0 ≤ (q-8)^3 := pow_nonneg hu _
  have hp4 : 0 ≤ (q-8)^4 := pow_nonneg hu _
  nlinarith only [he,hu,hp2,hp3,hp4]

private theorem compensation_compact_loss_lower {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -compactLoss (firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000) x*
        thetaCuspFullSource x^2 ≤ compensation x := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith only [hq])
  have hF := thetaCuspFullSource_pos_all x
  have hS : 0 ≤ firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000 := by
    linarith only [(compact_slope_bounds hq).1]
  have hm := mass_slope_bounds (x := x) (by linarith only [hq])
  have hmass := mul_le_mul_of_nonneg_left hm.1 hS
  have hd : -(firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000)*
      thetaCuspFullSource x ≤ deriv thetaCuspFullSource x := by
    nlinarith only [hmass,hm.2.2]
  have hpay := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by positivity)
  dsimp only [compactLoss,compensation,thetaCuspCenterCompensationSource]
  nlinarith only [hpay]

private theorem compactLoss_upper {S x : ℝ}
    (hS : 11 ≤ S) (hx : 7/15 ≤ x) (hx2 : x^2 ≤ 1/2) :
    compactLoss S x ≤ (3/10)*S+7/250 := by
  have ha : AntitoneOn (compactLoss S) (Icc (7/15) x) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun y => -2*(1-2*y^2)*(10*y^2-1)*S+8*y*(5-14*y^2)) ?_ ?_ ?_
    · intro y _
      exact (compactLoss_hasDerivAt S y).continuousAt.continuousWithinAt
    · intro y _
      exact (compactLoss_hasDerivAt S y).hasDerivWithinAt
    · intro y hy
      have hyc := interior_subset hy
      have hy0 : 0 ≤ y := by linarith only [hyc.1]
      have hysq := mul_self_le_mul_self hy0 hyc.2
      exact compactLoss_derivative_nonpos hS hyc.1 (by nlinarith only [hysq,hx2])
  calc
    compactLoss S x ≤ compactLoss S (7/15) := ha ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
    _ ≤ (3/10)*S+7/250 := by
      dsimp only [compactLoss]
      nlinarith only [hS]

private theorem compensation_compact_affine_lower {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hx2 : x^2 ≤ 1/2) :
    -((61/100)*thetaCuspSingleAtomReflectionScale 1 x-13/10)*sourceUnit x*
        (2*thetaCuspSingleAtomReflectionScale 1 x-3)^2 ≤ compensation x := by
  let S := firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000
  have hS : 11 ≤ S ∧ S ≤ 2*thetaCuspSingleAtomReflectionScale 1 x-9/2+1/100000 :=
    compact_slope_bounds hq
  have hL : 0 ≤ (3/10)*S+7/250 := by linarith only [hS.1]
  have hm := mass_slope_bounds (x := x) (by linarith only [hq])
  have hsq := mul_self_le_mul_self (thetaCuspFullSource_pos_all x).le hm.2.1
  have hmass := mul_le_mul_of_nonneg_left hsq hL
  have hloss := compactLoss_upper hS.1 (compact_center_lower hq) hx2
  have hpay := mul_le_mul_of_nonneg_right hloss (sq_nonneg (thetaCuspFullSource x))
  have hc : ((3/10)*S+7/250)*(1000001/1000000)^2 ≤
      (61/100)*thetaCuspSingleAtomReflectionScale 1 x-13/10 := by
    nlinarith only [hS.2,hq]
  have hcoeff := mul_le_mul_of_nonneg_right hc (sq_nonneg (thetaCuspSourceTerm x 1))
  have hcomp : -compactLoss S x*thetaCuspFullSource x^2 ≤ compensation x :=
    compensation_compact_loss_lower hq
  have hlower : -((61/100)*thetaCuspSingleAtomReflectionScale 1 x-13/10)*
      thetaCuspSourceTerm x 1^2 ≤ compensation x := by
    nlinarith only [hcomp,hpay,hmass,hcoeff]
  rw [first_mass_square] at hlower
  nlinarith only [hlower]

/-- Before the profile zero, the complete compensation exceeds the quartic load envelope. -/
theorem compensation_compact_quartic_lower {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hx2 : x^2 ≤ 1/2) :
    -(3/20)*sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^4 < compensation x := by
  have haff := compensation_compact_affine_lower hq hx2
  have hgap := compact_quartic_gap hq
  have hK := FifthNativeRay.sourceUnit_pos (x := x) (by linarith only [hq])
  have hp := mul_lt_mul_of_pos_left hgap hK
  nlinarith only [haff,hp]

end GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
