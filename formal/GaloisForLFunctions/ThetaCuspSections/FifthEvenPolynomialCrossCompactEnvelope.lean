import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleCompensationBounds
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad

/-!
# A quartic load envelope before the profile zero

The complete correction is positive before theta scale five and exceeds a
negative quartic scale bound afterward, up to the profile's double zero.
Likelihood moments control the full source and its derivative. Affine center
bounds give sharper polynomial reserves on the initial and middle intervals.
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

/-- At both endpoint slopes, expansion around two fifths leaves a positive quadratic remainder. -/
private theorem compactLoss_middle_bound {S x : ℝ}
    (hS0 : 8 ≤ S) (hS1 : S ≤ 45/4) (hx0 : 1/4 ≤ x) (hx1 : x ≤ 1/2) :
    compactLoss S x ≤ (13/40)*S := by
  let t := x-2/5
  have ht0 : -(3/20 : ℝ) ≤ t := by dsimp only [t]; linarith only [hx0]
  have ht1 : t ≤ (3/20 : ℝ) := by dsimp only [t]; linarith only [hx1]
  have ht2 : t^2 ≤ (9/400 : ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr ht1)
      (show 0 ≤ t+3/20 by linarith only [ht0])
    nlinarith only [h]
  have ht3 : t^3 ≤ (27/8000 : ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg t)
    nlinarith only [h,ht2]
  have hR0 : 0 ≤ 93/25+(32/5)*t-100*t^2-64*t^3 := by
    nlinarith only [ht0,ht2,ht3]
  have hR1 : 0 ≤ 182/25-(46/5)*t-152*t^2-90*t^3 := by
    nlinarith only [ht1,ht2,ht3]
  have hQ0 : 0 < 492/3125-(288/125)*t+39*t^2 := by
    nlinarith only [sq_nonneg (39*t-144/125)]
  have hQ1 : 0 < 229/20000+(87/250)*t+50*t^2 := by
    nlinarith only [sq_nonneg (50*t+87/500)]
  have he0 : (13/40)*8-compactLoss 8 x =
      492/3125-(288/125)*t+39*t^2+
        t^2*(93/25+(32/5)*t-100*t^2-64*t^3) := by
    dsimp only [compactLoss,t]
    ring
  have he1 : (13/40)*(45/4)-compactLoss (45/4) x =
      229/20000+(87/250)*t+50*t^2+
        t^2*(182/25-(46/5)*t-152*t^2-90*t^3) := by
    dsimp only [compactLoss,t]
    ring
  have hp0 : 0 ≤ (13/40)*8-compactLoss 8 x := by
    rw [he0]
    exact (add_pos_of_pos_of_nonneg hQ0 (mul_nonneg (sq_nonneg t) hR0)).le
  have hp1 : 0 ≤ (13/40)*(45/4)-compactLoss (45/4) x := by
    rw [he1]
    exact (add_pos_of_pos_of_nonneg hQ1 (mul_nonneg (sq_nonneg t) hR1)).le
  have ha := mul_nonneg (sub_nonneg.mpr hS1) hp0
  have hb := mul_nonneg (sub_nonneg.mpr hS0) hp1
  have he : (45/4-S)*((13/40)*8-compactLoss 8 x)+
      (S-8)*((13/40)*(45/4)-compactLoss (45/4) x) =
        (13/4)*((13/40)*S-compactLoss S x) := by
    unfold compactLoss
    ring
  nlinarith only [ha,hb,he]

/-- Near zero, the negative profile term pays the slope contribution. -/
private theorem compactLoss_lower_left {S x : ℝ}
    (hS0 : 8 ≤ S) (hS1 : S ≤ 45/4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/4) :
    compactLoss S x ≤ (13/40)*S := by
  have hx2 : x^2 ≤ (1/16 : ℝ) := by
    have h := mul_self_le_mul_self hx0 hx1
    nlinarith only [h]
  have hp0 : 0 ≤ 1-2*x^2 := by nlinarith only [hx2]
  have hp1 : 0 ≤ 1-(1-2*x^2) := by nlinarith only [sq_nonneg x]
  have hps : (1-2*x^2)^2 ≤ 1-2*x^2 := by
    nlinarith only [mul_nonneg hp0 hp1]
  have hb : 0 ≤ 2-4*(x^2+x/4+1/16) := by nlinarith only [hx2,hx1]
  have hprod := mul_nonneg (sub_nonneg.mpr hx1) hb
  have hcap : 2*x*(1-2*x^2) ≤ (7/16 : ℝ) := by nlinarith only [hprod]
  have hc : 2*x*(1-2*x^2)^2 ≤ (7/16 : ℝ) :=
    (mul_le_mul_of_nonneg_left hps (by linarith only [hx0])).trans hcap
  have hpiece : (1-2*x^2)*(14*x^2-3) ≤ -(119/64 : ℝ) := by
    have hA : 14*x^2-3 ≤ -(17/8 : ℝ) := by nlinarith only [hx2]
    have hP : (7/8 : ℝ) ≤ 1-2*x^2 := by nlinarith only [hx2]
    have h1 := mul_le_mul_of_nonneg_left hA hp0
    have h2 := mul_le_mul_of_nonpos_right hP (by norm_num : -(17/8 : ℝ) ≤ 0)
    nlinarith only [h1,h2]
  have h := mul_le_mul_of_nonneg_right hc (by linarith only [hS0] : 0 ≤ S)
  unfold compactLoss
  nlinarith only [h,hpiece,hS1]

/-- Beyond one half, the loss is at most one quarter of the slope plus four sevenths. -/
private theorem compactLoss_lower_right {S x : ℝ}
    (hS0 : 8 ≤ S) (hx0 : 1/2 ≤ x) (hx2 : x^2 ≤ 1/2) :
    compactLoss S x ≤ (13/40)*S := by
  have hx : 0 ≤ x := by linarith only [hx0]
  have hx1 : x ≤ 1 := by nlinarith only [hx2,sq_nonneg (x-1)]
  have hp0 : 0 ≤ 1-2*x^2 := by linarith only [hx2]
  have hp1 : 1-2*x^2 ≤ 1-x := by
    have h := mul_nonneg hx (show 0 ≤ 2*x-1 by linarith only [hx0])
    nlinarith only [h]
  have hs := mul_self_le_mul_self hp0 hp1
  have hb : 0 ≤ 2*x*(1-x)+x-1/2 := by
    have h := mul_nonneg (show 0 ≤ 2*x by linarith only [hx]) (sub_nonneg.mpr hx1)
    linarith only [h,hx0]
  have hprod := mul_nonneg (sub_nonneg.mpr hx0) hb
  have hcap : 2*x*(1-x)^2 ≤ (1/4 : ℝ) := by nlinarith only [hprod]
  have hsmall : (1-2*x^2)^2 ≤ (1-x)^2 := by nlinarith only [hs]
  have hc : 2*x*(1-2*x^2)^2 ≤ (1/4 : ℝ) :=
    (mul_le_mul_of_nonneg_left hsmall (by linarith only [hx])).trans hcap
  have hpiece : (1-2*x^2)*(14*x^2-3) ≤ (4/7 : ℝ) := by
    nlinarith only [sq_nonneg (x^2-5/14)]
  have h := mul_le_mul_of_nonneg_right hc (by linarith only [hS0] : 0 ≤ S)
  unfold compactLoss
  nlinarith only [h,hpiece,hS0]

/-- Affine interpolation in the slope combines the two endpoint polynomial bounds. -/
private theorem compactLoss_seven_upper {S x : ℝ}
    (hS0 : 8 ≤ S) (hS1 : S ≤ 45/4) (hx0 : 0 ≤ x) (hx2 : x^2 ≤ 1/2) :
    compactLoss S x ≤ (13/40)*S := by
  by_cases hl : x ≤ 1/4
  · exact compactLoss_lower_left hS0 hS1 hx0 hl
  by_cases hr : 1/2 ≤ x
  · exact compactLoss_lower_right hS0 hr hx2
  exact compactLoss_middle_bound hS0 hS1 (not_le.mp hl).le (not_le.mp hr).le

private theorem compact_seven_slope_bounds {q : ℝ} (hq : 7 ≤ q) (hu : q ≤ 8) :
    8 ≤ firstSlope q+1/100000 ∧ firstSlope q+1/100000 ≤ 45/4 := by
  have hd : 0 < 2*(2*q-3) := by linarith only [hq]
  constructor
  · have hl : 8-1/100000 ≤ firstSlope q := by
      unfold firstSlope
      apply (le_div_iff₀ hd).mpr
      nlinarith only [hq,sq_nonneg (q-7)]
    linarith only [hl]
  · have hl : firstSlope q ≤ 45/4-1/100000 := by
      unfold firstSlope
      apply (div_le_iff₀ hd).mpr
      have h := mul_nonneg (sub_nonneg.mpr hu)
        (show 0 ≤ 8*q-11 by linarith only [hq])
      nlinarith only [h,hu]
    linarith only [hl]

/-- The quartic scale allowance pays both the mass inflation and the derivative error. -/
private theorem compact_seven_quartic_gap {q : ℝ} (hq : 7 ≤ q) (hu : q ≤ 8) :
    (1000001/1000000)^2*(13/40)*(firstSlope q+1/100000)*(2*q-3)^2 <
      (3/20)*q^4 := by
  have hS := compact_seven_slope_bounds hq hu
  have hd : 0 < 2*q-3 := by linarith only [hq]
  have hs : (2*q-3)^2 ≤ (169 : ℝ) := by
    have h := mul_self_le_mul_self hd.le
      (show 2*q-3 ≤ (13 : ℝ) by linarith only [hu])
    nlinarith only [h]
  have hB0 : 0 ≤ (13/40)*(firstSlope q+1/100000)*(2*q-3)^2 := by
    have hSn : 0 ≤ firstSlope q+1/100000 := by linarith only [hS.1]
    positivity
  have hB1 : (13/40)*(firstSlope q+1/100000)*(2*q-3)^2 ≤ (1000 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hS.2 (sq_nonneg (2*q-3))
    have h2 := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ (13/40)*(45/4))
    nlinarith only [h1,h2]
  have hE : ((1000001/1000000 : ℝ)^2-1) ≤ 1/100000 := by norm_num
  have hEB := mul_le_mul_of_nonneg_right hE hB0
  have hB : (1000001/1000000)^2*((13/40)*(firstSlope q+1/100000)*(2*q-3)^2) ≤
      (13/40)*(firstSlope q+1/100000)*(2*q-3)^2+1/100 := by
    nlinarith only [hEB,hB1]
  have hc : (13/40)*(firstSlope q+1/100000)*(2*q-3)^2 =
      (13/80)*(8*q^2-30*q+15)*(2*q-3)+(13/4000000)*(2*q-3)^2 := by
    have hm : firstSlope q*(2*(2*q-3))=8*q^2-30*q+15 := by
      unfold firstSlope
      exact div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hd.ne')
    have hp := congrArg (fun y : ℝ => y*(2*q-3)) hm
    nlinarith only [hp]
  have hraw : (13/40)*(firstSlope q+1/100000)*(2*q-3)^2 ≤
      (13/80)*(8*q^2-30*q+15)*(2*q-3)+1/100 := by
    nlinarith only [hc,hs]
  have he : (3/20)*q^4-(13/80)*(8*q^2-30*q+15)*(2*q-3) =
      641/80-(24/5)*(q-7)+(63/20)*(q-7)^2+
        (8/5)*(q-7)^3+(3/20)*(q-7)^4 := by ring
  have ht : 0 ≤ q-7 := sub_nonneg.mpr hq
  have ht1 : q-7 ≤ 1 := by linarith only [hu]
  have hgap : (13/80)*(8*q^2-30*q+15)*(2*q-3)+1 < (3/20)*q^4 := by
    nlinarith only [he,ht1,sq_nonneg (q-7),pow_nonneg ht 3,pow_nonneg ht 4]
  nlinarith only [hB,hraw,hgap]

private theorem compensation_compact_seven_loss {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) :
    -compactLoss (firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000) x*
        thetaCuspFullSource x^2 ≤ compensation x := by
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith only [hq])
  have hF := thetaCuspFullSource_pos_all x
  have hS : 0 ≤ firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000 := by
    linarith only [(compact_seven_slope_bounds hq hu).1]
  have hm := mass_slope_bounds hq
  have hmass := mul_le_mul_of_nonneg_left hm.1 hS
  have hd : -(firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000)*
      thetaCuspFullSource x ≤ deriv thetaCuspFullSource x := by
    nlinarith only [hmass,hm.2.2]
  have hpay := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by positivity)
  dsimp only [compactLoss,compensation,thetaCuspCenterCompensationSource]
  nlinarith only [hpay]

/-- The complete quartic correction exceeds its quartic scale bound from scale seven. -/
theorem compensation_compact_quartic_lower_seven {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hx2 : x^2 ≤ 1/2) :
    -(3/20)*sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^4 < compensation x := by
  by_cases hu : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x
  · exact compensation_compact_quartic_lower hu hx2
  have hu8 := (not_le.mp hu).le
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith only [hq])
  let S := firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+1/100000
  have hS : 8 ≤ S ∧ S ≤ 45/4 := compact_seven_slope_bounds hq hu8
  have hT : 0 ≤ (13/40)*S := by linarith only [hS.1]
  have hm := mass_slope_bounds hq
  have hsq := mul_self_le_mul_self (thetaCuspFullSource_pos_all x).le hm.2.1
  have hmass := mul_le_mul_of_nonneg_left hsq hT
  have hJ := compactLoss_seven_upper hS.1 hS.2 hx.le hx2
  have hpay := mul_le_mul_of_nonneg_right hJ (sq_nonneg (thetaCuspFullSource x))
  have hcomp : -compactLoss S x*thetaCuspFullSource x^2 ≤ compensation x :=
    compensation_compact_seven_loss hq hu8
  have hlower : -(1000001/1000000)^2*((13/40)*S)*thetaCuspSourceTerm x 1^2 ≤
      compensation x := by nlinarith only [hcomp,hpay,hmass]
  rw [first_mass_square] at hlower
  have hgap := compact_seven_quartic_gap hq hu8
  have hK := FifthNativeRay.sourceUnit_pos (x := x) (by linarith only [hq])
  have hp := mul_lt_mul_of_pos_left hgap hK
  dsimp only [S] at hlower
  nlinarith only [hlower,hp]

/-- A quadratic floor controls the smallest slope throughout the compact profile. -/
private theorem compactLoss_halfSeven_upper {x : ℝ}
    (hx : 0 ≤ x) (hx2 : x^2 ≤ 1/2) :
    compactLoss (7/2) x ≤ (13/40)*(7/2) := by
  let t := x-1/2
  have ht0 : -(1/2 : ℝ) ≤ t := by dsimp only [t]; linarith only [hx]
  have ht1 : t ≤ (1/4 : ℝ) := by
    dsimp only [t]
    nlinarith only [hx2,sq_nonneg (x-3/4)]
  have htsq : t^2 ≤ (1/4 : ℝ) := by
    have h := mul_nonneg (show 0 ≤ 1/2-t by linarith only [ht1])
      (show 0 ≤ t+1/2 by linarith only [ht0])
    nlinarith only [h]
  have hR : 0 ≤ 1-t-t^2 := by linarith only [ht1,htsq]
  have hQ : 0 < 1/80-(3/4)*t+15*t^2 := by
    nlinarith only [sq_nonneg (15*t-3/8)]
  have hrest := mul_nonneg (sq_nonneg t)
    (mul_nonneg (show 0 ≤ t+1/2 by linarith only [ht0]) hR)
  have he : (13/40)*(7/2)-compactLoss (7/2) x =
      1/80-(3/4)*t+15*t^2+28*t^2*(t+1/2)*(1-t-t^2) := by
    dsimp only [compactLoss,t]
    ring
  nlinarith only [he,hQ,hrest]

/-- The loss bound persists between the small-slope quadratic and the slope-nine bound. -/
private theorem compactLoss_five_upper {S x : ℝ}
    (hS0 : 7/2 ≤ S) (hS1 : S ≤ 9) (hx : 0 ≤ x) (hx2 : x^2 ≤ 1/2) :
    compactLoss S x ≤ (13/40)*S := by
  have h0 := sub_nonneg.mpr (compactLoss_halfSeven_upper hx hx2)
  have h1 := sub_nonneg.mpr (compactLoss_seven_upper
    (by norm_num : (8 : ℝ) ≤ 9) (by norm_num : (9 : ℝ) ≤ 45/4) hx hx2)
  have ha := mul_nonneg (sub_nonneg.mpr hS1) h0
  have hb := mul_nonneg (sub_nonneg.mpr hS0) h1
  have he : (9-S)*((13/40)*(7/2)-compactLoss (7/2) x)+
      (S-7/2)*((13/40)*9-compactLoss 9 x) =
        (11/2)*((13/40)*S-compactLoss S x) := by
    unfold compactLoss
    ring
  nlinarith only [ha,hb,he]

private theorem compact_middle_first_derivative {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      -firstSlope (thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hd := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
  rw [iteratedDeriv_one] at hd
  have hj : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      Real.exp (x/2-q)*(-8*q^3+30*q^2-15*q) := by
    rw [hd]
    dsimp only [thetaCuspGaussianScaleJet,thetaCuspGaussianScaleMoment,q]
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,pow_one]
    ring
  rw [hj,thetaCuspSourceTerm_one_eq_scale_profile]
  change Real.exp (x/2-q)*(-8*q^3+30*q^2-15*q) =
    -firstSlope q*(Real.exp (x/2-q)*(4*q^2-6*q))
  have hden : 2*q-3 ≠ 0 := by dsimp only [q]; linarith only [hq]
  unfold firstSlope
  field_simp [hden]
  ring

/-- The full first likelihood moment controls both mass inflation and slope loss. -/
private theorem compact_middle_mass_slope {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFullSource x ≤ (501/500)*thetaCuspSourceTerm x 1 ∧
      -(firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+
        thetaCuspSingleAtomReflectionScale 1 x/250)*thetaCuspFullSource x ≤
          deriv thetaCuspFullSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let R := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0
  let M := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 1
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith only [hq]
  have hM : M ≤ 1/500 := thetaCuspHigherLikelihoodSpectralMoment_one_le_middle hqm
  have hR : R ≤ 1/500 :=
    (thetaCuspHigherLikelihoodSpectralMoment_zero_le_one hB).trans hM
  have hF : f ≤ F := (thetaCuspFullSource_mass_bounds_middle hqm).1
  have heF : F=f*(1+R) := by
    dsimp only [F,f,R]
    rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
      thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
  have hd : deriv thetaCuspFullSource x =
      -firstSlope q*F-2*q*f*M := by
    have hh := deriv_thetaCuspFullSource_eq_likelihood_moment hx
    rw [compact_middle_first_derivative hq] at hh
    change _ = (-firstSlope q*f)*(1+R)-2*q*f*M at hh
    rw [hh,heF]
    ring
  have htail := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2*q*f by positivity)
  have hmass := mul_le_mul_of_nonneg_left hF (show 0 ≤ q/250 by positivity)
  constructor
  · change F ≤ (501/500)*f
    rw [heF]
    nlinarith only [mul_le_mul_of_nonneg_left hR hf.le]
  · change -(firstSlope q+q/250)*F ≤ _
    linarith only [hd,htail,hmass]

private theorem compact_five_slope_bounds {q : ℝ} (hq : 5 ≤ q) (hu : q ≤ 7) :
    7/2 ≤ firstSlope q+q/250 ∧ firstSlope q+q/250 ≤ 9 := by
  have hd : 0 < 2*(2*q-3) := by linarith only [hq]
  have hl : 7/2 ≤ firstSlope q := by
    unfold firstSlope
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hq,sq_nonneg (q-5)]
  have hh : firstSlope q ≤ 9-7/250 := by
    unfold firstSlope
    apply (div_le_iff₀ hd).mpr
    have hp := mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ 8*q-10 by linarith only [hq])
    nlinarith only [hp,hu]
  constructor <;> linarith only [hl,hh,hq,hu]

private theorem compact_five_quartic_gap {q : ℝ} (hq : 5 ≤ q) (hu : q ≤ 7) :
    (501/500)^2*(13/40)*(firstSlope q+q/250)*(2*q-3)^2 < (3/20)*q^4 := by
  have hS := compact_five_slope_bounds hq hu
  have hd : 0 < 2*q-3 := by linarith only [hq]
  have hs : (2*q-3)^2 ≤ (121 : ℝ) := by
    have h := mul_self_le_mul_self hd.le (show 2*q-3 ≤ (11 : ℝ) by linarith only [hu])
    nlinarith only [h]
  have hB0 : 0 ≤ (13/40)*(firstSlope q+q/250)*(2*q-3)^2 := by
    have hSn : 0 ≤ firstSlope q+q/250 := by linarith only [hS.1]
    positivity
  have hB1 : (13/40)*(firstSlope q+q/250)*(2*q-3)^2 ≤ (400 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hS.2 (sq_nonneg (2*q-3))
    have h2 := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ (13/40)*9)
    nlinarith only [h1,h2]
  have hE : ((501/500 : ℝ)^2-1) ≤ 1/200 := by norm_num
  have hEB := mul_le_mul_of_nonneg_right hE hB0
  have hB : (501/500)^2*((13/40)*(firstSlope q+q/250)*(2*q-3)^2) ≤
      (13/40)*(firstSlope q+q/250)*(2*q-3)^2+2 := by
    nlinarith only [hEB,hB1]
  have hc : (13/40)*(firstSlope q+q/250)*(2*q-3)^2 =
      (13/80)*(8*q^2-30*q+15)*(2*q-3)+(13/10000)*q*(2*q-3)^2 := by
    have hm : firstSlope q*(2*(2*q-3))=8*q^2-30*q+15 := by
      unfold firstSlope
      exact div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hd.ne')
    have hp := congrArg (fun y : ℝ => y*(2*q-3)) hm
    nlinarith only [hp]
  have hqs := mul_le_mul hu hs (sq_nonneg (2*q-3)) (by norm_num : (0 : ℝ) ≤ 7)
  have hraw : (13/40)*(firstSlope q+q/250)*(2*q-3)^2 ≤
      (13/80)*(8*q^2-30*q+15)*(2*q-3)+2 := by
    nlinarith only [hc,hqs]
  let t := 7-q
  have ht : 0 ≤ t := by dsimp only [t]; linarith only [hu]
  have ht1 : t ≤ 2 := by dsimp only [t]; linarith only [hq]
  have ht2 : t^2 ≤ 4 := by
    have h := mul_self_le_mul_self ht ht1
    nlinarith only [h]
  have hnegative := mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg t)
  have he : (3/20)*q^4-(13/80)*(8*q^2-30*q+15)*(2*q-3) =
      641/80+(24/5)*t+(63/20)*t^2-(8/5)*t^3+(3/20)*t^4 := by
    dsimp only [t]
    ring
  have hgap : (13/80)*(8*q^2-30*q+15)*(2*q-3)+5 < (3/20)*q^4 := by
    nlinarith only [he,ht,ht2,hnegative,pow_nonneg ht 4]
  nlinarith only [hB,hraw,hgap]

/-- The complete compact quartic allowance holds from native positivity's scale five. -/
theorem compensation_compact_quartic_lower_five {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hx2 : x^2 ≤ 1/2) :
    -(3/20)*sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^4 < compensation x := by
  by_cases hu : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x
  · exact compensation_compact_quartic_lower_seven hu hx2
  have hu7 := (not_le.mp hu).le
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  let S := firstSlope (thetaCuspSingleAtomReflectionScale 1 x)+
    thetaCuspSingleAtomReflectionScale 1 x/250
  have hS : 7/2 ≤ S ∧ S ≤ 9 := compact_five_slope_bounds hq hu7
  have hT : 0 ≤ (13/40)*S := by linarith only [hS.1]
  have hm := compact_middle_mass_slope (x := x) (by linarith only [hq])
  have hsq := mul_self_le_mul_self (thetaCuspFullSource_pos_all x).le hm.1
  have hmass := mul_le_mul_of_nonneg_left hsq hT
  have hJ := compactLoss_five_upper hS.1 hS.2 hx.le hx2
  have hpay := mul_le_mul_of_nonneg_right hJ (sq_nonneg (thetaCuspFullSource x))
  have hcomp : -compactLoss S x*thetaCuspFullSource x^2 ≤ compensation x := by
    have hd := mul_le_mul_of_nonneg_left hm.2
      (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by
        exact mul_nonneg (by positivity) (thetaCuspFullSource_pos_all x).le)
    dsimp only [compactLoss,compensation,thetaCuspCenterCompensationSource,S]
    nlinarith only [hd]
  have hlower : -(501/500)^2*((13/40)*S)*thetaCuspSourceTerm x 1^2 ≤
      compensation x := by nlinarith only [hcomp,hpay,hmass]
  rw [first_mass_square] at hlower
  have hgap := compact_five_quartic_gap hq hu7
  have hK := FifthNativeRay.sourceUnit_pos hq
  have hp := mul_lt_mul_of_pos_left hgap hK
  dsimp only [S] at hlower
  nlinarith only [hlower,hp]

private theorem compactLoss_derivative_nonneg {S x : ℝ}
    (hS0 : 0 ≤ S) (hS1 : S ≤ 9) (hx : 0 ≤ x) (hxu : x ≤ 41/100) :
    0 ≤ -2*(1-2*x^2)*(10*x^2-1)*S+8*x*(5-14*x^2) := by
  have hx2 : x^2 ≤ (1681/10000 : ℝ) := by
    have h := mul_self_le_mul_self hx hxu
    nlinarith only [h]
  have hP : 0 ≤ 1-2*x^2 := by linarith only [hx2]
  have hW : 0 ≤ 5-14*x^2 := by linarith only [hx2]
  by_cases hb : 10*x^2 ≤ 1
  · have hp := mul_nonneg (mul_nonneg hP (show 0 ≤ 1-10*x^2 by linarith only [hb])) hS0
    have hq := mul_nonneg hx hW
    nlinarith only [hp,hq]
  · have hxl : 3/10 ≤ x := by
      by_contra h
      have hp := mul_nonneg
        (show 0 ≤ 3/10-x by linarith only [not_le.mp h])
        (show 0 ≤ 3/10+x by linarith only [hx])
      nlinarith only [not_le.mp hb,hp]
    have hc : (90 : ℝ) ≤ 216-360*(x^2+(41/100)^2) := by
      nlinarith only [hx2]
    have hxc : (7/10 : ℝ) ≤ x+41/100 := by linarith only [hxl]
    have hm := mul_le_mul hxc hc (by norm_num : (0 : ℝ) ≤ 90)
      (show 0 ≤ x+41/100 by linarith only [hx])
    have hquad : 0 ≤ x^2+x*(41/100)+(41/100)^2 := by positivity
    have hbracket : 0 ≤ (x+41/100)*(216-360*(x^2+(41/100)^2))-40+
        112*(x^2+x*(41/100)+(41/100)^2) := by nlinarith only [hm,hquad]
    have hprod := mul_nonneg (sub_nonneg.mpr hxu) hbracket
    have hD : 0 ≤ 18+40*x-216*x^2-112*x^3+360*x^4 := by
      nlinarith only [hprod]
    have hS := mul_le_mul_of_nonneg_left hS1
      (show 0 ≤ 2*(1-2*x^2)*(10*x^2-1) by
        exact mul_nonneg (mul_nonneg (by norm_num) hP) (by linarith only [not_le.mp hb]))
    nlinarith only [hS,hD]

private theorem compactLoss_monotone_middle {S : ℝ} (hS0 : 0 ≤ S) (hS1 : S ≤ 9) :
    MonotoneOn (compactLoss S) (Icc 0 (41/100)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (f' := fun x => -2*(1-2*x^2)*(10*x^2-1)*S+8*x*(5-14*x^2)) ?_ ?_ ?_
  · intro x _
    exact (compactLoss_hasDerivAt S x).continuousAt.continuousWithinAt
  · intro x _
    exact (compactLoss_hasDerivAt S x).hasDerivWithinAt
  · intro x hx
    have hh := interior_subset hx
    exact compactLoss_derivative_nonneg hS0 hS1 hh.1 hh.2

private theorem compact_middle_slope_lower {q : ℝ} (hq : 5 ≤ q) :
    816/175 ≤ firstSlope q+q/250 := by
  have hd : 0 < 2*(2*q-3) := by linarith only [hq]
  have hf : 65/14 ≤ firstSlope q := by
    unfold firstSlope
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hq,sq_nonneg (q-5)]
  linarith only [hf,hq]

private theorem compact_middle_loss_pos {q : ℝ} (hq : 5 ≤ q) (hu : q ≤ 7) :
    0 < compactLoss (firstSlope q+q/250) (q/14-99/1000) := by
  have hT0 : (1807/7000 : ℝ) ≤ q/14-99/1000 := by linarith only [hq]
  have hT1 : q/14-99/1000 ≤ (41/100 : ℝ) := by linarith only [hu]
  have hTn : 0 ≤ q/14-99/1000 := by linarith only [hT0]
  have hbase : 0 < compactLoss (816/175) (1807/7000) := by norm_num [compactLoss]
  have hx := compactLoss_monotone_middle
    (by norm_num : (0 : ℝ) ≤ 816/175) (by norm_num : (816/175 : ℝ) ≤ 9)
    (by constructor <;> norm_num : (1807/7000 : ℝ) ∈ Icc 0 (41/100))
    ⟨hTn,hT1⟩ hT0
  have hS := mul_le_mul_of_nonneg_left (compact_middle_slope_lower hq)
    (show 0 ≤ 2*(q/14-99/1000)*(1-2*(q/14-99/1000)^2)^2 by positivity)
  unfold compactLoss at hbase hx ⊢
  nlinarith only [hbase,hx,hS]

/-- A polynomial allowance retaining the affine center bound on scales five through seven. -/
def compactMiddleAllowance (q : ℝ) : ℝ :=
  let t := q/14-99/1000
  let p := 1-2*t^2
  (501/500)^2*(t*p^2*(8*q^2-30*q+15)*(2*q-3)+
    ((q/125)*t*p^2+p*(14*t^2-3))*(2*q-3)^2)

private theorem compactMiddleAllowance_eq {q : ℝ} (hq : 5 ≤ q) :
    compactMiddleAllowance q = (501/500)^2*
      compactLoss (firstSlope q+q/250) (q/14-99/1000)*(2*q-3)^2 := by
  have hd : 2*q-3 ≠ 0 := by linarith only [hq]
  unfold compactMiddleAllowance compactLoss firstSlope
  generalize q/14-99/1000 = t
  field_simp [hd]
  ring

/-- The complete quartic correction keeps the center-dependent polynomial allowance. -/
theorem compensation_compact_middle_lower {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hu : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    -compactMiddleAllowance (thetaCuspSingleAtomReflectionScale 1 x)*sourceUnit x ≤
      compensation x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let S := firstSlope q+q/250
  let T := q/14-99/1000
  have hx := thetaCusp_pos_of_thirtySevenTenths_le
    (show 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])
  have hS : 7/2 ≤ S ∧ S ≤ 9 := compact_five_slope_bounds hq hu
  have hxT : x ≤ T := by
    have ht := center_tangent hx.le
    dsimp only [T,q]
    linarith only [ht]
  have hTu : T ≤ (41/100 : ℝ) := by dsimp only [T,q]; linarith only [hu]
  have hTn : 0 ≤ T := hx.le.trans hxT
  have hL : 0 ≤ compactLoss S T := (compact_middle_loss_pos hq hu).le
  have hJ : compactLoss S x ≤ compactLoss S T :=
    compactLoss_monotone_middle (by linarith only [hS.1]) hS.2
      ⟨hx.le,hxT.trans hTu⟩ ⟨hTn,hTu⟩ hxT
  have hm := compact_middle_mass_slope (x := x) (by linarith only [hq])
  have hsq := mul_self_le_mul_self (thetaCuspFullSource_pos_all x).le hm.1
  have hmass := mul_le_mul_of_nonneg_left hsq hL
  have hpay := mul_le_mul_of_nonneg_right hJ (sq_nonneg (thetaCuspFullSource x))
  have hcomp : -compactLoss S x*thetaCuspFullSource x^2 ≤ compensation x := by
    have hd := mul_le_mul_of_nonneg_left hm.2
      (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by
        exact mul_nonneg (by positivity) (thetaCuspFullSource_pos_all x).le)
    dsimp only [compactLoss,compensation,thetaCuspCenterCompensationSource,S,q]
    nlinarith only [hd]
  have hlower : -(501/500)^2*compactLoss S T*thetaCuspSourceTerm x 1^2 ≤
      compensation x := by nlinarith only [hcomp,hpay,hmass]
  rw [first_mass_square] at hlower
  have he : compactMiddleAllowance q = (501/500)^2*compactLoss S T*(2*q-3)^2 :=
    compactMiddleAllowance_eq hq
  change -compactMiddleAllowance q*sourceUnit x ≤ _
  rw [he]
  change -(501/500)^2*compactLoss S T*(sourceUnit x*(2*q-3)^2) ≤ _ at hlower
  nlinarith only [hlower]

private theorem compact_lower_middle_slope_bounds {q : ℝ}
    (hq : 37/10 ≤ q) (hu : q ≤ 5) :
    0 ≤ firstSlope q+q/250 ∧ firstSlope q+q/250 ≤ 75/16 := by
  have hd : 0 < 2*(2*q-3) := by linarith only [hq]
  have hl : 0 ≤ firstSlope q := by
    unfold firstSlope
    apply div_nonneg ?_ hd.le
    nlinarith only [hq,sq_nonneg (q-37/10)]
  have hh : firstSlope q ≤ 65/14 := by
    unfold firstSlope
    apply (div_le_iff₀ hd).mpr
    have hp := mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ 8*q-60/7 by linarith only [hq])
    nlinarith only [hp]
  constructor <;> linarith only [hl,hh,hq,hu]

/-- The complete quartic correction remains positive across the lower middle scales. -/
theorem compensation_lower_middle_positive {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    thetaCuspFullSource x^2/16 ≤ compensation x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let S := firstSlope q+q/250
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hxu := center_le_quarter_of_firstAtomScale_le_five hu
  have hS : 0 ≤ S ∧ S ≤ 75/16 := compact_lower_middle_slope_bounds hq hu
  have hJ : compactLoss S x ≤ compactLoss S (1/4) :=
    compactLoss_monotone_middle hS.1 (by linarith only [hS.2])
      ⟨hx.le,by linarith only [hxu]⟩ (by constructor <;> norm_num) hxu
  have hpiece : compactLoss S (1/4) ≤ -(1/16 : ℝ) := by
    norm_num [compactLoss]
    nlinarith only [hS.2]
  have hpay := mul_le_mul_of_nonneg_right (hJ.trans hpiece)
    (sq_nonneg (thetaCuspFullSource x))
  have hm := compact_middle_mass_slope hq
  have hd := mul_le_mul_of_nonneg_left hm.2
    (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by
      exact mul_nonneg (by positivity) (thetaCuspFullSource_pos_all x).le)
  dsimp only [compactLoss,S,q] at hpay
  dsimp only [compensation,thetaCuspCenterCompensationSource]
  nlinarith only [hpay,hd]

private theorem compact_initial_slope_lower {x : ℝ} (hx : 0 < x)
    (hq : thetaCuspSingleAtomReflectionScale 1 x ≤ 37/10) :
    -3*thetaCuspFullSource x ≤ deriv thetaCuspFullSource x := by
  let s := thetaCuspMorseScale 1 x
  let q := thetaCuspBornWittenWeight 1 x
  have hsq : q=s-3/2 := thetaCuspBornWittenWeight_eq 1 x
  have hs : 3 ≤ s := le_trans Real.pi_gt_three.le
    (thetaCuspMorseScale_pi_le (by norm_num) hx.le)
  have hq0 : 0 < q := by linarith only [hs,hsq]
  have hfirst : thetaCuspFirstAtomLogJetOne x = -2*s+9/2+3*q⁻¹ := by
    dsimp only [thetaCuspFirstAtomLogJetOne,thetaCuspBornWittenSuperpotential,
      thetaCuspMorseSuperpotential]
    change -2*(s-5/4-s/q)=_
    rw [show s=q+3/2 by linarith only [hsq]]
    field_simp [hq0.ne']
    ring
  have hden : 1 ≤ 1+thetaCuspHigherToFirstAtomLikelihoodRatio x := by
    linarith only [thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx]
  have hdenpos : 0 < 1+thetaCuspHigherToFirstAtomLikelihoodRatio x := by
    linarith only [hden]
  have htail : |thetaCuspHigherLikelihoodLogJetOne x| ≤ 1/10 := by
    rw [thetaCuspHigherLikelihoodLogJetOne,abs_div,abs_of_pos hdenpos]
    exact (div_le_self (abs_nonneg _) hden).trans
      (abs_thetaCuspHigherLikelihoodJetOne_lt hx).le
  have hscale : s=thetaCuspSingleAtomReflectionScale 1 x := by
    simp only [s,thetaCuspMorseScale,thetaCuspSingleAtomReflectionScale,
      Nat.cast_one,one_pow,mul_one,one_mul,← Real.exp_nat_mul,Nat.cast_ofNat]
  have he := iteratedDeriv_one_thetaCuspLogSource_eq_full_jets hx
  rw [iteratedDeriv_one,(hasDerivAt_thetaCuspLogSource x).deriv,
    iteratedDeriv_one,hfirst] at he
  have hl : -3 ≤ deriv thetaCuspFullSource x/thetaCuspFullSource x := by
    rw [he]
    have hi := inv_nonneg.mpr hq0.le
    have ht := (abs_le.mp htail).1
    rw [← hscale] at hq
    linarith only [hq,hi,ht]
  exact (le_div_iff₀ (thetaCuspFullSource_pos_all x)).mp hl

private theorem compact_initial_center_upper {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x ≤ 37/10) : x ≤ 1/10 := by
  by_contra h
  have he := Real.add_one_le_exp (2*x)
  have hp := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hx : 1/10 < x := not_le.mp h
  have hprod := mul_pos
    (show 0 < Real.pi-31/10 by linarith only [Real.pi_gt_d2])
    (show 0 < 2*x+1 by linarith only [hx])
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one] at hq
  nlinarith only [hp,hq,hx,hprod]

/-- The quartic correction retains two source squares before theta scale thirty-seven tenths. -/
theorem compensation_initial_positive {x : ℝ} (hx : 0 ≤ x)
    (hq : thetaCuspSingleAtomReflectionScale 1 x ≤ 37/10) :
    2*thetaCuspFullSource x^2 ≤ compensation x := by
  by_cases hz : x=0
  · subst x
    simp only [compensation,thetaCuspCenterCompensationSource,mul_zero,zero_mul,add_zero]
    nlinarith only [sq_nonneg (thetaCuspFullSource 0)]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hxu := compact_initial_center_upper hq
  have hJ : compactLoss 3 x ≤ compactLoss 3 (1/10) :=
    compactLoss_monotone_middle (by norm_num) (by norm_num)
      ⟨hx,by linarith only [hxu]⟩ (by constructor <;> norm_num) hxu
  have hb : compactLoss 3 (1/10) ≤ -(2 : ℝ) := by norm_num [compactLoss]
  have hpay := mul_le_mul_of_nonneg_right (hJ.trans hb)
    (sq_nonneg (thetaCuspFullSource x))
  have hd := mul_le_mul_of_nonneg_left (compact_initial_slope_lower hxp hq)
    (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by
      exact mul_nonneg (by positivity) (thetaCuspFullSource_pos_all x).le)
  dsimp only [compactLoss] at hpay
  dsimp only [compensation,thetaCuspCenterCompensationSource]
  nlinarith only [hpay,hd]

/-- The quartic correction is positive throughout the interval before native scale five. -/
theorem compensation_before_five_positive {x : ℝ} (hx : 0 ≤ x)
    (hq : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    thetaCuspFullSource x^2/16 ≤ compensation x := by
  by_cases hm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x
  · exact compensation_lower_middle_positive hm hq
  · have h := compensation_initial_positive hx (not_le.mp hm).le
    nlinarith only [h,sq_nonneg (thetaCuspFullSource x)]

private theorem compact_initial_tangent {x : ℝ} (hx : 0 ≤ x) :
    x ≤ (25/157)*thetaCuspSingleAtomReflectionScale 1 x-1/2 := by
  have hpi : (157/50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have hp := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ 2*x+1 by linarith only [hx])
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*x)) Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
  nlinarith only [hp,he]

private theorem compact_first_square_le_full {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x 1^2 ≤ thetaCuspFullSource x^2 := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  have hP := one_le_thetaCuspLikelihoodPartition hB
  have hs := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hP
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,mul_pow]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (thetaCuspSourceTerm x 1))
  nlinarith only [hm]

/-- A positive polynomial reserve retaining the center's distance from the origin. -/
def compactInitialReserve (q : ℝ) : ℝ :=
  let t := (25/157)*q-1/2;
  -(6*t*(1-2*t^2)^2+(1-2*t^2)*(14*t^2-3))*(2*q-3)^2

/-- Before scale thirty-seven tenths, the correction pays the initial polynomial reserve. -/
theorem compensation_initial_polynomial_lower {x : ℝ} (hx : 0 ≤ x)
    (hq : thetaCuspSingleAtomReflectionScale 1 x ≤ 37/10) :
    compactInitialReserve (thetaCuspSingleAtomReflectionScale 1 x)*sourceUnit x ≤
      compensation x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let T := (25/157)*q-1/2
  have hxT : x ≤ T := compact_initial_tangent hx
  have hT0 : 0 ≤ T := hx.trans hxT
  have hT1 : T ≤ (1/10 : ℝ) := by dsimp only [T,q]; linarith only [hq]
  have hmono := compactLoss_monotone_middle
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) ≤ 9)
  have hJ := hmono ⟨hx,by linarith only [hxT,hT1]⟩
    ⟨hT0,by linarith only [hT1]⟩ hxT
  have hJu := hmono ⟨hT0,by linarith only [hT1]⟩
    (by constructor <;> norm_num : (1/10 : ℝ) ∈ Icc 0 (41/100)) hT1
  have hJneg : compactLoss 3 T ≤ -(2 : ℝ) :=
    hJu.trans (by norm_num [compactLoss])
  have hbase : -compactLoss 3 x*thetaCuspFullSource x^2 ≤ compensation x := by
    by_cases hz : x=0
    · subst x
      simp [compactLoss,compensation,thetaCuspCenterCompensationSource]
    · have hd := mul_le_mul_of_nonneg_left
        (compact_initial_slope_lower (lt_of_le_of_ne hx (Ne.symm hz)) hq)
        (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by
          exact mul_nonneg (by positivity) (thetaCuspFullSource_pos_all x).le)
      dsimp only [compactLoss,compensation,thetaCuspCenterCompensationSource]
      nlinarith only [hd]
  have hpay := mul_le_mul_of_nonneg_right hJ (sq_nonneg (thetaCuspFullSource x))
  have hmass := mul_le_mul_of_nonneg_left (compact_first_square_le_full hx)
    (show 0 ≤ -compactLoss 3 T by linarith only [hJneg])
  rw [first_mass_square] at hmass
  have he : compactInitialReserve q = -compactLoss 3 T*(2*q-3)^2 := by
    dsimp only [compactInitialReserve,compactLoss,T]
    ring
  change compactInitialReserve q*sourceUnit x ≤ _
  rw [he]
  change -compactLoss 3 T*(sourceUnit x*(2*q-3)^2) ≤ _ at hmass
  nlinarith only [hbase,hpay,hmass]

/-- A cubic positive reserve obtained from the quarter-center bound. -/
def compactLowerReserve (q : ℝ) : ℝ :=
  (119/64)*(2*q-3)^2-(49/256)*(8*q^2-30*q+15)*(2*q-3)-
    (49/32000)*q*(2*q-3)^2

private theorem compactLowerReserve_eq {q : ℝ} (hq : 37/10 ≤ q) :
    compactLowerReserve q = -compactLoss (firstSlope q+q/250) (1/4)*(2*q-3)^2 := by
  have hd : 2*q-3 ≠ 0 := by linarith only [hq]
  unfold compactLowerReserve compactLoss firstSlope
  field_simp [hd]
  ring

/-- The complete correction pays a cubic reserve on scales thirty-seven tenths through five. -/
theorem compensation_lower_polynomial_lower {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    compactLowerReserve (thetaCuspSingleAtomReflectionScale 1 x)*sourceUnit x ≤
      compensation x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let S := firstSlope q+q/250
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hxu := center_le_quarter_of_firstAtomScale_le_five hu
  have hS : 0 ≤ S ∧ S ≤ 75/16 := compact_lower_middle_slope_bounds hq hu
  have hJ : compactLoss S x ≤ compactLoss S (1/4) :=
    compactLoss_monotone_middle hS.1 (by linarith only [hS.2])
      ⟨hx.le,by linarith only [hxu]⟩ (by constructor <;> norm_num) hxu
  have hJneg : compactLoss S (1/4) ≤ -(1/16 : ℝ) := by
    norm_num [compactLoss]
    nlinarith only [hS.2]
  have hm := compact_middle_mass_slope hq
  have hd := mul_le_mul_of_nonneg_left hm.2
    (show 0 ≤ 2*x*(1-2*x^2)^2*thetaCuspFullSource x by
      exact mul_nonneg (by positivity) (thetaCuspFullSource_pos_all x).le)
  have hbase : -compactLoss S x*thetaCuspFullSource x^2 ≤ compensation x := by
    dsimp only [compactLoss,compensation,thetaCuspCenterCompensationSource,S,q]
    nlinarith only [hd]
  have hpay := mul_le_mul_of_nonneg_right hJ (sq_nonneg (thetaCuspFullSource x))
  have hmass := mul_le_mul_of_nonneg_left (compact_first_square_le_full hx.le)
    (show 0 ≤ -compactLoss S (1/4) by linarith only [hJneg])
  rw [first_mass_square] at hmass
  change compactLowerReserve q*sourceUnit x ≤ _
  rw [compactLowerReserve_eq hq]
  change -compactLoss S (1/4)*(sourceUnit x*(2*q-3)^2) ≤ _ at hmass
  nlinarith only [hbase,hpay,hmass]

end GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
