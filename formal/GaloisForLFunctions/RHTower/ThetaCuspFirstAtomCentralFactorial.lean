import GaloisForLFunctions.RHTower.ThetaCuspEffectiveFirstAtomJets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomGaussianJetLimits
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomScaleSevenProfiles

/-!
# First-atom central-factorial middle reserve

The literal first theta atom has a finite central-factorial normal form through
reflection order twelve. With q = pi exp(2x), its central moments are a Gaussian
moment sequence multiplied by the affine factor 1 + 6n/(2q-3)^2. A triangular
change of the four even polynomial coordinates makes the quantitative source
comparison small enough to prove by explicit positive polynomial decompositions.

The raw first-atom energy retains 196 f1^2 (8q)^6 in its squared leading
coefficient for q >= 7/2, and 282 for q >= 4. On x >= 0 and q >= 4, the literal
fixed correction 10^12 (3 f1^2 + 2x f1 f1') leaves four coordinate reserves
1, 7/8, 3, and 82. These are first-atom statements; the unequal-atom and full-tail
comparison is separate.

All estimates below are analytical polynomial and exponential inequalities.
-/

namespace RHTower
noncomputable section

/-- Signed even reflection moments of the actual first theta atom. -/
def firstAtomSignedMoment (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^n * thetaCuspFirstAtomReflectionJet (2*n) x

/-- The first seven central-factorial transforms, with no Gaussian approximation. -/
def firstAtomCentralMoment (n : Fin 7) (x : ℝ) : ℝ :=
  let m := fun k => firstAtomSignedMoment k x
  match n.val with
  | 0 => m 0
  | 1 => m 1
  | 2 => m 2 + 4*m 1
  | 3 => m 3 + 20*m 2 + 64*m 1
  | 4 => m 4 + 56*m 3 + 784*m 2 + 2304*m 1
  | 5 => m 5 + 120*m 4 + 4368*m 3 + 52480*m 2 + 147456*m 1
  | _ => m 6 + 220*m 5 + 16368*m 4 + 489280*m 3 + 5395456*m 2 + 14745600*m 1

/-- The exact coefficients (2n)! 4^n / n! through n = 6. -/
def centralGaussianCoefficient (n : Fin 7) : ℝ :=
  match n.val with
  | 0 => 1 | 1 => 8 | 2 => 192 | 3 => 7680
  | 4 => 430080 | 5 => 30965760 | _ => 2724986880

/-- Exact central-factorial moments in the original source normalization. -/
theorem firstAtomCentralMoment_eq (n : Fin 7) (x : ℝ) :
    firstAtomCentralMoment n x =
      let q := thetaCuspSingleAtomReflectionScale 1 x
      Real.exp (x/2-q)^2 * 4*q^2 * centralGaussianCoefficient n * q^n.val *
        ((2*q-3)^2 + 6*n.val) := by
  fin_cases n <;>
    norm_num [firstAtomCentralMoment, firstAtomSignedMoment, centralGaussianCoefficient,
      thetaCuspFirstAtomReflectionJet_zero,
      thetaCuspFirstAtomReflectionJet_2, thetaCuspFirstAtomReflectionJet_4,
      thetaCuspFirstAtomReflectionJet_6, thetaCuspFirstAtomReflectionJet_8,
      thetaCuspFirstAtomReflectionJet_10, thetaCuspFirstAtomReflectionJet_12,
      thetaCuspSourceTerm_one_eq_scale_profile] <;> ring


/-- First diagonal after completing the mass square. -/
def centralHermiteOne (v h : ℝ) := 2+4*h-h^2-v*(1+h)
/-- Second remaining diagonal in central Hermite coordinates. -/
def centralHermiteTwo (v h : ℝ) := (24-72*v)*(1+4*h)+36*v^2*(1+2*h)
/-- Third remaining diagonal in central Hermite coordinates. -/
def centralHermiteThree (v h : ℝ) :=
  720+4320*h-5400*v*(1+7*h)+13500*v^2+70200*v^2*h-5400*v^3*(1+3*h)
/-- Cross entry between the first and second nonconstant coordinates. -/
def centralHermiteCross12 (v h : ℝ) := 12*h-6*v*(1+3*h)
/-- Cross entry between the first and third nonconstant coordinates. -/
def centralHermiteCross13 (v h : ℝ) := -90*v*h
/-- Cross entry between the second and third nonconstant coordinates. -/
def centralHermiteCross23 (v h : ℝ) := 360*h-360*v*(1+7*h)+540*v^2*(1+4*h)

/-- Explicit entry bounds on the actual parameter curve for q >= 4. -/
theorem centralHermite_bounds {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/8)
    (hrel : h*(1-3*v)^2 = 6*v^2) :
    15/8 ≤ centralHermiteOne v h ∧ 15 ≤ centralHermiteTwo v h ∧
    400 ≤ centralHermiteThree v h ∧
    |centralHermiteCross12 v h| ≤ 2 ∧
    |centralHermiteCross13 v h| ≤ 3 ∧
    |centralHermiteCross23 v h| ≤ 20 := by
  have hd : 0 < 1-3*v := by linarith
  have hD : 0 < (1-3*v)^2 := sq_pos_of_pos hd
  have hh : 0 ≤ h := by nlinarith only [hrel, sq_nonneg v, hD]
  have hv2 : v^2 ≤ (1/8 : ℝ)^2 := pow_le_pow_left₀ hv hvU 2
  have hDl : (5/8 : ℝ)^2 ≤ (1-3*v)^2 := by nlinarith [sq_nonneg (1-3*v-5/8)]
  have hhU : h ≤ 6/25 := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hDl)]
  have hr : 0 ≤ 1-8*v := by linarith
  have hrU : 1-8*v ≤ 1 := by linarith
  have hb1 : 15/8 ≤ centralHermiteOne v h := by
    have hp := mul_nonneg hh (show 0 ≤ 4-h-v by linarith)
    unfold centralHermiteOne
    nlinarith only [hp, hvU]
  have hb2 : 15 ≤ centralHermiteTwo v h := by
    have hp := mul_nonneg (show 0 ≤ 24-72*v by linarith) hh
    have hq := mul_nonneg (sq_nonneg v) (show 0 ≤ 1+2*h by linarith)
    unfold centralHermiteTwo
    nlinarith only [hp,hq,hvU]
  have hid3 : 32768*(centralHermiteThree v h-400)*(1-3*v)^2 =
      49240+208920*(1-8*v)+5072400*(1-8*v)*(8*v)+
        6210000*(1-8*v)^3+3871800*(1-8*v)^4+145800*(1-8*v)^5 := by
    unfold centralHermiteThree
    linear_combination 32768*(4320-37800*v+70200*v^2-16200*v^3)*hrel
  have hb3 : 400 ≤ centralHermiteThree v h := by
    have hp : 0 ≤ 49240+208920*(1-8*v)+5072400*(1-8*v)*(8*v)+
        6210000*(1-8*v)^3+3871800*(1-8*v)^4+145800*(1-8*v)^5 := by positivity
    nlinarith only [hid3,hp,hD]
  have hib : 512*(2-centralHermiteCross12 v h)*(1-3*v)^2 =
      82+942*(1-8*v)+234*(1-8*v)*(8*v)+
        162*(1-8*v)*(1-(1-8*v)^2) := by
    unfold centralHermiteCross12
    linear_combination -512*(12-18*v)*hrel
  have hr2 : (1-8*v)^2 ≤ 1 := by nlinarith [mul_nonneg hr (show 0 ≤ 8*v by positivity)]
  have hbU : centralHermiteCross12 v h ≤ 2 := by
    have hp : 0 ≤ 82+942*(1-8*v)+234*(1-8*v)*(8*v)+
        162*(1-8*v)*(1-(1-8*v)^2) := by positivity
    nlinarith only [hib,hp,hD]
  have hbL : -2 ≤ centralHermiteCross12 v h := by
    have hp := mul_nonneg hv (sub_nonneg.mpr hhU)
    have hq := mul_nonneg (sub_nonneg.mpr hvU) (show 0 ≤ 1+3*h by positivity)
    unfold centralHermiteCross12
    nlinarith only [hh,hhU,hp,hq]
  have hc : |centralHermiteCross13 v h| ≤ 3 := by
    have hp := mul_nonneg (sub_nonneg.mpr hvU) hh
    have hq := mul_nonneg hv hh
    unfold centralHermiteCross13
    exact abs_le.mpr ⟨by nlinarith only [hp,hhU], by nlinarith only [hq]⟩
  have hieU : -512*centralHermiteCross23 v h*(1-3*v)^2 =
      180*v*(157+105*(1-8*v)+663*(1-8*v)^2+99*(1-8*v)^3) := by
    unfold centralHermiteCross23
    linear_combination -512*(360-2520*v+2160*v^2)*hrel
  have hieL : 4096*(20+centralHermiteCross23 v h)*(1-3*v)^2 =
      3740+(1-8*v)*(47760*(8*v)^2+6600*(1-8*v)*(8*v)+
        60360*(1-8*v)^2)+17820*(1-8*v)^4 := by
    unfold centralHermiteCross23
    linear_combination 4096*(360-2520*v+2160*v^2)*hrel
  have heU : centralHermiteCross23 v h ≤ 0 := by
    have hp : 0 ≤ 180*v*(157+105*(1-8*v)+663*(1-8*v)^2+99*(1-8*v)^3) := by positivity
    nlinarith only [hieU,hp,hD]
  have heL : -20 ≤ centralHermiteCross23 v h := by
    have hp : 0 ≤ 3740+(1-8*v)*(47760*(8*v)^2+6600*(1-8*v)*(8*v)+
        60360*(1-8*v)^2)+17820*(1-8*v)^4 := by positivity
    nlinarith only [hieL,hp,hD]
  exact ⟨hb1,hb2,hb3,abs_le.mpr ⟨hbL,hbU⟩,hc,abs_le.mpr ⟨heL,heU.trans (by norm_num)⟩⟩


/-- Explicit entry bounds on the actual parameter curve for q >= 7/2. -/
theorem centralHermiteInner_bounds {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/7)
    (hrel : h*(1-3*v)^2 = 6*v^2) :
    13/7 ≤ centralHermiteOne v h ∧ 20 ≤ centralHermiteTwo v h ∧
    320 ≤ centralHermiteThree v h ∧
    |centralHermiteCross12 v h| ≤ 3 ∧
    |centralHermiteCross13 v h| ≤ 5 ∧
    |centralHermiteCross23 v h| ≤ 25 := by
  have hd : 0 < 1-3*v := by linarith
  have hD : 0 < (1-3*v)^2 := sq_pos_of_pos hd
  have hh : 0 ≤ h := by nlinarith only [hrel, sq_nonneg v, hD]
  have hv2 : v^2 ≤ (1/7 : ℝ)^2 := pow_le_pow_left₀ hv hvU 2
  have hDl : (4/7 : ℝ)^2 ≤ (1-3*v)^2 := by nlinarith [sq_nonneg (1-3*v-4/7)]
  have hhU : h ≤ 3/8 := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hDl)]
  have hr : 0 ≤ 1-7*v := by linarith
  have hrU : 1-7*v ≤ 1 := by linarith
  have hb1 : 13/7 ≤ centralHermiteOne v h := by
    have hp := mul_nonneg hh (show 0 ≤ 4-h-v by linarith)
    unfold centralHermiteOne
    nlinarith only [hp, hvU]
  have hid2 : (centralHermiteTwo v h-20)*(1-3*v)^2 =
      (2-24*v)^2+(504-2592*v)*v^2+756*v^4 := by
    unfold centralHermiteTwo
    linear_combination (96-288*v+72*v^2)*hrel
  have hb2 : 20 ≤ centralHermiteTwo v h := by
    have hp : 0 ≤ (2-24*v)^2+(504-2592*v)*v^2+756*v^4 := by
      have hpv : 0 ≤ 504-2592*v := by linarith
      positivity
    nlinarith only [hid2,hp,hD]
  have hid3 : 16807*(centralHermiteThree v h-320)*(1-3*v)^2 =
      15760+181140*(1-7*v)+4619340*(1-7*v)*(7*v)+
        3083400*(1-7*v)^3+3296700*(1-7*v)^4+145800*(1-7*v)^5 := by
    unfold centralHermiteThree
    linear_combination 16807*(4320-37800*v+70200*v^2-16200*v^3)*hrel
  have hb3 : 320 ≤ centralHermiteThree v h := by
    have hp : 0 ≤ 15760+181140*(1-7*v)+4619340*(1-7*v)*(7*v)+
        3083400*(1-7*v)^3+3296700*(1-7*v)^4+145800*(1-7*v)^5 := by positivity
    nlinarith only [hid3,hp,hD]
  have hib : 343*(3-centralHermiteCross12 v h)*(1-3*v)^2 =
      36+993*(1-7*v)+81*(1-7*v)*(7*v)+
        162*(1-7*v)*(1-(1-7*v)^2) := by
    unfold centralHermiteCross12
    linear_combination -343*(12-18*v)*hrel
  have hr2 : (1-7*v)^2 ≤ 1 := by nlinarith [mul_nonneg hr (show 0 ≤ 7*v by positivity)]
  have hbU : centralHermiteCross12 v h ≤ 3 := by
    have hp : 0 ≤ 36+993*(1-7*v)+81*(1-7*v)*(7*v)+
        162*(1-7*v)*(1-(1-7*v)^2) := by positivity
    nlinarith only [hib,hp,hD]
  have hbL : -3 ≤ centralHermiteCross12 v h := by
    have hp := mul_nonneg hv (sub_nonneg.mpr hhU)
    have hq := mul_nonneg (sub_nonneg.mpr hvU) (show 0 ≤ 1+3*h by positivity)
    unfold centralHermiteCross12
    nlinarith only [hh,hhU,hp,hq]
  have hc : |centralHermiteCross13 v h| ≤ 5 := by
    have hp := mul_nonneg (sub_nonneg.mpr hvU) hh
    have hq := mul_nonneg hv hh
    unfold centralHermiteCross13
    exact abs_le.mpr ⟨by nlinarith only [hp,hhU], by nlinarith only [hq]⟩
  have hieU : -343*centralHermiteCross23 v h*(1-3*v)^2 =
      180*v*(44+60*(7*v)+543*(1-7*v)^2+99*(1-7*v)^3) := by
    unfold centralHermiteCross23
    linear_combination -343*(360-2520*v+2160*v^2)*hrel
  have hieL : 2401*(25+centralHermiteCross23 v h)*(1-3*v)^2 =
      880+(1-7*v)*(58920*(7*v)^2+20325*(1-7*v)*(7*v)+
        41325*(1-7*v)^2)+17820*(1-7*v)^4 := by
    unfold centralHermiteCross23
    linear_combination 2401*(360-2520*v+2160*v^2)*hrel
  have heU : centralHermiteCross23 v h ≤ 0 := by
    have hp : 0 ≤ 180*v*(44+60*(7*v)+543*(1-7*v)^2+99*(1-7*v)^3) := by positivity
    nlinarith only [hieU,hp,hD]
  have heL : -25 ≤ centralHermiteCross23 v h := by
    have hp : 0 ≤ 880+(1-7*v)*(58920*(7*v)^2+20325*(1-7*v)*(7*v)+
        41325*(1-7*v)^2)+17820*(1-7*v)^4 := by positivity
    nlinarith only [hieL,hp,hD]
  exact ⟨hb1,hb2,hb3,abs_le.mpr ⟨hbL,hbU⟩,hc,abs_le.mpr ⟨heL,heU.trans (by norm_num)⟩⟩


/-- The normalized four-coordinate first-atom quadratic form. -/
def centralHermiteQuadratic (v h : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  (y 0+h*y 1)^2 + centralHermiteOne v h*(y 1)^2 +
    centralHermiteTwo v h*(y 2)^2 + centralHermiteThree v h*(y 3)^2 +
    2*centralHermiteCross12 v h*y 1*y 2 +
    2*centralHermiteCross13 v h*y 1*y 3 +
    2*centralHermiteCross23 v h*y 2*y 3

/-- Four quantitative reserves after absorbing the three cross entries. -/
theorem centralHermiteQuadratic_lower {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/8)
    (hrel : h*(1-3*v)^2 = 6*v^2) (y : Fin 4 → ℝ) :
    (y 0+h*y 1)^2 + (7/8)*(y 1)^2 + 3*(y 2)^2 + 282*(y 3)^2 ≤
      centralHermiteQuadratic v h y := by
  obtain ⟨hd1,hd2,hd3,hb,hc,he⟩ := centralHermite_bounds hv hvU hrel
  have hbb : (centralHermiteCross12 v h)^2 ≤ 4 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ centralHermiteCross12 v h+2 by linarith)]
  have hcc : (centralHermiteCross13 v h)^2 ≤ 9 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ centralHermiteCross13 v h+3 by linarith)]
  have hee : (centralHermiteCross23 v h)^2 ≤ 400 := by
    obtain ⟨hl,hu⟩ := abs_le.mp he
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ centralHermiteCross23 v h+20 by linarith)]
  have hxy : 0 ≤ (1/2)*(y 1)^2+2*centralHermiteCross12 v h*y 1*y 2+8*(y 2)^2 := by
    nlinarith only [sq_nonneg (y 1/2+centralHermiteCross12 v h*y 2),
      mul_nonneg (sub_nonneg.mpr hbb) (sq_nonneg (y 2))]
  have hxz : 0 ≤ (1/2)*(y 1)^2+2*centralHermiteCross13 v h*y 1*y 3+18*(y 3)^2 := by
    nlinarith only [sq_nonneg (y 1/2+centralHermiteCross13 v h*y 3),
      mul_nonneg (sub_nonneg.mpr hcc) (sq_nonneg (y 3))]
  have hyz : 0 ≤ 4*(y 2)^2+2*centralHermiteCross23 v h*y 2*y 3+100*(y 3)^2 := by
    nlinarith only [sq_nonneg (2*y 2+centralHermiteCross23 v h/2*y 3),
      mul_nonneg (sub_nonneg.mpr hee) (sq_nonneg (y 3))]
  have h1 := mul_le_mul_of_nonneg_right hd1 (sq_nonneg (y 1))
  have h2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (y 2))
  have h3 := mul_le_mul_of_nonneg_right hd3 (sq_nonneg (y 3))
  unfold centralHermiteQuadratic
  linarith only [hxy,hxz,hyz,h1,h2,h3]

/-- The corresponding reserves on the larger inner scale range. -/
theorem centralHermiteQuadratic_inner_lower {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/7)
    (hrel : h*(1-3*v)^2 = 6*v^2) (y : Fin 4 → ℝ) :
    (y 0+h*y 1)^2 + (5/14)*(y 1)^2 + (y 2)^2 + 196*(y 3)^2 ≤
      centralHermiteQuadratic v h y := by
  obtain ⟨hd1,hd2,hd3,hb,hc,he⟩ := centralHermiteInner_bounds hv hvU hrel
  have hbb : (centralHermiteCross12 v h)^2 ≤ 9 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ centralHermiteCross12 v h+3 by linarith)]
  have hcc : (centralHermiteCross13 v h)^2 ≤ 25 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ centralHermiteCross13 v h+5 by linarith)]
  have hee : (centralHermiteCross23 v h)^2 ≤ 625 := by
    obtain ⟨hl,hu⟩ := abs_le.mp he
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ centralHermiteCross23 v h+25 by linarith)]
  have hxy : 0 ≤ (3/4)*(y 1)^2+2*centralHermiteCross12 v h*y 1*y 2+12*(y 2)^2 := by
    nlinarith only [sq_nonneg (3*y 1/4+centralHermiteCross12 v h*y 2),
      mul_nonneg (sub_nonneg.mpr hbb) (sq_nonneg (y 2))]
  have hxz : 0 ≤ (3/4)*(y 1)^2+2*centralHermiteCross13 v h*y 1*y 3+(100/3)*(y 3)^2 := by
    nlinarith only [sq_nonneg (3*y 1/4+centralHermiteCross13 v h*y 3),
      mul_nonneg (sub_nonneg.mpr hcc) (sq_nonneg (y 3))]
  have hyz : 0 ≤ 7*(y 2)^2+2*centralHermiteCross23 v h*y 2*y 3+(625/7)*(y 3)^2 := by
    nlinarith only [sq_nonneg (7*y 2+centralHermiteCross23 v h*y 3),
      mul_nonneg (sub_nonneg.mpr hee) (sq_nonneg (y 3))]
  have h1 := mul_le_mul_of_nonneg_right hd1 (sq_nonneg (y 1))
  have h2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (y 2))
  have h3 := mul_le_mul_of_nonneg_right hd3 (sq_nonneg (y 3))
  unfold centralHermiteQuadratic
  linarith only [hxy,hxz,hyz,h1,h2,h3,sq_nonneg (y 3)]


/-- Triangular coordinates of an even polynomial in the central Hermite basis. -/
def firstAtomCentralCoordinates (v s : ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let y3 := s^3*c 3
  let y2 := s^2*c 2-(5*v-15)*y3
  let y1 := s*c 1-(v-6)*y2-(4*v^2-15*v+45)*y3
  fun i => if i.val = 0 then c 0+y1-3*y2+15*y3
    else if i.val = 1 then y1 else if i.val = 2 then y2 else y3

/-- Literal first-atom signed energy of the polynomial sum c_i X^(2i). -/
def firstAtomEvenEnergy (x : ℝ) (c : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomSignedMoment (i.val+j.val) x

/-- Completing the first square preserves affine dependence on the seed parameter. -/
theorem centralHermiteQuadratic_affine (v h : ℝ) (y : Fin 4 → ℝ) :
    centralHermiteQuadratic v h y = centralHermiteQuadratic v 0 y +
      h*(centralHermiteQuadratic v 1 y-centralHermiteQuadratic v 0 y) := by
  unfold centralHermiteQuadratic centralHermiteOne centralHermiteTwo centralHermiteThree
    centralHermiteCross12 centralHermiteCross13 centralHermiteCross23
  ring

set_option maxRecDepth 2048 in
/-- Exact source quadratic identity; all first-atom derivatives through twelve are retained. -/
theorem firstAtomEvenEnergy_eq_centralHermite {x : ℝ}
    (hq : 3/2 < thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    firstAtomEvenEnergy x c = thetaCuspSourceTerm x 1^2 *
      centralHermiteQuadratic ((2*thetaCuspSingleAtomReflectionScale 1 x)⁻¹)
        (6/(2*thetaCuspSingleAtomReflectionScale 1 x-3)^2)
        (firstAtomCentralCoordinates ((2*thetaCuspSingleAtomReflectionScale 1 x)⁻¹)
          (8*thetaCuspSingleAtomReflectionScale 1 x) c) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 2*thetaCuspSingleAtomReflectionScale 1 x-3 ≠ 0 := by linarith
  rw [centralHermiteQuadratic_affine]
  dsimp only [centralHermiteQuadratic, firstAtomCentralCoordinates]
  norm_num [firstAtomEvenEnergy, firstAtomSignedMoment, Fin.sum_univ_succ,
    thetaCuspFirstAtomReflectionJet_zero,
    thetaCuspFirstAtomReflectionJet_2, thetaCuspFirstAtomReflectionJet_4,
    thetaCuspFirstAtomReflectionJet_6, thetaCuspFirstAtomReflectionJet_8,
    thetaCuspFirstAtomReflectionJet_10, thetaCuspFirstAtomReflectionJet_12,
    thetaCuspSourceTerm_one_eq_scale_profile, firstAtomCentralCoordinates,
    centralHermiteQuadratic, centralHermiteOne, centralHermiteTwo, centralHermiteThree,
    centralHermiteCross12, centralHermiteCross13, centralHermiteCross23]
  generalize heq : thetaCuspSingleAtomReflectionScale 1 x = q at *
  generalize heg : Real.exp (x/2-q) = g
  have hD : 9-q*12+q^2*4 ≠ 0 := by
    (convert pow_ne_zero 2 hd using 1; ring)
  norm_num [Fin.succ]
  ring_nf
  (field_simp [hqp.ne', hd, hD]; ring!)

/-- A quantitative first-atom reserve on the middle scale, in the actual source normalization. -/
theorem firstAtomEvenEnergy_lower_of_four_le {x : ℝ}
    (hq : 4 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    282*thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6*(c 3)^2 ≤
      firstAtomEvenEnergy x c := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let v := (2*q)⁻¹
  let h := 6/(2*q-3)^2
  have hqp : 0 < q := by dsimp [q]; linarith
  have hd : 2*q-3 ≠ 0 := by dsimp [q]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvU : v ≤ 1/8 := by
    dsimp [v]
    apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]
    linarith
  have hrel : h*(1-3*v)^2 = 6*v^2 := by
    dsimp [h,v]
    field_simp [hqp.ne', hd]
  have hp := centralHermiteQuadratic_lower hv hvU hrel (firstAtomCentralCoordinates v (8*q) c)
  have hl : 282*((firstAtomCentralCoordinates v (8*q) c) 3)^2 ≤
      centralHermiteQuadratic v h (firstAtomCentralCoordinates v (8*q) c) := by
    nlinarith only [hp,
      sq_nonneg ((firstAtomCentralCoordinates v (8*q) c) 0+h*(firstAtomCentralCoordinates v (8*q) c) 1),
      sq_nonneg ((firstAtomCentralCoordinates v (8*q) c) 1),
      sq_nonneg ((firstAtomCentralCoordinates v (8*q) c) 2)]
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (thetaCuspSourceTerm x 1))
  rw [firstAtomEvenEnergy_eq_centralHermite (by linarith : 3/2 < thetaCuspSingleAtomReflectionScale 1 x) c]
  have hy3 : firstAtomCentralCoordinates v (8*q) c 3 = (8*q)^3*c 3 := rfl
  rw [hy3] at hm
  calc
    282*thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6*(c 3)^2 =
        thetaCuspSourceTerm x 1^2*(282*((8*q)^3*c 3)^2) := by dsimp [q]; ring
    _ ≤ _ := hm

/-- A quantitative first-atom reserve on the middle scale, in the actual source normalization. -/
theorem firstAtomEvenEnergy_lower_of_seven_halves_le {x : ℝ}
    (hq : 7/2 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    196*thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6*(c 3)^2 ≤
      firstAtomEvenEnergy x c := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let v := (2*q)⁻¹
  let h := 6/(2*q-3)^2
  have hqp : 0 < q := by dsimp [q]; linarith
  have hd : 2*q-3 ≠ 0 := by dsimp [q]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvU : v ≤ 1/7 := by
    dsimp [v]
    apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]
    linarith
  have hrel : h*(1-3*v)^2 = 6*v^2 := by
    dsimp [h,v]
    field_simp [hqp.ne', hd]
  have hp := centralHermiteQuadratic_inner_lower hv hvU hrel (firstAtomCentralCoordinates v (8*q) c)
  have hl : 196*((firstAtomCentralCoordinates v (8*q) c) 3)^2 ≤
      centralHermiteQuadratic v h (firstAtomCentralCoordinates v (8*q) c) := by
    nlinarith only [hp,
      sq_nonneg ((firstAtomCentralCoordinates v (8*q) c) 0+h*(firstAtomCentralCoordinates v (8*q) c) 1),
      sq_nonneg ((firstAtomCentralCoordinates v (8*q) c) 1),
      sq_nonneg ((firstAtomCentralCoordinates v (8*q) c) 2)]
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (thetaCuspSourceTerm x 1))
  rw [firstAtomEvenEnergy_eq_centralHermite (by linarith : 3/2 < thetaCuspSingleAtomReflectionScale 1 x) c]
  have hy3 : firstAtomCentralCoordinates v (8*q) c 3 = (8*q)^3*c 3 := rfl
  rw [hy3] at hm
  calc
    196*thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6*(c 3)^2 =
        thetaCuspSourceTerm x 1^2*(196*((8*q)^3*c 3)^2) := by dsimp [q]; ring
    _ ≤ _ := hm

/-- Polynomial controlling the loss from the fixed first-atom correction. -/
def firstAtomCompensationReservePolynomial (q : ℝ) : ℝ :=
  629145600*q^7*(2*q-3)+1000000000000*(-8*q^4+30*q^3+129*q^2-378*q+135)

/-- A positive decomposition on three adjacent scale intervals. -/
theorem firstAtomCompensationReservePolynomial_pos {q : ℝ} (hq : 4 ≤ q) :
    0 < firstAtomCompensationReservePolynomial q := by
  by_cases h5 : q ≤ 5
  · let r := q-4
    have hr : 0 ≤ r := by dsimp [r]; linarith
    have hr1 : r ≤ 1 := by dsimp [r]; linarith
    have hp (n : ℕ) : r^n ≤ 1 := by simpa using pow_le_pow_left₀ hr hr1 n
    have hn : 174 ≤ -8*q^4+30*q^3+129*q^2-378*q+135 := by
      have he : -8*q^4+30*q^3+129*q^2-378*q+135 = 559+46*r-279*r^2-98*r^3-8*r^4 := by dsimp [r]; ring
      rw [he]
      nlinarith only [hp 2,hp 3,hp 4,hr]
    have hg : 0 ≤ 629145600*q^7*(2*q-3) := by
      have hp : 0 ≤ q := by linarith
      have hd : 0 ≤ 2*q-3 := by linarith
      positivity
    unfold firstAtomCompensationReservePolynomial
    nlinarith only [hn,hg]
  · have hq5 : 5 ≤ q := by linarith
    by_cases h6 : q ≤ 6
    · let r := q-5
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have hr1 : r ≤ 1 := by dsimp [r]; linarith
      have hr2 : r^2 ≤ 1 := by simpa using pow_le_pow_left₀ hr hr1 2
      have he : firstAtomCompensationReservePolynomial q =
          100000000000000 +
          (629145600*546875+220*1000000000000-560*1000000000000) +
          (629145600*921875-838*1000000000000+260*1000000000000)*r +
          (629145600*678125-621*1000000000000+200*1000000000000)*r^2 +
          (629145600*284375-130*1000000000000)*r^3 +
          (629145600*74375-8*1000000000000)*r^4 +
          629145600*(12425*r^5+1295*r^6+77*r^7+2*r^8) +
          260*1000000000000*(1-r)+200*1000000000000*(1-r^2) := by
        dsimp [firstAtomCompensationReservePolynomial,r]
        ring
      rw [he]
      have h1 : 0 ≤ 1-r := by linarith
      have h2 : 0 ≤ 1-r^2 := by linarith
      (norm_num; positivity)
    · have hq6 : 6 ≤ q := by linarith
      let r := q-6
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have he : firstAtomCompensationReservePolynomial q =
          1000000000000*((10-(31/2)*r)^2+100+(119/4)*r^2) +
          (629145600*2519424-1377*1000000000000-200*1000000000000) +
          (629145600*3499200-2502*1000000000000+310*1000000000000)*r +
          (629145600*2122848-1059*1000000000000-270*1000000000000)*r^2 +
          (629145600*734832-162*1000000000000)*r^3 +
          (629145600*158760-8*1000000000000)*r^4 +
          629145600*(21924*r^5+1890*r^6+93*r^7+2*r^8) := by
        dsimp [firstAtomCompensationReservePolynomial,r]
        ring
      rw [he]
      (norm_num; positivity)
/-- The actual scale retains a quadratic center bound from the hyperbolic sine inequality. -/
theorem twelve_mul_center_scale_le {x : ℝ} (hx : 0 ≤ x) :
    12*x*thetaCuspSingleAtomReflectionScale 1 x ≤
      thetaCuspSingleAtomReflectionScale 1 x^2-9 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 ≤ q := by dsimp [q,thetaCuspSingleAtomReflectionScale]; positivity
  have hs : 4*x ≤ Real.exp (2*x)-Real.exp (-(2*x)) := by
    have h := Real.self_le_sinh_iff.mpr (show 0 ≤ 2*x by linarith)
    rw [Real.sinh_eq] at h
    linarith
  have hqe : 3*Real.exp (2*x) ≤ q := by
    have h := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (2*x)).le
    simpa [q,thetaCuspSingleAtomReflectionScale] using h
  have he : q*Real.exp (-(2*x)) = Real.pi := by
    dsimp [q,thetaCuspSingleAtomReflectionScale]
    norm_num only [Nat.cast_one,one_pow,mul_one]
    rw [mul_assoc,← Real.exp_add]
    simp
  have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3*q by positivity)
  have h2 := mul_le_mul_of_nonneg_right hqe hqp
  change 12*x*q ≤ q^2-9
  nlinarith only [h1,h2,he,Real.pi_gt_three]

/-- The fixed first-atom correction uses the same mass/slope expression as the complete source. -/
def firstAtomCompensationSource (x : ℝ) : ℝ :=
  3*thetaCuspSourceTerm x 1^2 +
    2*x*thetaCuspSourceTerm x 1*deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x

/-- A fixed rational loss bound for the literal first-atom correction throughout the middle scale. -/
theorem firstAtomCompensationSource_lower_of_four_le {x : ℝ}
    (hx : 0 ≤ x) (hq : 4 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -200*thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6 <
      1000000000000*firstAtomCompensationSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let e := Real.exp (x/2-q)
  have hqp : 0 < q := by dsimp [q]; linarith
  have he : 0 < e := Real.exp_pos _
  have hd : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x = e*(-8*q^3+30*q^2-15*q) := by
    have h := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
    rw [iteratedDeriv_one] at h
    rw [h]
    dsimp [thetaCuspGaussianScaleJet,thetaCuspGaussianScaleMoment,e,q]
    ring
  have hp0 : 0 ≤ 4*q^2-6*q := by
    have h := mul_nonneg hqp.le (show 0 ≤ 4*q-6 by dsimp [q]; linarith)
    nlinarith only [h]
  have hp1 : -8*q^3+30*q^2-15*q ≤ 0 := by
    have h0 : 0 ≤ 8*q^2-30*q+15 := by
      have h := mul_nonneg (show 0 ≤ q-4 by dsimp [q]; linarith)
        (show 0 ≤ 8*q+2 by positivity)
      nlinarith only [h]
    have h := mul_nonneg hqp.le h0
    nlinarith only [h]
  have hgap : 12*q*x-q^2+9 ≤ 0 := by
    have h := twelve_mul_center_scale_le hx
    change 12*x*q ≤ q^2-9 at h
    nlinarith only [h]
  have hw : 0 < firstAtomCompensationReservePolynomial q :=
    firstAtomCompensationReservePolynomial_pos hq
  have herror : 0 ≤ 1000000000000*e^2*(4*q^2-6*q)*(-8*q^3+30*q^2-15*q)*(12*q*x-q^2+9) := by
    have hprod := mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hp0 hp1) hgap
    have h := mul_nonneg (show 0 ≤ 1000000000000*e^2 by positivity) hprod
    nlinarith only [h]
  have hmain : 0 < 2*q^2*(2*q-3)*e^2*firstAtomCompensationReservePolynomial q := by
    have hh : 0 < 2*q-3 := by dsimp [q]; linarith
    positivity
  have hid : 6*q*(1000000000000*firstAtomCompensationSource x+
      200*thetaCuspSourceTerm x 1^2*(8*q)^6) =
      2*q^2*(2*q-3)*e^2*firstAtomCompensationReservePolynomial q+
      1000000000000*e^2*(4*q^2-6*q)*(-8*q^3+30*q^2-15*q)*(12*q*x-q^2+9) := by
    unfold firstAtomCompensationSource
    rw [hd,thetaCuspSourceTerm_one_eq_scale_profile]
    change 6*q*(1000000000000*(3*(e*(4*q^2-6*q))^2+
      2*x*(e*(4*q^2-6*q))*(e*(-8*q^3+30*q^2-15*q)))+
      200*(e*(4*q^2-6*q))^2*(8*q)^6) = _
    unfold firstAtomCompensationReservePolynomial
    ring
  have hsum : 0 < 6*q*(1000000000000*firstAtomCompensationSource x+
      200*thetaCuspSourceTerm x 1^2*(8*q)^6) := by rw [hid]; linarith only [hmain,herror]
  have hpos : 0 < 1000000000000*firstAtomCompensationSource x+
      200*thetaCuspSourceTerm x 1^2*(8*q)^6 := by
    exact (mul_pos_iff_of_pos_left (show 0 < 6*q by positivity)).mp hsum
  dsimp [q] at hpos
  linarith only [hpos]

/-- The literal fixed-coefficient first-atom form retains an explicit sixth-degree reserve. -/
theorem firstAtomCompensatedEvenEnergy_lower_of_four_le {x : ℝ}
    (hx : 0 ≤ x) (hq : 4 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    82*thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^6*(c 3)^2 ≤
      firstAtomEvenEnergy x c+1000000000000*firstAtomCompensationSource x*(c 3)^2 := by
  have h1 := firstAtomEvenEnergy_lower_of_four_le hq c
  have h2 := mul_le_mul_of_nonneg_right (firstAtomCompensationSource_lower_of_four_le hx hq).le (sq_nonneg (c 3))
  nlinarith only [h1,h2]

/-- Four separate reserves survive the literal first-atom correction. -/
theorem firstAtomCompensatedEvenEnergy_coordinate_lower {x : ℝ}
    (hx : 0 ≤ x) (hq : 4 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let v := (2*q)⁻¹
    let h := 6/(2*q-3)^2
    let y := firstAtomCentralCoordinates v (8*q) c
    thetaCuspSourceTerm x 1^2 *
      ((y 0+h*y 1)^2+(7/8)*(y 1)^2+3*(y 2)^2+82*(y 3)^2) ≤
        firstAtomEvenEnergy x c+1000000000000*firstAtomCompensationSource x*(c 3)^2 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hd : 2*q-3 ≠ 0 := by dsimp [q]; linarith
  have hv : 0 ≤ (2*q)⁻¹ := by positivity
  have hvU : (2*q)⁻¹ ≤ (1/8 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]
    linarith
  have hrel : (6/(2*q-3)^2)*(1-3*(2*q)⁻¹)^2 = 6*((2*q)⁻¹)^2 := by
    field_simp [hqp.ne', hd]
  let y := firstAtomCentralCoordinates ((2*q)⁻¹) (8*q) c
  have hm := mul_le_mul_of_nonneg_left (centralHermiteQuadratic_lower hv hvU hrel y)
    (sq_nonneg (thetaCuspSourceTerm x 1))
  have hid := firstAtomEvenEnergy_eq_centralHermite
    (by linarith : 3/2 < thetaCuspSingleAtomReflectionScale 1 x) c
  change firstAtomEvenEnergy x c = thetaCuspSourceTerm x 1^2 *
    centralHermiteQuadratic ((2*q)⁻¹) (6/(2*q-3)^2) y at hid
  rw [← hid] at hm
  have hc := mul_le_mul_of_nonneg_right
    (firstAtomCompensationSource_lower_of_four_le hx hq).le (sq_nonneg (c 3))
  have hy3 : y 3 = (8*q)^3*c 3 := rfl
  change thetaCuspSourceTerm x 1^2 *
    ((y 0+(6/(2*q-3)^2)*y 1)^2+(7/8)*(y 1)^2+3*(y 2)^2+82*(y 3)^2) ≤ _
  have heq : thetaCuspSourceTerm x 1^2*(y 3)^2 =
      thetaCuspSourceTerm x 1^2*(8*q)^6*(c 3)^2 := by rw [hy3]; ring
  change -200*thetaCuspSourceTerm x 1^2*(8*q)^6*(c 3)^2 ≤ _ at hc
  nlinarith only [hm,hc,heq]

end
end RHTower
