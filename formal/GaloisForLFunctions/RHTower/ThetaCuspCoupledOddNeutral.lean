import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomOddFourPositivity
import GaloisForLFunctions.RHTower.ThetaCuspOddCentralTailPayment
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomAffineEnergy
import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddDrift
import GaloisForLFunctions.RHTower.ThetaCuspMixedPairOddFourFloor
import GaloisForLFunctions.RHTower.ThetaCuspCompensationNeutralAnchor
import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddRayModel

/-!
# Coupled odd-four positivity at the actual compensation-neutral point

The complete native reflection quadratic, including the canonical
moving-coordinate drift, has a uniform positive reserve on the neutral
scale interval. Its proof combines the exact first-atom matrix, the
literal unequal-pair weight, the pure second pair, and the complete
reflected Cauchy tail. At the actual zero of the center compensation
source, the coupled four-row form is positive for every nonzero vector
and every final diagonal coefficient. With the final diagonal coefficient
zero, the full canonical coupled form also has a strict reserve on the
entire scale-five ray, covering the complete negative-compensation region.
-/

namespace RHTower.ThetaCuspCoupledOddNeutral
noncomputable section
open Matrix HTGeometry.SignedPoisson ThetaCuspOddCentral ThetaCuspOddCentralTail
open ThetaCuspMixedPairOddFourFloor

private def d1 (v h : ℝ) : ℝ := 2/3-v+2*h*(1-v)
private def c12 (v h : ℝ) : ℝ := 5*v/6+h*(5*v-5/3)
private def c13 (v h : ℝ) : ℝ := -5*v*h/2
private def d2 (v h : ℝ) : ℝ :=
  (5/6)*(1+5*h)*(1-5*v)+(25/6)*v^2*(1+3*h)
private def c23 (v h : ℝ) : ℝ :=
  5*v/2-25*v^2/4+h*(-5/2+25*v-75*v^2/2)
private def d3 (v h : ℝ) : ℝ :=
  (5/7)*(1+7*h)-(15/2)*v*(1+8*h)+
    (15/4)*v^2*(7+45*h)-(75/4)*v^3*(1+4*h)

private theorem denominator_bounds {v : ℝ} (hvL : 4/45 ≤ v) (hvU : v ≤ 1/10) :
    49/100 ≤ (1-3*v)^2 ∧ (1-3*v)^2 ≤ 121/225 := by
  constructor <;> nlinarith

private theorem h_bounds {v h : ℝ} (hvL : 4/45 ≤ v) (hvU : v ≤ 1/10)
    (hrel : h*(1-3*v)^2=6*v^2) : 1/12 ≤ h ∧ h ≤ 6/49 := by
  obtain ⟨hDl,hDu⟩ := denominator_bounds hvL hvU
  have hD : 0 < (1-3*v)^2 := by linarith
  have hh : 0 ≤ h := by nlinarith only [hrel,hD,sq_nonneg v]
  have hv2l : (4/45:ℝ)^2 ≤ v^2 := by nlinarith
  have hv2u : v^2 ≤ (1/10:ℝ)^2 := by nlinarith
  have hl := mul_nonneg hh (sub_nonneg.mpr hDu)
  have hu := mul_nonneg hh (sub_nonneg.mpr hDl)
  constructor <;> nlinarith only [hl,hu,hrel,hv2l,hv2u]

private theorem c12_bound {v h : ℝ} (hvL : 4/45 ≤ v) (hvU : v ≤ 1/10)
    (hh : 0 ≤ h) (hhU : h ≤ 6/49) : |c12 v h| ≤ 1/10 := by
  have hl : 0 ≤ 5/3-5*v := by linarith
  have hu : 5/3-5*v ≤ 11/9 := by linarith
  have hp := mul_nonneg hh hl
  have hprod : h*(5/3-5*v) ≤ 22/147 := by
    calc
      _ ≤ (6/49)*(5/3-5*v) := mul_le_mul_of_nonneg_right hhU hl
      _ ≤ 22/147 := by nlinarith only [hu]
  apply abs_le.mpr
  unfold c12
  constructor <;> nlinarith only [hp,hprod,hvL,hvU]

private theorem b_bounds {v h : ℝ} (hvL : 4/45 ≤ v) (hvU : v ≤ 1/10)
    (hhL : 1/12 ≤ h) (hhU : h ≤ 6/49) : 1/54 ≤ 5*v*h/2 ∧ 5*v*h/2 ≤ 3/98 := by
  have hv : 0 ≤ v := by linarith
  have hh : 0 ≤ h := by linarith
  have hl := mul_le_mul hvL hhL (by norm_num : (0:ℝ) ≤ 1/12) hv
  have hu := mul_le_mul hvU hhU hh (by norm_num : (0:ℝ) ≤ 1/10)
  constructor <;> nlinarith only [hl,hu]

private theorem d1_bound {v h : ℝ} (hvU : v ≤ 1/10) (hh : 0 ≤ h) :
    17/30 ≤ d1 v h := by
  have hp := mul_nonneg hh (show 0 ≤ 1-v by linarith)
  unfold d1
  nlinarith only [hp,hvU]

private theorem d2_bound {v h : ℝ} (hvU : v ≤ 1/10) (hhL : 1/12 ≤ h) :
    85/144 ≤ d2 v h := by
  have hh : 0 ≤ h := by linarith
  have hA : 17/12 ≤ 1+5*h := by linarith
  have hB : 1/2 ≤ 1-5*v := by linarith
  have hp := mul_le_mul hA hB (by norm_num : (0:ℝ) ≤ 1/2)
    (show 0 ≤ 1+5*h by positivity)
  have htail : 0 ≤ (25/6)*v^2*(1+3*h) := by positivity
  unfold d2
  nlinarith only [hp,htail]

private theorem c23_bounds {v h : ℝ} (hvL : 4/45 ≤ v) (hvU : v ≤ 1/10)
    (hrel : h*(1-3*v)^2=6*v^2) : 3/25 ≤ c23 v h ∧ c23 v h ≤ 3/20 := by
  let r := 1-10*v
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrU : r ≤ 1/9 := by dsimp [r]; linarith
  have hD : 0 < 4*(1-3*v)^2 := by
    have : 0 < 1-3*v := by linarith
    positivity
  have h2 : r^2 ≤ r/9 := by nlinarith
  have h3 : r^3 ≤ r^2/9 := by
    nlinarith only [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrU)]
  have h4 : r^4 ≤ r^2/81 := by
    have h2U : r^2 ≤ 1/81 := by nlinarith
    nlinarith only [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr h2U)]
  have hL : 4*(1-3*v)^2*(c23 v h-3/25) =
      (423-3716*r+3518*r^2-3900*r^3-1125*r^4)/10000 := by
    dsimp [r,c23]
    linear_combination 4*(-5/2+25*v-75*v^2/2)*hrel
  have hU : 4*(1-3*v)^2*(3/20-c23 v h) =
      (33+844*r-682*r^2+780*r^3+225*r^4)/2000 := by
    dsimp [r,c23]
    linear_combination -4*(-5/2+25*v-75*v^2/2)*hrel
  have hPL : 0 ≤ (423-3716*r+3518*r^2-3900*r^3-1125*r^4)/10000 := by
    nlinarith only [hrU,h3,h4,sq_nonneg r]
  have hPU : 0 ≤ (33+844*r-682*r^2+780*r^3+225*r^4)/2000 := by
    nlinarith only [hr,h2,pow_nonneg hr 3,pow_nonneg hr 4]
  rw [← hL] at hPL
  rw [← hU] at hPU
  exact ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hD).mp hPL),
    sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hD).mp hPU)⟩

private theorem last_margin {v h : ℝ} (hvL : 4/45 ≤ v) (hvU : v ≤ 1/10)
    (hrel : h*(1-3*v)^2=6*v^2) : 1/10 ≤ d3 v h-5*v*h/2-c23 v h := by
  let r := 1-10*v
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrU : r ≤ 1 := by dsimp [r]; linarith
  have hD : 0 < 112000*(1-3*v)^2 := by
    have : 0 < 1-3*v := by linarith
    positivity
  have hDu := (denominator_bounds hvL hvU).2
  have hid : 112000*(1-3*v)^2*(d3 v h-5*v*h/2-c23 v h) =
      6083+45941*r-13814*r^2+26166*r^3+14931*r^4+693*r^5 := by
    dsimp [r,d3,c23]
    linear_combination 112000*(15/2-(175/2)*v+(825/4)*v^2-75*v^3)*hrel
  have h2 : r^2 ≤ r := by nlinarith
  have hp : 6083 ≤ 6083+45941*r-13814*r^2+26166*r^3+14931*r^4+693*r^5 := by
    nlinarith only [hr,h2,pow_nonneg hr 3,pow_nonneg hr 4,pow_nonneg hr 5]
  have hm : 0 ≤ 112000*(1-3*v)^2*(d3 v h-5*v*h/2-c23 v h-1/10) := by
    nlinarith only [hid,hp,hDu]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hD).mp hm)

private theorem cross_one (c x y : ℝ) :
    0 ≤ |c| * (x^2+y^2)+2*c*x*y := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    nlinarith only [mul_nonneg hc (sq_nonneg (x+y))]
  · rw [abs_of_nonpos hc]
    nlinarith only [mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg (x-y))]

private theorem cross_two (c x y : ℝ) :
    0 ≤ |c| * (2*x^2+y^2/2)+2*c*x*y := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    nlinarith only [mul_nonneg hc (sq_nonneg (2*x+y))]
  · rw [abs_of_nonpos hc]
    nlinarith only [mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg (2*x-y))]

private def modelEnergy (v h tau : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  (1+h)*(y 0)^2-2*h*y 0*y 1+d1 v h*(y 1)^2+
    2*c12 v h*y 1*y 2-5*v*h*y 1*y 3+d2 v h*(y 2)^2+
    2*(c23 v h-tau)*y 2*y 3+d3 v h*(y 3)^2

private theorem modelEnergy_coercive {v h tau : ℝ} (hvL : 4/45 ≤ v) (hvU : v ≤ 1/10)
    (hrel : h*(1-3*v)^2=6*v^2) (htauL : 0 ≤ tau) (htauU : tau ≤ 29/100)
    (y : Fin 4 → ℝ) :
    ((y 0)^2+(y 1)^2+(y 2)^2+(y 3)^2)/7 ≤ modelEnergy v h tau y := by
  obtain ⟨hhL,hhU⟩ := h_bounds hvL hvU hrel
  have hh : 0 ≤ h := by linarith
  have hc12 := c12_bound hvL hvU hh hhU
  obtain ⟨hbL,hbU⟩ := b_bounds hvL hvU hhL hhU
  obtain ⟨hc23L,hc23U⟩ := c23_bounds hvL hvU hrel
  have hd1 := d1_bound hvU hh
  have hd2 := d2_bound hvU hhL
  have hd3 := last_margin hvL hvU hrel
  have hk : |c23 v h-tau| ≤ 17/100 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hb : 0 ≤ 5*v*h/2 := by linarith
  have hr0 : 0 ≤ (1:ℝ)-1/7 := by norm_num
  have hr1 : 0 ≤ d1 v h-h-|c12 v h|-2*(5*v*h/2)-1/7 := by linarith
  have hr2 : 0 ≤ d2 v h-|c12 v h|-2*|c23 v h-tau|-1/7 := by linarith
  have hr3 : 0 ≤ d3 v h-(5*v*h/2)/2-|c23 v h-tau|/2-1/7 := by linarith
  have h01 := cross_one (-h) (y 0) (y 1)
  simp only [abs_neg,abs_of_nonneg hh] at h01
  have h12 := cross_one (c12 v h) (y 1) (y 2)
  have h13 := cross_two (-(5*v*h/2)) (y 1) (y 3)
  simp only [abs_neg,abs_of_nonneg hb] at h13
  have h23 := cross_two (c23 v h-tau) (y 2) (y 3)
  have h0 := mul_nonneg hr0 (sq_nonneg (y 0))
  have h1 := mul_nonneg hr1 (sq_nonneg (y 1))
  have h2 := mul_nonneg hr2 (sq_nonneg (y 2))
  have h3 := mul_nonneg hr3 (sq_nonneg (y 3))
  unfold modelEnergy
  nlinarith only [h0,h1,h2,h3,h01,h12,h13,h23]

private theorem canonicalModel_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqU : thetaCuspSingleAtomReflectionScale 1 x ≤ 45/8)
    (y : Fin 4 → ℝ) :
    ((y 0)^2+(y 1)^2+(y 2)^2+(y 3)^2)/7 ≤
      modelEnergy (1/(2*thetaCuspSingleAtomReflectionScale 1 x))
        (6/(2*thetaCuspSingleAtomReflectionScale 1 x-3)^2)
        (ThetaCuspCoupledOddDrift.normalizedCanonicalDrift x) y := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq3 : 0 < 2*q-3 := by dsimp [q]; linarith
  have hvL : (4/45:ℝ) ≤ 1/(2*q) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]
    linarith
  have hvU : 1/(2*q) ≤ (1/10:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]
    linarith
  have hrel : (6/(2*q-3)^2)*(1-3*(1/(2*q)))^2=6*(1/(2*q))^2 := by
    field_simp [hq0.ne', hq3.ne']
  obtain ⟨htauL,htauU⟩ := ThetaCuspCoupledOddDrift.normalizedCanonicalDrift_bounds hq
  exact modelEnergy_coercive hvL hvU hrel htauL htauU y

private theorem coordinates_centralBasis {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    coordinates q ((centralBasis (1/q)).mulVec y) = y := by
  funext i
  fin_cases i <;>
    norm_num [coordinates,centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
  all_goals
    field_simp [hq]
    ring_nf <;> rfl

private theorem centralBasis_coordinates {q : ℝ} (hq : q ≠ 0) (c : Fin 4 → ℝ) :
    (centralBasis (1/q)).mulVec (coordinates q c) = c := by
  funext i
  fin_cases i <;>
    norm_num [coordinates,centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
  all_goals
    field_simp [hq]
    ring_nf <;> rfl

private theorem firstAtom_energy_central {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j) =
      (8*q*thetaCuspSourceTerm x 1^2)*
        (star y ⬝ᵥ (centralMatrix (1/(2*q)) (6/(2*q-3)^2)).mulVec y) := by
  dsimp only
  have hq0 : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  rw [firstAtomOddFour_energy_eq hq,coordinates_centralBasis hq0]
  have hm := thetaCuspAffineGaussian_mul_seedSquare x
  dsimp only at hm
  rw [show 4*thetaCuspSingleAtomReflectionScale 1 x^2*
      Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)*
      (8*thetaCuspSingleAtomReflectionScale 1 x*(2*thetaCuspSingleAtomReflectionScale 1 x-3)^2) =
      8*thetaCuspSingleAtomReflectionScale 1 x*
        (4*thetaCuspSingleAtomReflectionScale 1 x^2*
          Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)*
          (2*thetaCuspSingleAtomReflectionScale 1 x-3)^2) by ring,hm]

private theorem signed_first_radial (k : ℕ) (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    (-1:ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) x =
      4*q^2*Real.exp (x-2*q)*(thetaPairRadialEvenPolynomial (q^2) k).eval (2*q) := by
  have h := thetaCuspAtomPairEvenJet_eq_radial 1 1 k x
  change thetaCuspFirstAtomReflectionJet (2*k) x = _ at h
  dsimp only
  rw [h]
  rw [show thetaCuspSingleAtomReflectionScale 1 x*thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspSingleAtomReflectionScale 1 x^2 by ring,
    show thetaCuspSingleAtomReflectionScale 1 x+thetaCuspSingleAtomReflectionScale 1 x =
      2*thetaCuspSingleAtomReflectionScale 1 x by ring,
    show x-thetaCuspSingleAtomReflectionScale 1 x-thetaCuspSingleAtomReflectionScale 1 x =
      x-2*thetaCuspSingleAtomReflectionScale 1 x by ring]
  have hs : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1:ℝ)^k*(-1:ℝ)^k)*
      (4*thetaCuspSingleAtomReflectionScale 1 x^2*
        Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)*
        (thetaPairRadialEvenPolynomial (thetaCuspSingleAtomReflectionScale 1 x^2) k).eval
          (2*thetaCuspSingleAtomReflectionScale 1 x)) := by ring
    _ = _ := by rw [hs,one_mul]

private theorem signed_twoAtom_decomposition (k : ℕ) (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    (-1:ℝ)^k*thetaCuspTwoAtomReflectionJet (2*k) x =
      (-1:ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) x+
      (4*q^2*Real.exp (x-2*q))*(8*Real.exp (-3*q))*
        (thetaPairRadialEvenPolynomial (4*q^2) k).eval (5*q)+
      (-1:ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 2 2 x := by
  rw [thetaCuspTwoAtomSignedEvenJet_eq_affine_add_second,signed_first_radial]
  dsimp only [thetaCuspTwoAtomAffineEvenMoment]
  ring

private theorem basis_quadratic (B M : Matrix (Fin 4) (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    (∑ r : Fin 4, ∑ s : Fin 4, (B.mulVec y r)*(B.mulVec y s)*M r s) =
      ∑ i : Fin 4, ∑ j : Fin 4, y i*y j*(∑ r : Fin 4, ∑ s : Fin 4, B r i*B s j*M r s) := by
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext r
    arg 2
    ext s
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem moving_coordinate {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    let c := (centralBasis (1/q)).mulVec y
    c 2+(168*q-56)*c 3=y 2/(768*q^2) := by
  norm_num [centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,
    show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
  field_simp [hq]
  ring

private theorem moving_coordinate_derivative {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    336*q*((centralBasis (1/q)).mulVec y) 3 = -y 3/(128*q^2) := by
  norm_num [centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,
    show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
  field_simp [hq]
  ring

private theorem canonical_flux_drift_eq {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    2*thetaCuspNativeOddCompensationCoefficient*x*thetaCuspFullSource x^2*
      (c 2+(168*q-56)*c 3)*(336*q*c 3) =
      -2*(8*q*thetaCuspSourceTerm x 1^2)*
        ThetaCuspCoupledOddDrift.normalizedCanonicalDrift x*y 2*y 3 := by
  dsimp only
  have hq0 : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (show 37/10 ≤
    thetaCuspSingleAtomReflectionScale 1 x by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  rw [moving_coordinate hq0,moving_coordinate_derivative hq0]
  unfold ThetaCuspCoupledOddDrift.normalizedCanonicalDrift
  field_simp [hq0,hf.ne']
  ring

private theorem firstAtom_canonical_drift_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqU : thetaCuspSingleAtomReflectionScale 1 x ≤ 45/8) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (8*q*thetaCuspSourceTerm x 1^2)/7*(∑ i : Fin 4, y i^2) ≤
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j)+
        2*thetaCuspNativeOddCompensationCoefficient*x*thetaCuspFullSource x^2*
          (c 2+(168*q-56)*c 3)*(336*q*c 3) := by
  dsimp only
  rw [firstAtom_energy_central hq,canonical_flux_drift_eq hq]
  have h := canonicalModel_coercive hq hqU y
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 8*q*thetaCuspSourceTerm x 1^2 by positivity)
  have he (v h t : ℝ) :
      star y ⬝ᵥ (centralMatrix v h).mulVec y-2*t*y 2*y 3=modelEnergy v h t y := by
    have hM : centralMatrix v h =
        !![1+h,-h,0,0;-h,d1 v h,c12 v h,c13 v h;
          0,c12 v h,d2 v h,c23 v h;0,c13 v h,c23 v h,d3 v h] := rfl
    rw [hM]
    norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,
      Matrix.cons_val_three,show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl,
      modelEnergy,c13]
    ring
  rw [← he] at hm
  have hs : (∑ i : Fin 4, y i^2)=(y 0)^2+(y 1)^2+(y 2)^2+(y 3)^2 := by
    norm_num [Fin.sum_univ_succ]
    simp only [show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
    ring
  rw [hs]
  dsimp [q] at hm
  nlinarith only [hm]

private theorem secondPair_odd_nonneg {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 2 2 x := by
  have hs : thetaCuspSingleAtomReflectionScale 1 (x+Real.log 2)=
      4*thetaCuspSingleAtomReflectionScale 1 x := by
    have he : Real.exp (2*Real.log 2)=4 := by
      rw [show (2:ℝ)*Real.log 2=Real.log 2+Real.log 2 by ring,
        Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
      norm_num
    unfold thetaCuspSingleAtomReflectionScale
    rw [show (2:ℝ)*(x+Real.log 2)=2*x+2*Real.log 2 by ring,Real.exp_add,he]
    norm_num
    ring
  have hscale : 5 ≤ thetaCuspSingleAtomReflectionScale 1 (x+Real.log 2) := by
    rw [hs]; linarith
  have hn := (firstAtomOddFour_posDef hscale).posSemidef.dotProduct_mulVec_nonneg c
  have he : (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 2 2 x) =
      ((2:ℝ)^(-(1/2:ℝ)))^2*(star c ⬝ᵥ (firstAtomOddFour (x+Real.log 2)).mulVec c) := by
    simp only [thetaCuspSecondPairReflectionJet_eq_shift,firstAtomOddFour,
      Matrix.mulVec,dotProduct,Pi.star_apply,star_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact mul_nonneg (sq_nonneg _) hn

private theorem weighted_division (d u v z : ℝ) (hd : d ≠ 0) :
    u*v*z=d*(u*v*(z/d)) := by
  field_simp [hd]

private theorem mixed_radial_energy {q : ℝ} (hq : 5 ≤ q) (y : Fin 4 → ℝ) :
    let c := (centralBasis (1/q)).mulVec y
    (∑ r : Fin 4, ∑ s : Fin 4, c r*c s*
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      (8*q*(2*q-3)^2)*(∑ i : Fin 4, ∑ j : Fin 4, y i*y j*mixedCentralMatrix q i j) := by
  dsimp only
  rw [basis_quadratic]
  have hd : 8*q*(2*q-3)^2 ≠ 0 := by
    have hq0 : q ≠ 0 := by linarith
    have hq3 : 2*q-3 ≠ 0 := by linarith
    exact mul_ne_zero (mul_ne_zero (by norm_num) hq0) (pow_ne_zero 2 hq3)
  simp only [mixedCentralMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  exact weighted_division _ _ _ _ hd

private theorem twoAtom_odd_energy_decomposition {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x) =
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j)+
      (8*q*thetaCuspSourceTerm x 1^2)*(8*Real.exp (-3*q))*
        (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*mixedCentralMatrix q i j)+
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 2 2 x) := by
  dsimp only
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let c := (centralBasis (1/q)).mulVec y
  have he (i j : Fin 4) : c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x =
      c i*c j*firstAtomOddFour x i j+
      ((4*q^2*Real.exp (x-2*q))*(8*Real.exp (-3*q)))*
        (c i*c j*(thetaPairRadialEvenPolynomial (4*q^2) (i.val+j.val+1)).eval (5*q))+
      c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 2 2 x := by
    calc
      _ = c i*c j*((-1:ℝ)^(i.val+j.val+1)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x) := by ring
      _ = _ := by
        rw [signed_twoAtom_decomposition]
        dsimp only [q,firstAtomOddFour]
        ring
  change (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
    thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)=_
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hrad := mixed_radial_energy hq y
  dsimp only at hrad
  change (∑ r : Fin 4, ∑ s : Fin 4, c r*c s*
    (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q))=_ at hrad
  rw [hrad]
  have hm := thetaCuspAffineGaussian_mul_seedSquare x
  change 4*q^2*Real.exp (x-2*q)*(2*q-3)^2=thetaCuspSourceTerm x 1^2 at hm
  have hp := congrArg (fun z : ℝ =>
    8*q*(8*Real.exp (-3*q))*(∑ i : Fin 4, ∑ j : Fin 4,
      y i*y j*mixedCentralMatrix q i j)*z) hm
  change _ = (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j)+
    (8*q*thetaCuspSourceTerm x 1^2)*(8*Real.exp (-3*q))*
      (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*mixedCentralMatrix q i j)+
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 2 2 x)
  linear_combination hp


/-- Native odd energy with the literal canonical moving-coordinate drift has a strict reserve. -/
theorem native_canonical_drift_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqU : thetaCuspSingleAtomReflectionScale 1 x ≤ 45/8) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (8*q*thetaCuspSourceTerm x 1^2)/56*(∑ i : Fin 4, y i^2) ≤
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x)+
        2*thetaCuspNativeOddCompensationCoefficient*x*thetaCuspFullSource x^2*
          (c 2+(168*q-56)*c 3)*(336*q*c 3) := by
  dsimp only
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let c := (centralBasis (1/q)).mulVec y
  have hfirst := firstAtom_canonical_drift_coercive hq hqU y
  have hsecond := secondPair_odd_nonneg hq c
  have hmix := mixedPairOddFour_exponential_floor hq hqU y
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hmixA := mul_nonneg (show 0 ≤ 8*q*thetaCuspSourceTerm x 1^2 by positivity) hmix
  have htail := (abs_le.mp (native_central_tail_payment hq y)).1
  have he := twoAtom_odd_energy_decomposition hq y
  dsimp only at hfirst htail he
  have hd : (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x-
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)) =
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x)-
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  change -((8*q*thetaCuspSourceTerm x 1^2)/10*(∑ i : Fin 4, y i^2)) ≤
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x-
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)) at htail
  rw [hd,he] at htail
  dsimp only [q,c] at hmixA hsecond htail
  linear_combination hfirst+hmixA+hsecond+htail



private theorem native_canonical_drift_pos {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqU : thetaCuspSingleAtomReflectionScale 1 x ≤ 45/8)
    (c : Fin 4 → ℝ) (hc : c ≠ 0) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    0 < (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x)+
      2*thetaCuspNativeOddCompensationCoefficient*x*thetaCuspFullSource x^2*
        (c 2+(168*q-56)*c 3)*(336*q*c 3) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let y := coordinates q c
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hcy : (centralBasis (1/q)).mulVec y=c := centralBasis_coordinates hq0.ne' c
  have hy : y ≠ 0 := by
    intro hy
    apply hc
    rw [← hcy,hy]
    simp
  have hsum : 0 < ∑ i : Fin 4, y i^2 := by
    by_contra hn
    have hs : (∑ i : Fin 4, y i^2) ≤ 0 := le_of_not_gt hn
    have hz (i : Fin 4) : y i=0 := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
        sq_nonneg (y j)) (Finset.mem_univ i)
      nlinarith only [hi,hs,sq_nonneg (y i)]
    exact hy (funext hz)
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (show 37/10 ≤
    thetaCuspSingleAtomReflectionScale 1 x by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hpos : 0 < (8*q*thetaCuspSourceTerm x 1^2)/56*(∑ i : Fin 4, y i^2) := by positivity
  have h := native_canonical_drift_coercive hq hqU y
  dsimp only at h
  change (8*q*thetaCuspSourceTerm x 1^2)/56*(∑ i : Fin 4, y i^2) ≤ _ at h
  rw [hcy] at h
  exact hpos.trans_le h

/-- Literal coupled odd-four source form, including both center-flux terms. -/
def coupledOddFourEnergy (C x : ℝ) (c : Fin 4 → ℝ) : ℝ :=
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let u := c 2+(168*q-56)*c 3
  (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
    thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x)+
    thetaCuspNativeOddCompensationCoefficient*
      (thetaCuspCenterCompensationSource x*u^2+
        2*x*thetaCuspFullSource x^2*u*(336*q*c 3))+
    C*thetaCuspCenterCompensationSource x*(c 3)^2

/-- The actual compensation-neutral point admits the coupled odd-four source form
for every final diagonal coefficient and every nonzero native vector. -/
theorem exists_neutral_coupledOddFour_positive :
    ∃ x : ℝ, 0 < x ∧ thetaCuspCenterCompensationSource x=0 ∧
      ∀ (C : ℝ) (c : Fin 4 → ℝ), c ≠ 0 → 0 < coupledOddFourEnergy C x c := by
  obtain ⟨x,hx,hq,hqU,hs⟩ := exists_thetaCuspCompensationNeutralAnchor
  have hz := (hs x hx.le).2.1.mpr rfl
  refine ⟨x,hx,hz,?_⟩
  intro C c hc
  have h := native_canonical_drift_pos hq.le hqU.le c hc
  dsimp only [coupledOddFourEnergy]
  rw [hz]
  simp only [zero_mul,mul_zero,zero_add,add_zero]
  convert h using 1
  ring


open ThetaCuspCoupledOddRayModel

private theorem canonical_compensation_eq {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource x*
      (c 2+(168*q-56)*c 3)^2 =
      (8*q*thetaCuspSourceTerm x 1^2)*normalizedCompensation x*(y 2)^2 := by
  dsimp only
  have hq0 : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (show 37/10 ≤
    thetaCuspSingleAtomReflectionScale 1 x by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  rw [moving_coordinate hq0]
  unfold normalizedCompensation
  field_simp [hq0,hf.ne']
  ring

private theorem star_quadratic (M : Matrix (Fin 4) (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    star y ⬝ᵥ M.mulVec y=∑ i : Fin 4,∑ j : Fin 4,y i*y j*M i j := by
  simp only [Matrix.mulVec,dotProduct,Pi.star_apply,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem firstAtom_coupled_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (8*q*thetaCuspSourceTerm x 1^2)/7*(∑ i : Fin 4,y i^2) ≤
      (∑ i : Fin 4,∑ j : Fin 4,c i*c j*firstAtomOddFour x i j)+
      thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource x*
        (c 2+(168*q-56)*c 3)^2+
      2*thetaCuspNativeOddCompensationCoefficient*x*thetaCuspFullSource x^2*
        (c 2+(168*q-56)*c 3)*(336*q*c 3) := by
  dsimp only
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let c := (centralBasis (1/q)).mulVec y
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hfirst := firstAtom_energy_central hq y
  have hg := canonical_compensation_eq hq y
  have ht := canonical_flux_drift_eq hq y
  dsimp only at hfirst hg ht
  have he : (∑ i : Fin 4,∑ j : Fin 4,c i*c j*firstAtomOddFour x i j)+
      thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource x*
        (c 2+(168*q-56)*c 3)^2+
      2*thetaCuspNativeOddCompensationCoefficient*x*thetaCuspFullSource x^2*
        (c 2+(168*q-56)*c 3)*(336*q*c 3) =
      (8*q*thetaCuspSourceTerm x 1^2)*centralEnergy q (normalizedCompensation x)
        (ThetaCuspCoupledOddDrift.normalizedCanonicalDrift x) y := by
    dsimp only [q,c]
    rw [hfirst,hg,ht,star_quadratic]
    unfold centralEnergy
    ring
  change (8*q*thetaCuspSourceTerm x 1^2)/7*(∑ i : Fin 4,y i^2) ≤ _
  rw [he]
  have hp := mul_le_mul_of_nonneg_left (source_central_coercive hq y)
    (show 0 ≤ 8*q*thetaCuspSourceTerm x 1^2 by positivity)
  calc
    (8*q*thetaCuspSourceTerm x 1^2)/7*(∑ i : Fin 4,y i^2) =
        (8*q*thetaCuspSourceTerm x 1^2)*((1/7)*∑ i : Fin 4,y i^2) := by ring
    _ ≤ _ := hp

/-- Actual canonical coupled source, with the complete infinite tail retained, on the scale-five ray. -/
theorem native_coupled_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (8*q*thetaCuspSourceTerm x 1^2)/56*(∑ i : Fin 4,y i^2) ≤ coupledOddFourEnergy 0 x c := by
  dsimp only [coupledOddFourEnergy]
  simp only [zero_mul,add_zero]
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let c := (centralBasis (1/q)).mulVec y
  have hfirst := firstAtom_coupled_coercive hq y
  have hsecond := secondPair_odd_nonneg hq c
  have hmix := mixedPairOddFour_exponential_floor_global hq y
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hmixA := mul_nonneg (show 0 ≤ 8*q*thetaCuspSourceTerm x 1^2 by positivity) hmix
  have htail := (abs_le.mp (native_central_tail_payment hq y)).1
  have he := twoAtom_odd_energy_decomposition hq y
  dsimp only at hfirst htail he
  have hd : (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x-
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)) =
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x)-
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  change -((8*q*thetaCuspSourceTerm x 1^2)/10*(∑ i : Fin 4,y i^2)) ≤
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x-
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)) at htail
  rw [hd,he] at htail
  dsimp only [q,c] at hmixA hsecond htail
  linear_combination hfirst+hmixA+hsecond+htail

/-- Unloaded coupled odd-four positivity for every nonzero native coefficient vector on the whole ray. -/
theorem coupledOddFourEnergy_zero_pos_of_scale_five {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) (hc : c ≠ 0) :
    0 < coupledOddFourEnergy 0 x c := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let y := coordinates q c
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hcy : (centralBasis (1/q)).mulVec y=c := centralBasis_coordinates hq0.ne' c
  have hy : y ≠ 0 := by
    intro hy
    apply hc
    rw [← hcy,hy]
    simp
  have hsum : 0 < ∑ i : Fin 4,y i^2 := by
    by_contra hn
    have hs : (∑ i : Fin 4,y i^2) ≤ 0 := le_of_not_gt hn
    have hz (i : Fin 4) : y i=0 := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
        sq_nonneg (y j)) (Finset.mem_univ i)
      nlinarith only [hi,hs,sq_nonneg (y i)]
    exact hy (funext hz)
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (show 37/10 ≤
    thetaCuspSingleAtomReflectionScale 1 x by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hpos : 0 < (8*q*thetaCuspSourceTerm x 1^2)/56*(∑ i : Fin 4,y i^2) := by positivity
  have h := native_coupled_coercive hq y
  dsimp only at h
  change (8*q*thetaCuspSourceTerm x 1^2)/56*(∑ i : Fin 4,y i^2) ≤
    coupledOddFourEnergy 0 x ((centralBasis (1/q)).mulVec y) at h
  rw [hcy] at h
  exact hpos.trans_le h

/-- The actual coupled form with C4=0 is positive throughout the entire negative-compensation region. -/
theorem coupledOddFourEnergy_zero_pos_of_compensation_neg {x : ℝ} (hx : 0 ≤ x)
    (hG : thetaCuspCenterCompensationSource x < 0) (c : Fin 4 → ℝ) (hc : c ≠ 0) :
    0 < coupledOddFourEnergy 0 x c :=
  coupledOddFourEnergy_zero_pos_of_scale_five (five_lt_scale_of_compensation_neg hx hG).le c hc

end
end RHTower.ThetaCuspCoupledOddNeutral
