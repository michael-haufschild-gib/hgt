import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCoupledOddNeutral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourSeamSplit

/-!
# The native odd-four fibre beyond scale six

On the scale ray `q = π e^{2x} ≥ 6` the complete native odd reflection block through order
fourteen is positive definite. In first-atom central coordinates the exact first-atom matrix has
every Gershgorin row reserve at least `1/5` once `v = 1/(2q) ≤ 1/12`; the ordered unequal pair
costs at most `1/40`, the second pair is a rescaled first atom and hence nonnegative, and the
complete tail beyond two atoms costs at most `1/10`.
-/

namespace RHTower.ThetaCuspOddFourNativeBulk
noncomputable section
open Matrix HTGeometry.SignedPoisson ThetaCuspOddCentral ThetaCuspOddCentralTail
open ThetaCuspMixedPairOddFourFloor

theorem coordinates_centralBasis' {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    coordinates q ((centralBasis (1/q)).mulVec y) = y := by
  funext i
  fin_cases i <;>
    norm_num [coordinates,centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
  all_goals
    field_simp [hq]
    ring_nf <;> rfl

theorem centralBasis_coordinates' {q : ℝ} (hq : q ≠ 0) (c : Fin 4 → ℝ) :
    (centralBasis (1/q)).mulVec (coordinates q c) = c := by
  funext i
  fin_cases i <;>
    norm_num [coordinates,centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
  all_goals
    field_simp [hq]
    ring_nf <;> rfl

/-! ### First-atom row reserves -/

theorem centralMatrix_00 (v h : ℝ) : centralMatrix v h 0 0 = 1+h := rfl
theorem centralMatrix_01 (v h : ℝ) : centralMatrix v h 0 1 = -h := rfl
theorem centralMatrix_02 (v h : ℝ) : centralMatrix v h 0 2 = 0 := rfl
theorem centralMatrix_03 (v h : ℝ) : centralMatrix v h 0 3 = 0 := rfl
theorem centralMatrix_10 (v h : ℝ) : centralMatrix v h 1 0 = -h := rfl
theorem centralMatrix_11 (v h : ℝ) : centralMatrix v h 1 1 = 2/3-v+2*h*(1-v) := rfl
theorem centralMatrix_12 (v h : ℝ) : centralMatrix v h 1 2 = 5*v/6+h*(5*v-5/3) := rfl
theorem centralMatrix_13 (v h : ℝ) : centralMatrix v h 1 3 = -5*v*h/2 := rfl
theorem centralMatrix_20 (v h : ℝ) : centralMatrix v h 2 0 = 0 := rfl
theorem centralMatrix_21 (v h : ℝ) : centralMatrix v h 2 1 = 5*v/6+h*(5*v-5/3) := rfl
theorem centralMatrix_22 (v h : ℝ) :
    centralMatrix v h 2 2 = (5/6)*(1+5*h)*(1-5*v)+(25/6)*v^2*(1+3*h) := rfl
theorem centralMatrix_23 (v h : ℝ) :
    centralMatrix v h 2 3 = 5*v/2-25*v^2/4+h*(-5/2+25*v-75*v^2/2) := rfl
theorem centralMatrix_30 (v h : ℝ) : centralMatrix v h 3 0 = 0 := rfl
theorem centralMatrix_31 (v h : ℝ) : centralMatrix v h 3 1 = -5*v*h/2 := rfl
theorem centralMatrix_32 (v h : ℝ) :
    centralMatrix v h 3 2 = 5*v/2-25*v^2/4+h*(-5/2+25*v-75*v^2/2) := rfl
theorem centralMatrix_33 (v h : ℝ) :
    centralMatrix v h 3 3 = (5/7)*(1+7*h)-(15/2)*v*(1+8*h)+
      (15/4)*v^2*(7+45*h)-(75/4)*v^3*(1+4*h) := rfl

private theorem cross_bound {c b a1 a2 : ℝ} (hcb : |c| ≤ b) :
    0 ≤ 2*c*a1*a2 + b*(a1^2+a2^2) := by
  have h0 : 0 ≤ |c| * (a1^2+a2^2)+2*c*a1*a2 := by
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc]
      nlinarith [mul_nonneg hc (sq_nonneg (a1+a2))]
    · rw [abs_of_nonpos hc]
      nlinarith [mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg (a1-a2))]
  have h1 := mul_le_mul_of_nonneg_right hcb (add_nonneg (sq_nonneg a1) (sq_nonneg a2))
  linarith

/-- Every first-atom row reserve is at least `1/6` for `v ≤ 1/12`. -/
theorem centralMatrix_coercive {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/12)
    (hrel : h*(1-3*v)^2 = 6*v^2) (y : Fin 4 → ℝ) :
    (1/6)*∑ i : Fin 4, y i^2 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i*y j*centralMatrix v h i j := by
  have hD : 0 < (1-3*v)^2 := by
    have h3 : 0 < 1-3*v := by linarith
    positivity
  set r := 1-12*v with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hh0 : 0 ≤ h := by
    by_contra hn
    push Not at hn
    nlinarith [mul_neg_of_neg_of_pos hn hD, sq_nonneg v]
  have hp2 := pow_nonneg hr0 2; have hp3 := pow_nonneg hr0 3
  have hp4 := pow_nonneg hr0 4; have hp5 := pow_nonneg hr0 5
  -- the off-diagonal entry `c23` is nonnegative
  set c23 := 5*v/2-25*v^2/4+h*(-5/2+25*v-75*v^2/2) with hc23def
  have hc23 : 0 ≤ c23 := by
    have hid : (1-3*v)^2*c23 =
        v*(595/768 + 455/768*r + 745/768*r^2 + 125/768*r^3) := by
      rw [hc23def, hr]
      linear_combination (-5/2+25*v-75*v^2/2) * hrel
    have hq : 0 ≤ v*(595/768 + 455/768*r + 745/768*r^2 + 125/768*r^3) :=
      mul_nonneg hv (by linarith)
    rw [← hid] at hq
    exact (mul_nonneg_iff_of_pos_left hD).mp hq
  -- the three nontrivial row reserves
  have hrow (E P : ℝ) (hid : (1-3*v)^2*E = P) (hP : 0 ≤ P) : 0 ≤ E := by
    rw [← hid] at hP
    exact (mul_nonneg_iff_of_pos_left hD).mp hP
  have R1 : 0 ≤ (2/3-v+2*h*(1-v)) - h - (5*v/6+5*h/3) - 5*v*h/2 - 1/6 :=
    hrow _ (175/1152 + 367/1152*r + 5/1152*r^2 + 29/1152*r^3)
      (by rw [hr]; linear_combination (-2/3 - 9/2*v) * hrel) (by linarith)
  have R2 : 0 ≤ ((5/6)*(1+5*h)*(1-5*v)+(25/6)*v^2*(1+3*h)) - (5*v/6+5*h/3) - c23 - 1/6 :=
    hrow _ (3533/27648 + 2183/6912*r + 631/13824*r^2 + 365/2304*r^3 + 175/9216*r^4)
      (by rw [hc23def, hr]; linear_combination (5 - 275/6*v + 50*v^2) * hrel) (by linarith)
  have R3 : 0 ≤ ((5/7)*(1+7*h)-(15/2)*v*(1+8*h)+(15/4)*v^2*(7+45*h)-(75/4)*v^3*(1+4*h)) -
      5*v*h/2 - c23 - 1/6 :=
    hrow _ (20659/774144 + 203881/774144*r + 263/387072*r^2 + 10375/55296*r^3 +
        7385/110592*r^4 + 275/110592*r^5)
      (by rw [hc23def, hr]; linear_combination (15/2 - 175/2*v + 825/4*v^2 - 75*v^3) * hrel)
      (by linarith)
  -- off-diagonal majorants
  have b01 : |(-h)| ≤ h := by rw [abs_neg, abs_of_nonneg hh0]
  have b12 : |5*v/6+h*(5*v-5/3)| ≤ 5*v/6+5*h/3 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hh0 hv]
  have b13 : |-5*v*h/2| ≤ 5*v*h/2 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hh0 hv]
  have b23 : |c23| ≤ c23 := (abs_of_nonneg hc23).le
  have x01 := cross_bound (a1 := y 0) (a2 := y 1) b01
  have x12 := cross_bound (a1 := y 1) (a2 := y 2) b12
  have x13 := cross_bound (a1 := y 1) (a2 := y 3) b13
  have x23 := cross_bound (a1 := y 2) (a2 := y 3) b23
  have d1 := mul_nonneg R1 (sq_nonneg (y 1))
  have d2 := mul_nonneg R2 (sq_nonneg (y 2))
  have d3 := mul_nonneg R3 (sq_nonneg (y 3))
  have d0 := sq_nonneg (y 0)
  have hsum : (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*centralMatrix v h i j) -
      (1/6)*∑ i : Fin 4, y i^2 =
      (5/6)*(y 0)^2 +
      ((2/3-v+2*h*(1-v)) - h - (5*v/6+5*h/3) - 5*v*h/2 - 1/6)*(y 1)^2 +
      (((5/6)*(1+5*h)*(1-5*v)+(25/6)*v^2*(1+3*h)) - (5*v/6+5*h/3) - c23 - 1/6)*(y 2)^2 +
      (((5/7)*(1+7*h)-(15/2)*v*(1+8*h)+(15/4)*v^2*(7+45*h)-(75/4)*v^3*(1+4*h)) -
        5*v*h/2 - c23 - 1/6)*(y 3)^2 +
      (2*(-h)*y 0*y 1 + h*((y 0)^2+(y 1)^2)) +
      (2*(5*v/6+h*(5*v-5/3))*y 1*y 2 + (5*v/6+5*h/3)*((y 1)^2+(y 2)^2)) +
      (2*(-5*v*h/2)*y 1*y 3 + (5*v*h/2)*((y 1)^2+(y 3)^2)) +
      (2*c23*y 2*y 3 + c23*((y 2)^2+(y 3)^2)) := by
    simp only [Fin.sum_univ_four, centralMatrix_00, centralMatrix_01, centralMatrix_02,
      centralMatrix_03, centralMatrix_10, centralMatrix_11, centralMatrix_12, centralMatrix_13,
      centralMatrix_20, centralMatrix_21, centralMatrix_22, centralMatrix_23, centralMatrix_30,
      centralMatrix_31, centralMatrix_32, centralMatrix_33, hc23def]
    ring
  linarith


/-! ### The two-atom decomposition in central coordinates -/

private theorem firstAtom_energy_central {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j) =
      (8*q*thetaCuspSourceTerm x 1^2)*
        (star y ⬝ᵥ (centralMatrix (1/(2*q)) (6/(2*q-3)^2)).mulVec y) := by
  dsimp only
  have hq0 : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  rw [firstAtomOddFour_energy_eq hq,coordinates_centralBasis' hq0]
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

/-- **Native coercivity beyond scale six.** In first-atom central coordinates the complete native
odd quadratic form is at least `S/24` times the squared coordinate norm, `S = 8 q f₁²`. -/
theorem native_oddFour_coercive {x : ℝ}
    (hq : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (8*q*thetaCuspSourceTerm x 1^2)/24*(∑ i : Fin 4, y i^2) ≤
      ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x := by
  dsimp only
  have hq5 : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  set q := thetaCuspSingleAtomReflectionScale 1 x with hqdef
  set c := (centralBasis (1/q)).mulVec y with hcdef
  set S := 8*q*thetaCuspSourceTerm x 1^2 with hS
  have hq0 : 0 < q := by linarith
  have hS0 : 0 ≤ S := by positivity
  have hfirst := firstAtom_energy_central hq5 y
  have hsecond := secondPair_odd_nonneg hq5 c
  have hmix := mixedPairOddFour_exponential_floor_global hq5 y
  have htail := (abs_le.mp (native_central_tail_payment hq5 y)).1
  have he := twoAtom_odd_energy_decomposition hq5 y
  dsimp only at hfirst htail he
  -- first-atom coercivity at `v = 1/(2q) ≤ 1/12`
  have hcoer := centralMatrix_coercive (v := 1/(2*q)) (h := 6/(2*q-3)^2) (by positivity)
    (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    (by have : 2*q-3 ≠ 0 := by linarith
        field_simp) y
  have hquad : star y ⬝ᵥ (centralMatrix (1/(2*q)) (6/(2*q-3)^2)).mulVec y =
      ∑ i : Fin 4, ∑ j : Fin 4, y i*y j*centralMatrix (1/(2*q)) (6/(2*q-3)^2) i j := by
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hquad] at hfirst
  have hfirstL : S/6*(∑ i : Fin 4, y i^2) ≤ ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j := by
    rw [hfirst]
    have := mul_le_mul_of_nonneg_left hcoer hS0
    linarith
  have hmixA := mul_nonneg hS0 hmix
  have hsplit : (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x) =
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x) +
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x-
          thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit, he]
  have hy0 : 0 ≤ ∑ i : Fin 4, y i^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [hfirstL, hmixA, hsecond, htail, mul_nonneg hS0 hy0]

/-- The native odd reflection block is nonnegative beyond scale six. -/
theorem nativeOddFour_nonneg {x : ℝ} (hq : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (c : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x := by
  have hq0 : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have h := native_oddFour_coercive hq (coordinates (thetaCuspSingleAtomReflectionScale 1 x) c)
  dsimp only at h
  rw [centralBasis_coordinates' hq0] at h
  refine le_trans ?_ h
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (show 37/10 ≤
    thetaCuspSingleAtomReflectionScale 1 x by linarith)
  have : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  positivity


theorem signedJet_even_eq (x : ℝ) (m : ℕ) :
    thetaCuspNativeSignedJet x (2*m) = (-1:ℝ)^m*thetaCuspNativeReflectionJet (2*m) x := by
  unfold thetaCuspNativeSignedJet
  congr 1
  rw [pow_mul]
  have h : ((-Complex.I)^2 : ℂ) = ((-1:ℝ) : ℂ) := by simp
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **The bulk hypothesis of the seam split.** Beyond `r_c = log(6/π)` the odd native fibre form
is nonnegative. -/
theorem thetaCuspOddFourFibreForm_nonneg_of_log_six {r : ℝ} (hr : Real.log (6/Real.pi) < r)
    (v : Fin 4 → ℝ) : 0 ≤ thetaCuspOddFourFibreForm r v := by
  have hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2) := by
    have he : 6/Real.pi < Real.exp r := by
      rw [← Real.exp_log (by positivity : (0:ℝ) < 6/Real.pi)]
      exact Real.exp_lt_exp.mpr hr
    rw [div_lt_iff₀ Real.pi_pos] at he
    simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
    rw [show 2*(r/2) = r by ring]
    linarith
  have h := nativeOddFour_nonneg hscale v
  unfold thetaCuspOddFourFibreForm
  convert h using 3 with i _ j _
  rw [show 2*(i.val+j.val)+2 = 2*(i.val+j.val+1) by ring, signedJet_even_eq,
    pow_succ]
  ring


/-- **The eighth section from one seam inequality.** With the native bulk now proved beyond
scale six, `I_7(a) ≥ 0` at every critical aperture follows from the single aperture-free
inequality between the `r²`-weighted fibre beyond `log(6/π)` and its negative part below. -/
theorem thetaCuspNativeSuccessorIntegral_seven_nonneg_of_logSixSplit
    (hsplit : ∀ v : Fin 4 → ℝ,
      0 ≤ ∫ r in Set.Ioi 0, thetaCuspOddFourSeamSplitIntegrand (Real.log (6/Real.pi)) r v)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 ≤ ∫ r : ℝ in Set.Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a 7 (r/2) := by
  have hrc : 0 < Real.log (6/Real.pi) := Real.log_pos (by
    rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])
  exact thetaCuspNativeSuccessorIntegral_seven_nonneg_of_seamSplit hrc
    (fun r hr v => thetaCuspOddFourFibreForm_nonneg_of_log_six hr v) hsplit ha0 ha

end
end RHTower.ThetaCuspOddFourNativeBulk
