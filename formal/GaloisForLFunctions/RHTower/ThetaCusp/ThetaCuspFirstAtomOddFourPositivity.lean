import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourGaussianFlow

/-!
# First-atom odd reflection positivity through order fourteen

The literal first theta atom has a positive definite signed odd reflection block
whenever its scale is at least five. An invertible triangular change to odd
central-factorial coordinates reduces the source energy to a strictly diagonally
dominant matrix. The exact affine jet recurrence identifies every entry, including
the fourteenth derivative; no asymptotic replacement is used.

The conclusion concerns the first atom. The unequal-pair terms in the complete
theta source require a separate signed estimate.
-/

namespace RHTower.ThetaCuspOddCentral
noncomputable section

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

/-- Exact normalized first-atom odd matrix, including finite-scale corrections. -/
def centralMatrix (v h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1+h,-h,0,0], ![-h,d1 v h,c12 v h,c13 v h],
    ![0,c12 v h,d2 v h,c23 v h], ![0,c13 v h,c23 v h,d3 v h]]

private theorem h_bounds {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/10)
    (hrel : h*(1-3*v)^2 = 6*v^2) : 0 ≤ h ∧ h ≤ 6/49 := by
  have hd : 0 < 1-3*v := by linarith
  have hD := sq_pos_of_pos hd
  have hh : 0 ≤ h := by nlinarith only [hrel, sq_nonneg v, hD]
  have hv2 : v^2 ≤ (1/10 : ℝ)^2 := by nlinarith
  have hDl : (7/10 : ℝ)^2 ≤ (1-3*v)^2 := by nlinarith
  have he := mul_nonneg hh (sub_nonneg.mpr hDl)
  exact ⟨hh,by nlinarith only [he,hrel,hv2]⟩

private theorem c12_bound {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/10)
    (hh : 0 ≤ h) (hhU : h ≤ 6/49) : |c12 v h| ≤ 10/49 := by
  have hp := mul_nonneg hv hh
  have hn := mul_nonneg hh (show 0 ≤ 5/3-5*v by linarith)
  unfold c12
  exact abs_le.mpr ⟨by nlinarith only [hv,hhU,hp], by nlinarith only [hvU,hn]⟩

private theorem c13_abs {v h : ℝ} (hv : 0 ≤ v) (hh : 0 ≤ h) :
    |c13 v h| = 5*v*h/2 := by
  unfold c13
  rw [abs_of_nonpos (by nlinarith [mul_nonneg hv hh])]
  ring

private theorem c23_bounds {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/10)
    (hh : 0 ≤ h) (hrel : h*(1-3*v)^2 = 6*v^2) :
    0 ≤ c23 v h ∧ c23 v h ≤ 3/16 := by
  let r := 1-10*v
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hD : 0 < (1-3*v)^2 := sq_pos_of_pos (by linarith)
  have hid : 4*(1-3*v)^2*c23 v h =
      (v/40)*(111+43*r+201*r^2+45*r^3) := by
    dsimp [r,c23]
    linear_combination 4*(-5/2+25*v-75*v^2/2)*hrel
  have hl : 0 ≤ c23 v h := by
    have hp : 0 ≤ (v/40)*(111+43*r+201*r^2+45*r^3) := by positivity
    nlinarith only [hid,hp,hD]
  have hn : 0 ≤ 5/2-25*v+75*v^2/2 := by nlinarith [sq_nonneg v]
  have hhterm := mul_nonneg hh hn
  have hu : 5*v/2-25*v^2/4 ≤ 3/16 := by
    have hp := mul_nonneg (show 0 ≤ 1-10*v by linarith)
      (show 0 ≤ 3-10*v by linarith)
    nlinarith only [hp]
  exact ⟨hl,by unfold c23; nlinarith only [hhterm,hu]⟩

private theorem last_row_positive {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/10)
    (hrel : h*(1-3*v)^2 = 6*v^2) :
    0 < d3 v h-5*v*h/2-c23 v h := by
  let r := 1-10*v
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrU : r ≤ 1 := by dsimp [r]; linarith
  have hid : 112000*(1-3*v)^2*(d3 v h-5*v*h/2-c23 v h) =
      6083+45941*r-13814*r^2+26166*r^3+14931*r^4+693*r^5 := by
    dsimp [r,d3,c23]
    linear_combination 112000*(15/2-(175/2)*v+(825/4)*v^2-75*v^3)*hrel
  have ht : 0 ≤ 45941*r-13814*r^2 := by
    nlinarith [mul_nonneg hr (show 0 ≤ 1-r by linarith)]
  have hp : 0 < 6083+45941*r-13814*r^2+26166*r^3+14931*r^4+693*r^5 := by
    have : 0 < 6083+(45941*r-13814*r^2)+26166*r^3+14931*r^4+693*r^5 := by
      positivity
    linarith only [this]
  rw [← hid] at hp
  by_contra hn
  have he := mul_nonneg (show 0 ≤ 112000*(1-3*v)^2 by positivity)
    (show 0 ≤ -(d3 v h-5*v*h/2-c23 v h) by linarith)
  nlinarith only [hp,he]

private theorem signed_cross_nonneg (c x y : ℝ) :
    0 ≤ |c| *(x^2+y^2)+2*c*x*y := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    have hp := mul_nonneg hc (sq_nonneg (x+y))
    nlinarith only [hp]
  · rw [abs_of_nonpos hc]
    have hp := mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg (x-y))
    nlinarith only [hp]

private theorem centralMatrix_posDef {v h : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/10)
    (hrel : h*(1-3*v)^2 = 6*v^2) : (centralMatrix v h).PosDef := by
  obtain ⟨hh,hhU⟩ := h_bounds hv hvU hrel
  obtain ⟨hc23,hc23U⟩ := c23_bounds hv hvU hh hrel
  have hc12 := c12_bound hv hvU hh hhU
  have hc13 := c13_abs hv hh
  have hc13U : 5*v*h/2 ≤ 3/98 := by
    have hp := mul_nonneg (sub_nonneg.mpr hvU) hh
    nlinarith only [hp,hhU]
  have hd1 : 17/30 ≤ d1 v h := by
    have hp := mul_nonneg hh (show 0 ≤ 1-v by linarith)
    unfold d1
    nlinarith only [hp,hvU]
  have hd2 : 5/12 ≤ d2 v h := by
    have hp := mul_nonneg hh (show 0 ≤ 1-5*v by linarith)
    have hq := mul_nonneg (sq_nonneg v) (show 0 ≤ 1+3*h by positivity)
    unfold d2
    nlinarith only [hp,hq,hvU]
  have hr1 : 0 < d1 v h-h-|c12 v h|-5*v*h/2 := by
    linarith only [hd1,hhU,hc12,hc13U]
  have hr2 : 0 < d2 v h-|c12 v h|-c23 v h := by
    linarith only [hd2,hc12,hc23U]
  have hr3 := last_row_positive hv hvU hrel
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [centralMatrix]
  · intro y hy
    have he01 := signed_cross_nonneg (-h) (y 0) (y 1)
    have he12 := signed_cross_nonneg (c12 v h) (y 1) (y 2)
    have he13 := signed_cross_nonneg (c13 v h) (y 1) (y 3)
    have he23 := signed_cross_nonneg (c23 v h) (y 2) (y 3)
    rw [abs_neg,abs_of_nonneg hh] at he01
    rw [hc13] at he13
    rw [abs_of_nonneg hc23] at he23
    have hreserve : 0 < (y 0)^2+
        (d1 v h-h-|c12 v h|-5*v*h/2)*(y 1)^2+
        (d2 v h-|c12 v h|-c23 v h)*(y 2)^2+
        (d3 v h-5*v*h/2-c23 v h)*(y 3)^2 := by
      by_contra hn
      have hs0 := sq_nonneg (y 0)
      have hs1 := mul_nonneg hr1.le (sq_nonneg (y 1))
      have hs2 := mul_nonneg hr2.le (sq_nonneg (y 2))
      have hs3 := mul_nonneg hr3.le (sq_nonneg (y 3))
      have hz0 : y 0 = 0 := by nlinarith only [hn,hs0,hs1,hs2,hs3]
      have hz1 : y 1 = 0 := by
        by_contra hi
        have hp := mul_pos hr1 (sq_pos_of_ne_zero hi)
        linarith only [hn,hs0,hs2,hs3,hp]
      have hz2 : y 2 = 0 := by
        by_contra hi
        have hp := mul_pos hr2 (sq_pos_of_ne_zero hi)
        linarith only [hn,hs0,hs1,hs3,hp]
      have hz3 : y 3 = 0 := by
        by_contra hi
        have hp := mul_pos hr3 (sq_pos_of_ne_zero hi)
        linarith only [hn,hs0,hs1,hs2,hp]
      apply hy
      funext i
      fin_cases i <;> simp [hz0,hz1,hz2,hz3]
    simp [centralMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    dsimp [c13] at he13 ⊢
    nlinarith only [hreserve,he01,he12,he13,he23]

end
end RHTower.ThetaCuspOddCentral

namespace RHTower.ThetaCuspOddCentral
noncomputable section
open ThetaCuspOddFour

private theorem even_odd_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (2*n), f i) =
      ∑ j ∈ Finset.range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [Finset.sum_range_succ,ih]
    ring

private theorem sinh_even (n : ℕ) :
    iteratedDeriv (2*n) (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sinh 2,Real.iteratedDeriv_even_sinh]
  simp

private theorem sinh_odd (n : ℕ) :
    iteratedDeriv (2*n+1) (fun t : ℝ => Real.sinh (2*t)) 0 = (2 : ℝ)^(2*n+1) := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sinh 2,Real.iteratedDeriv_odd_sinh]
  simp

private theorem affine_even_succ (n : ℕ) (q B : ℝ) :
    iteratedDeriv (2*(n+1)) (affine q B) 0 =
      -4*q * ∑ j ∈ Finset.range (n+1), ((2*n+1).choose (2*j+1) : ℝ)*
        (2 : ℝ)^(2*j+1)*iteratedDeriv (2*(n-j)) (affine q (B+6)) 0 := by
  have h := affine_jet_succ q B (2*n+1)
  have he : (fun t : ℝ => affine q B t+6*gaussian q t) = affine q (B+6) := by
    funext t
    dsimp [affine,factor]
    ring
  rw [show 2*n+1+1=2*(n+1) by omega,even_odd_sum,he] at h
  simp only [sinh_even,sinh_odd,mul_zero,zero_mul,zero_add] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (2*n+1)-(2*j+1)=2*(n-j) by omega]

private def affineRawMoment : ℕ → ℝ → ℝ → ℝ
  | 0, _, B => B
  | n+1, q, B => -4*q * ∑ j ∈ Finset.range (n+1),
      ((2*n+1).choose (2*j+1) : ℝ)*(2 : ℝ)^(2*j+1)*affineRawMoment (n-j) q (B+6)
termination_by n _ _ => n

private theorem affineRawMoment_eq (n : ℕ) (q B : ℝ) :
    affineRawMoment n q B = iteratedDeriv (2*n) (affine q B) 0 := by
  induction n using Nat.strong_induction_on generalizing B with
  | h n ih =>
    cases n with
    | zero => simp [affineRawMoment,affine,factor,gaussian]
    | succ n =>
      rw [affineRawMoment,affine_even_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih (n-j) (by omega)]

end
end RHTower.ThetaCuspOddCentral

namespace RHTower.ThetaCuspOddCentral
noncomputable section

private def m0 (_q B : ℝ) : ℝ := B
private def m1 (q B : ℝ) : ℝ := 8*q*(B+6)
private def m2 (q B : ℝ) : ℝ := 4*q*(6*m1 q (B+6)-8*m0 q (B+6))
private def m3 (q B : ℝ) : ℝ :=
  4*q*(10*m2 q (B+6)-80*m1 q (B+6)+32*m0 q (B+6))
private def m4 (q B : ℝ) : ℝ :=
  4*q*(14*m3 q (B+6)-280*m2 q (B+6)+672*m1 q (B+6)-128*m0 q (B+6))
private def m5 (q B : ℝ) : ℝ :=
  4*q*(18*m4 q (B+6)-672*m3 q (B+6)+4032*m2 q (B+6)-4608*m1 q (B+6)+512*m0 q (B+6))
private def m6 (q B : ℝ) : ℝ :=
  4*q*(22*m5 q (B+6)-1320*m4 q (B+6)+14784*m3 q (B+6)-42240*m2 q (B+6)+
    28160*m1 q (B+6)-2048*m0 q (B+6))
private def m7 (q B : ℝ) : ℝ :=
  4*q*(26*m6 q (B+6)-2288*m5 q (B+6)+41184*m4 q (B+6)-219648*m3 q (B+6)+
    366080*m2 q (B+6)-159744*m1 q (B+6)+8192*m0 q (B+6))

private theorem raw_zero (q B : ℝ) : affineRawMoment 0 q B = m0 q B := by
  rw [affineRawMoment]; rfl
private theorem raw_one (q B : ℝ) : affineRawMoment 1 q B = -m1 q B := by
  rw [affineRawMoment]
  norm_num only [Finset.sum_range_succ,Nat.choose,raw_zero,m0,m1]
  ring
private theorem raw_two (q B : ℝ) : affineRawMoment 2 q B = m2 q B := by
  rw [affineRawMoment]
  norm_num only [Finset.sum_range_succ,Nat.choose,raw_zero,raw_one,m2]
  ring
private theorem raw_three (q B : ℝ) : affineRawMoment 3 q B = -m3 q B := by
  rw [affineRawMoment]
  norm_num only [Finset.sum_range_succ,Nat.choose,raw_zero,raw_one,raw_two,m3]
  ring
private theorem raw_four (q B : ℝ) : affineRawMoment 4 q B = m4 q B := by
  rw [affineRawMoment]
  norm_num only [Finset.sum_range_succ,Nat.choose,raw_zero,raw_one,raw_two,raw_three,m4]
  ring
private theorem raw_five (q B : ℝ) : affineRawMoment 5 q B = -m5 q B := by
  rw [affineRawMoment]
  norm_num only [Finset.sum_range_succ,Nat.choose,raw_zero,raw_one,raw_two,raw_three,raw_four,m5]
  ring
private theorem raw_six (q B : ℝ) : affineRawMoment 6 q B = m6 q B := by
  rw [affineRawMoment]
  norm_num only [Finset.sum_range_succ,Nat.choose,raw_zero,raw_one,raw_two,raw_three,raw_four,raw_five,m6]
  ring
private theorem raw_seven (q B : ℝ) : affineRawMoment 7 q B = -m7 q B := by
  rw [affineRawMoment]
  norm_num only [Finset.sum_range_succ,Nat.choose,raw_zero,raw_one,raw_two,raw_three,raw_four,raw_five,raw_six,m7]
  ring

/-- Triangular odd central coordinates of a native coefficient vector. -/
def coordinates (q : ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let z3 := c 3
  let z2 := c 2-(56-168*q)*z3
  let z1 := c 1-(20-80*q)*z2-(784-3360*q+6720*q^2)*z3
  ![c 0-(4-24*q)*z1-(64-320*q+960*q^2)*z2-
      (2304-10752*q+26880*q^2-53760*q^3)*z3,
    -24*q*z1,768*q^2*z2,-43008*q^3*z3]

private theorem affine_energy_eq (q B : ℝ) (hq : q ≠ 0) (hB : B ≠ 0)
    (c : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1 : ℝ)^(i.val+j.val+1)*
      affineRawMoment (i.val+j.val+1) q B) =
    8*q*B*(star (coordinates q c) ⬝ᵥ
      (centralMatrix (1/(2*q)) (6/B)).mulVec (coordinates q c)) := by
  norm_num [Fin.sum_univ_succ,raw_zero,raw_one,raw_two,raw_three,raw_four,raw_five,raw_six,raw_seven,
    centralMatrix,coordinates,d1,c12,c13,d2,c23,d3,dotProduct,Matrix.mulVec]
  dsimp [m0,m1,m2,m3,m4,m5,m6,m7]
  field_simp [hq,hB]
  ring

end
end RHTower.ThetaCuspOddCentral

namespace RHTower.ThetaCuspOddCentral
noncomputable section
open ThetaCuspOddFour

private theorem coordinates_ne_zero {q : ℝ} (hq : 0 < q) {c : Fin 4 → ℝ}
    (hc : c ≠ 0) : coordinates q c ≠ 0 := by
  intro hy
  have hc3 : c 3 = 0 := by
    have h := congrFun hy 3
    simpa [coordinates,mul_eq_zero,hq.ne'] using h
  have hc2 : c 2 = 0 := by
    have h := congrFun hy 2
    simpa [coordinates,hc3,mul_eq_zero,hq.ne'] using h
  have hc1 : c 1 = 0 := by
    have h := congrFun hy 1
    simpa [coordinates,hc2,hc3,mul_eq_zero,hq.ne'] using h
  have hc0 : c 0 = 0 := by
    have h := congrFun hy 0
    simpa [coordinates,hc1,hc2,hc3] using h
  apply hc
  funext i
  fin_cases i <;> simp [hc0,hc1,hc2,hc3]

private theorem firstAtom_jet_affine (n : ℕ) (x : ℝ) :
    thetaCuspFirstAtomReflectionJet (2*n) x =
      let q := thetaCuspSingleAtomReflectionScale 1 x
      4*q^2*Real.exp (x-2*q)*affineRawMoment n q ((2*q-3)^2) := by
  dsimp only
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hf : (fun t : ℝ => thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1) =
      fun t => (4*q^2*Real.exp (x-2*q))*affine q ((2*q-3)^2) t := by
    funext t
    exact firstAtomPair_eq_affine x t
  unfold thetaCuspFirstAtomReflectionJet
  rw [hf,iteratedDeriv_const_mul_field,← affineRawMoment_eq]

/-- Signed odd reflection block of the literal first theta atom. -/
def firstAtomOddFour (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val+1)*
    thetaCuspFirstAtomReflectionJet (2*(i.val+j.val+1)) x

/-- The first theta atom has a strictly positive odd block through reflection order fourteen
on the scale-five ray. The proof retains every finite-scale correction. -/
theorem firstAtomOddFour_posDef {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) : (firstAtomOddFour x).PosDef := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hBp : 0 < 2*q-3 := by dsimp [q]; linarith
  have hv : 0 ≤ 1/(2*q) := by positivity
  have hvU : 1/(2*q) ≤ (1/10 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]
    linarith
  have hrel : (6/(2*q-3)^2)*(1-3*(1/(2*q)))^2 = 6*(1/(2*q))^2 := by
    field_simp [hqp.ne',hBp.ne']
  have hM := centralMatrix_posDef hv hvU hrel
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    simp [firstAtomOddFour,add_comm]
  · intro c hc
    have hpos := hM.dotProduct_mulVec_pos (coordinates_ne_zero hqp hc)
    have hid : star c ⬝ᵥ (firstAtomOddFour x).mulVec c =
        (4*q^2*Real.exp (x-2*q)) *
        (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1 : ℝ)^(i.val+j.val+1)*
          affineRawMoment (i.val+j.val+1) q ((2*q-3)^2)) := by
      simp only [firstAtomOddFour,dotProduct,Matrix.mulVec,Finset.mul_sum,
        Pi.star_apply,star_trivial,firstAtom_jet_affine]
      dsimp [q]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hid,affine_energy_eq q ((2*q-3)^2) hqp.ne' (pow_ne_zero 2 hBp.ne')]
    exact mul_pos (by positivity) (mul_pos (by positivity) hpos)

/-- Exact first-atom source energy in odd central coordinates. -/
theorem firstAtomOddFour_energy_eq {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j) =
      (4*q^2*Real.exp (x-2*q))*(8*q*(2*q-3)^2)*
        (star (coordinates q c) ⬝ᵥ
          (centralMatrix (1/(2*q)) (6/(2*q-3)^2)).mulVec (coordinates q c)) := by
  dsimp only
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hBp : 0 < 2*q-3 := by dsimp [q]; linarith
  have hid : (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*firstAtomOddFour x i j) =
      (4*q^2*Real.exp (x-2*q)) *
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1 : ℝ)^(i.val+j.val+1)*
        affineRawMoment (i.val+j.val+1) q ((2*q-3)^2)) := by
    simp only [firstAtomOddFour,firstAtom_jet_affine,Finset.mul_sum]
    dsimp [q]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid,affine_energy_eq q ((2*q-3)^2) hqp.ne' (pow_ne_zero 2 hBp.ne')]
  ring

end
end RHTower.ThetaCuspOddCentral
