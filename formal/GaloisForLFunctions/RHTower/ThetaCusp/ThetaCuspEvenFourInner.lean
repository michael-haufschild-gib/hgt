import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspInnerReflectionError
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomAffineEnergy
import GaloisForLFunctions.HTGeometry.TwoAtomInnerQuadraticAbsorption
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeEvenFourTail

/-!
# Complete compensated source positivity on the inner scale interval

All sixteen native entry errors fit the strict quadratic budget. The literal
two-atom affine energy and complete center compensation supply its four
reserves. Every nonzero coefficient vector therefore has positive energy.
-/
namespace RHTower
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

/-- All sixteen complete-source entry errors obey the proved normalized quadratic budget. -/
theorem abs_nativeEvenEnergy_sub_two_inner {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let y := fun i : Fin 4 => (8*q)^i.val*c i
    |(∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*c j)-
      (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j)| ≤
      thetaCuspSourceTerm x 1^(2 : ℕ)*HTGeometry.innerEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let s := 8*q
  let f := thetaCuspSourceTerm x 1
  let y := fun i : Fin 4 => s^i.val*c i
  let e := fun k => HTGeometry.innerEvenErrorBound k q
  let T := fun i j : Fin 4 => c i*((-1 : ℝ)^(i.val+j.val)*
    (thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
      thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x))*c j
  have hs : 0 ≤ s := by dsimp [s,q]; linarith
  have hp (i j : Fin 4) : |T i j| ≤ f^(2 : ℕ)*e (i.val+j.val)*|y i*y j| := by
    have h := abs_thetaCuspNativeReflectionJet_sub_two_le_inner_budget hq hqu
      (⟨i.val+j.val,by omega⟩ : Fin 7)
    have hm := mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg (c i)) (abs_nonneg (c j)))
    have hy : |y i*y j| = |c i| * |c j| * s^(i.val+j.val) := by
      dsimp [y]
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hs _),
        abs_of_nonneg (pow_nonneg hs _),pow_add]
      ring
    change |c i| * |c j| * |thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
      thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x| ≤
      |c i| * |c j| * (f^(2 : ℕ)*s^(i.val+j.val)*e (i.val+j.val)) at hm
    calc
      _ = |c i| * |c j| * |thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
          thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x| := by
        dsimp [T]
        simp only [abs_mul,abs_pow]
        norm_num only [abs_neg,abs_one,one_pow,one_mul]
        ring
      _ ≤ _ := hm
      _ = _ := by rw [hy]; ring
  have hid : (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*c j)-
      (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j) = ∑ i, ∑ j, T i j := by
    simp only [T,mul_sub,sub_mul,Finset.sum_sub_distrib]
  have hb : |∑ i, ∑ j, T i j| ≤ f^(2 : ℕ)*(∑ i, ∑ j, e (i.val+j.val)*|y i*y j|) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i, ∑ j, |T i j| := Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, f^(2 : ℕ)*e (i.val+j.val)*|y i*y j| :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hp i j
      _ = _ := by simp only [Finset.mul_sum,mul_assoc]
  have he : (∑ i : Fin 4, ∑ j : Fin 4, e (i.val+j.val)*|y i*y j|) =
      HTGeometry.innerEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3) := by
    norm_num [Fin.sum_univ_succ,HTGeometry.innerEvenErrorQuadratic,e,abs_mul]
    simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by rfl]
    ring_nf
  dsimp only
  rw [hid]
  change _ ≤ f^(2 : ℕ)*HTGeometry.innerEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3)
  rwa [he] at hb

/-- The literal retained source and the full compensation supply all four normalized reserves. -/
theorem twoAtomEvenEnergy_fullCompensation_inner_reserve {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let y := fun i : Fin 4 => (8*q)^i.val*c i
    thetaCuspSourceTerm x 1^(2 : ℕ)*HTGeometry.innerEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) ≤
      (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j)+
      1000000000000*thetaCuspCenterCompensationSource x*(c 3)^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let s := 8*q
  let f := thetaCuspSourceTerm x 1
  let C := 4*q^(2 : ℕ)*Real.exp (x-2*q)
  let y := fun i : Fin 4 => s^i.val*c i
  let B := (c 0)^(2 : ℕ)/1000000+s^(2 : ℕ)*(c 1)^(2 : ℕ)/10000+s^(4 : ℕ)*(c 2)^(2 : ℕ)/10+
    (500*(5-q)^(2 : ℕ)+1)*s^(6 : ℕ)*(c 3)^(2 : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hqp : 0 < q := by dsimp [q]; linarith
  have hs : s ≠ 0 := by dsimp [s]; positivity
  have hmass : C*(2*q-3)^(2 : ℕ) = f^(2 : ℕ) := thetaCuspAffineGaussian_mul_seedSquare x
  have hr := mul_le_mul_of_nonneg_left (HTGeometry.twoAtomAffineEvenFourDiagonalReserve_le
    hq hqu (Real.exp_pos (-3*q)).le (thetaCuspTwoAtom_lower_envelope_admission hq)
    (c 0) (c 1) (c 2) (c 3)) hC
  have ht := thetaCuspTwoAtomAffineCorrectedEnergy_le hq c
  have hb : f^(2 : ℕ)*B ≤ (∑ i : Fin 4, ∑ j : Fin 4,
      c i*((-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j)+
      1000000000000*(11/2-q)*f^(2 : ℕ)*(c 3)^(2 : ℕ) := by
    have hh := hr.trans ht
    change C*((2*q-3)^(2 : ℕ)*B) ≤ _ at hh
    rwa [← mul_assoc,hmass] at hh
  dsimp only
  change f^(2 : ℕ)*HTGeometry.innerEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) ≤ _
  by_cases hl : q ≤ 9/2
  · have hg := mul_le_mul_of_nonneg_left
      (thetaCuspCenterCompensationSource_firstAtom_extra_inner hq hl)
      (show 0 ≤ (1000000000000 : ℝ)*(c 3)^(2 : ℕ) by positivity)
    have he : HTGeometry.innerEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) =
        B+1000000000000*(2/5)*(q-5/2)*(9/2-q)*(c 3)^(2 : ℕ) := by
      dsimp [HTGeometry.innerEvenCoordinateReserve,y,B]
      rw [if_pos hl]
      unfold HTGeometry.innerExtraCompensation
      dsimp [s]
      field_simp [hqp.ne']
      ring
    rw [he]
    dsimp [q,f] at hb ⊢
    nlinarith only [hb,hg]
  · have hg := mul_le_mul_of_nonneg_left
      (thetaCuspCenterCompensationSource_firstAtom_affine_lower_on_scale_five hq hqu)
      (show 0 ≤ (1000000000000 : ℝ)*(c 3)^(2 : ℕ) by positivity)
    have he : HTGeometry.innerEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) = B := by
      dsimp [HTGeometry.innerEvenCoordinateReserve,y,B]
      rw [if_neg hl]
      ring
    rw [he]
    dsimp [q,f] at hb ⊢
    nlinarith only [hb,hg]

/-- Complete-source degree-six positivity throughout the inner scale interval. -/
theorem thetaCuspNativeEvenFourFixed_posDef_inner {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    (thetaCuspNativeEvenFourCompensated 1000000000000 x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspNativeEvenFourCompensated,add_comm,and_comm]
  · intro c hc
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let s := 8*q
    let f := thetaCuspSourceTerm x 1
    let y := fun i : Fin 4 => s^i.val*c i
    have hqp : 0 < q := by dsimp [q]; linarith
    have hs : s ≠ 0 := by dsimp [s]; positivity
    have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos (thetaCusp_pos_of_thirtySevenTenths_le hq)
      (by norm_num : 0 < (1 : ℕ))
    have hy : y 0 ≠ 0 ∨ y 1 ≠ 0 ∨ y 2 ≠ 0 ∨ y 3 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hc
      funext i
      have hh : y i = 0 := by fin_cases i <;> simp_all
      exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hs)
    have hp := mul_lt_mul_of_pos_left (HTGeometry.innerEvenErrorQuadratic_lt_reserve
      hq hqu (y 0) (y 1) (y 2) (y 3) hy) (sq_pos_of_pos hf)
    have he := abs_nativeEvenEnergy_sub_two_inner hq hqu c
    have hr := twoAtomEvenEnergy_fullCompensation_inner_reserve hq hqu c
    have heq : star c ⬝ᵥ (thetaCuspNativeEvenFourCompensated 1000000000000 x).mulVec c =
      (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*c j)+
        1000000000000*thetaCuspCenterCompensationSource x*(c 3)^(2 : ℕ) := by
      simp [thetaCuspNativeEvenFourCompensated,dotProduct,Matrix.mulVec,Fin.sum_univ_succ]
      ring
    rw [heq]
    dsimp only at he hr
    change _ ≤ f^(2 : ℕ)*HTGeometry.innerEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3) at he
    change f^(2 : ℕ)*HTGeometry.innerEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) ≤ _ at hr
    have helo := (abs_le.mp he).1
    linarith only [hp,hr,helo]
end
end RHTower
