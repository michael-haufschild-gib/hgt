import GaloisForLFunctions.RHTower.ThetaCuspMiddleReflectionError
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomAffineEnergy
import GaloisForLFunctions.RHTower.ThetaCuspMiddleCompensationReserve
import GaloisForLFunctions.HTGeometry.TwoAtomMiddleEvenFourReserve
import GaloisForLFunctions.RHTower.ThetaCuspEvenFourInner
import GaloisForLFunctions.RHTower.ThetaCuspEvenFourCentralTail
/-! # Complete degree-six source positivity from the middle interval

The exact two-atom affine reserve absorbs the complete compensation and all
sixteen reflection-error entries. The inner and outer theorems then cover every
scale from 37/10, hence every physical center from one twelfth onward.
-/
namespace RHTower
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
/-- All sixteen complete-source entry errors obey the proved normalized quadratic budget. -/
theorem abs_nativeEvenEnergy_sub_two_middle {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let y := fun i : Fin 4 => (8*q)^i.val*c i
    |(∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*c j)-
      (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j)| ≤
      thetaCuspSourceTerm x 1^(2 : ℕ)*HTGeometry.middleEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let s := 8*q
  let f := thetaCuspSourceTerm x 1
  let y := fun i : Fin 4 => s^i.val*c i
  let e := fun k => HTGeometry.middleEvenErrorBound k q
  let T := fun i j : Fin 4 => c i*((-1 : ℝ)^(i.val+j.val)*
    (thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
      thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x))*c j
  have hs : 0 ≤ s := by dsimp [s,q]; linarith
  have hp (i j : Fin 4) : |T i j| ≤ f^(2 : ℕ)*e (i.val+j.val)*|y i*y j| := by
    have h := abs_thetaCuspNativeReflectionJet_sub_two_le_middle_budget (by linarith : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
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
      HTGeometry.middleEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3) := by
    norm_num [Fin.sum_univ_succ,HTGeometry.middleEvenErrorQuadratic,e,abs_mul]
    simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by rfl]
    ring_nf
  dsimp only
  rw [hid]
  change _ ≤ f^(2 : ℕ)*HTGeometry.middleEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3)
  rwa [he] at hb

/-- The retained source and the complete compensation supply all middle coordinate reserves. -/
theorem twoAtomEvenEnergy_fullCompensation_middle_reserve {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let y := fun i : Fin 4 => (8*q)^i.val*c i
    thetaCuspSourceTerm x 1^(2 : ℕ)*HTGeometry.middleEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) ≤
      (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j)+
      1000000000000*thetaCuspCenterCompensationSource x*(c 3)^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let s := 8*q
  let f := thetaCuspSourceTerm x 1
  let C := 4*q^(2 : ℕ)*Real.exp (x-2*q)
  let y := fun i : Fin 4 => s^i.val*c i
  let B := (c 0)^(2 : ℕ)/1000000+s^(2 : ℕ)*(c 1)^(2 : ℕ)/10000+s^(4 : ℕ)*(c 2)^(2 : ℕ)/10+s^(6 : ℕ)*(c 3)^(2 : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmass : C*(2*q-3)^(2 : ℕ) = f^(2 : ℕ) := thetaCuspAffineGaussian_mul_seedSquare x
  have hr := mul_le_mul_of_nonneg_left (HTGeometry.twoAtomMiddleEvenFourDiagonalReserve_le
    hq hqu (Real.exp_pos (-3*q)).le (HTGeometry.twoAtomMiddleEnvelope_exp_admission hq)
    (c 0) (c 1) (c 2) (c 3)) hC
  have ht := thetaCuspTwoAtomAffineCorrectedEnergy_le
    (by linarith : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) c
  have hQ : HTGeometry.twoAtomMiddleEvenFourQuadratic q (Real.exp (-3*q)) (c 0) (c 1) (c 2) (c 3) =
      HTGeometry.twoAtomAffineEvenFourCorrectedQuadratic q (Real.exp (-3*q)) (c 0) (c 1) (c 2) (c 3)-
        (1000000000000*(11/2-q)+240*s^(6 : ℕ))*(2*q-3)^(2 : ℕ)*(c 3)^(2 : ℕ) := by
    unfold HTGeometry.twoAtomMiddleEvenFourQuadratic HTGeometry.twoAtomAffineEvenFourCorrectedQuadratic
    dsimp [s]
    ring
  change C*((2*q-3)^(2 : ℕ)*B) ≤ C*HTGeometry.twoAtomMiddleEvenFourQuadratic q (Real.exp (-3*q)) (c 0) (c 1) (c 2) (c 3) at hr
  rw [← mul_assoc,hmass,hQ,mul_sub] at hr
  have hc : C*((1000000000000*(11/2-q)+240*s^(6 : ℕ))*(2*q-3)^(2 : ℕ)*(c 3)^(2 : ℕ)) =
      (1000000000000*(11/2-q)+240*s^(6 : ℕ))*f^(2 : ℕ)*(c 3)^(2 : ℕ) := by
    calc
      _ = (1000000000000*(11/2-q)+240*s^(6 : ℕ))*(C*(2*q-3)^(2 : ℕ))*(c 3)^(2 : ℕ) := by ring
      _ = _ := by rw [hmass]
  rw [hc] at hr
  have hg := mul_le_mul_of_nonneg_right (thetaCuspFullCompensation_lower_middle_240 hq hqu).le
    (sq_nonneg (c 3))
  have he : HTGeometry.middleEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) = B := by
    dsimp [HTGeometry.middleEvenCoordinateReserve,y,B]
    ring
  dsimp only
  change f^(2 : ℕ)*HTGeometry.middleEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) ≤ _
  rw [he]
  change C*HTGeometry.twoAtomAffineEvenFourCorrectedQuadratic q (Real.exp (-3*q)) (c 0) (c 1) (c 2) (c 3) ≤ _ at ht
  dsimp [q,s,f] at hr ht ⊢
  nlinarith only [hr,ht,hg]

/-- Complete-source degree-six positivity throughout the middle scale interval. -/
theorem thetaCuspNativeEvenFourFixed_posDef_middle {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) :
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
    have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos (thetaCusp_pos_of_thirtySevenTenths_le (by linarith : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x))
      (by norm_num : 0 < (1 : ℕ))
    have hy : y 0 ≠ 0 ∨ y 1 ≠ 0 ∨ y 2 ≠ 0 ∨ y 3 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hc
      funext i
      have hh : y i = 0 := by fin_cases i <;> simp_all
      exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hs)
    have hp := mul_lt_mul_of_pos_left (HTGeometry.middleEvenErrorQuadratic_lt_reserve
      hq (y 0) (y 1) (y 2) (y 3) hy) (sq_pos_of_pos hf)
    have he := abs_nativeEvenEnergy_sub_two_middle hq c
    have hr := twoAtomEvenEnergy_fullCompensation_middle_reserve hq hqu c
    have heq : star c ⬝ᵥ (thetaCuspNativeEvenFourCompensated 1000000000000 x).mulVec c =
      (∑ i : Fin 4, ∑ j : Fin 4, c i*((-1 : ℝ)^(i.val+j.val)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)*c j)+
        1000000000000*thetaCuspCenterCompensationSource x*(c 3)^(2 : ℕ) := by
      simp [thetaCuspNativeEvenFourCompensated,dotProduct,Matrix.mulVec,Fin.sum_univ_succ]
      ring
    rw [heq]
    dsimp only at he hr
    change _ ≤ f^(2 : ℕ)*HTGeometry.middleEvenErrorQuadratic q (y 0) (y 1) (y 2) (y 3) at he
    change f^(2 : ℕ)*HTGeometry.middleEvenCoordinateReserve q (y 0) (y 1) (y 2) (y 3) ≤ _ at hr
    have helo := (abs_le.mp he).1
    linarith only [hp,hr,helo]

/-- The complete fixed compensated matrix is positive on the entire scale ray beginning at 37/10. -/
theorem thetaCuspNativeEvenFourFixed_posDef_of_thirtySevenTenths_le {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (thetaCuspNativeEvenFourCompensated 1000000000000 x).PosDef := by
  by_cases h5 : thetaCuspSingleAtomReflectionScale 1 x ≤ 5
  · exact thetaCuspNativeEvenFourFixed_posDef_inner hq h5
  · by_cases h8 : thetaCuspSingleAtomReflectionScale 1 x ≤ 8
    · exact thetaCuspNativeEvenFourFixed_posDef_middle (by linarith) h8
    · exact thetaCuspNativeEvenFourFixed_posDef_of_eight_le (by linarith)
/-- The quadratic exponential bound places every center from one twelfth on the proved scale ray. -/
theorem thirtySevenTenths_le_firstAtomScale_of_twelfth_le {x : ℝ} (hx : 1/12 ≤ x) :
    37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have hx0 : 0 ≤ x := by linarith
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ 2*x by linarith) 3
  norm_num [Finset.sum_range_succ] at he
  have hp : (157/50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have he0 : 0 ≤ 1+2*x+(2*x)^(2 : ℕ)/2 := by positivity
  have hprod := mul_le_mul hp he he0 Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
  have hs := mul_nonneg (show 0 ≤ x-1/12 by linarith) (show 0 ≤ x+1/12 by linarith)
  nlinarith only [hprod,hx,hs]

/-- Complete fixed degree-six source positivity on every center from one twelfth onward. -/
theorem thetaCuspNativeEvenFourFixed_posDef_of_twelfth_le {x : ℝ} (hx : 1/12 ≤ x) :
    (thetaCuspNativeEvenFourCompensated 1000000000000 x).PosDef := by
  exact thetaCuspNativeEvenFourFixed_posDef_of_thirtySevenTenths_le
    (thirtySevenTenths_le_firstAtomScale_of_twelfth_le hx)
end
end RHTower
