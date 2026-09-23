import GaloisForLFunctions.HTGeometry.TwoAtomAffineEvenFour
import GaloisForLFunctions.RHTower.ThetaCuspPairRadialRecurrence
import GaloisForLFunctions.RHTower.ThetaCuspMiddleCompensationBounds

/-!
# Literal radial moments and the scale-dependent complete-source correction

The full correction is at least `(11/2-q)*F^(2 : ℕ)` on the closed inner scale
interval. This preserves the stronger reserve at its lower end. Every affine
moment through order twelve is identified with the exact theta-pair radial
recurrence, retaining both ordered unequal-atom pairs. The resulting corrected
affine determinant exceeds `10^(20 : ℕ)`. Complete-tail absorption remains separate.
-/
namespace RHTower
noncomputable section
open Polynomial
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

/-- An affine center bound obtained from the quadratic exponential lower bound. -/
theorem ten_mul_center_add_five_halves_le_firstAtomScale {x : ℝ} (hx : 0 ≤ x) :
    10*x+5/2 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ 2*x by linarith) 3
  norm_num [Finset.sum_range_succ] at he
  have hp : (25/8 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have he0 : 0 ≤ 1+2*x+(2*x)^(2 : ℕ)/2 := by positivity
  have hprod := mul_le_mul hp he he0 Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
  nlinarith [sq_nonneg (x-3/10)]

/-- The full correction keeps its scale-dependent reserve across the inner interval. -/
theorem thetaCuspCenterCompensationSource_affine_lower_on_scale_five {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    (11/2-thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspFullSource x^(2 : ℕ) ≤
      thetaCuspCenterCompensationSource x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hF := thetaCuspFullSource_pos_all x
  have hd := mul_le_mul_of_nonneg_left (thetaCuspFullSource_slope_lower_on_scale_five hq hqu)
    (show 0 ≤ 2*x*thetaCuspFullSource x by positivity)
  have hb := mul_le_mul_of_nonneg_right
    (ten_mul_center_add_five_halves_le_firstAtomScale hx.le) (sq_nonneg (thetaCuspFullSource x))
  unfold thetaCuspCenterCompensationSource
  nlinarith only [hd,hb]

/-- The same complete correction controls the first-atom normalization used in the affine determinant. -/
theorem thetaCuspCenterCompensationSource_firstAtom_affine_lower_on_scale_five {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    (11/2-thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspSourceTerm x 1^(2 : ℕ) ≤
      thetaCuspCenterCompensationSource x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hm := pow_le_pow_left₀ hf.le (thetaCuspFullSource_mass_bounds_middle hq).1 2
  exact (mul_le_mul_of_nonneg_left hm (by linarith)).trans
    (thetaCuspCenterCompensationSource_affine_lower_on_scale_five hq hqu)

/-- First diagonal pair and both ordered mixed pairs in their common Gaussian normalization. -/
def thetaCuspTwoAtomAffineEvenMoment (k : ℕ) (q z : ℝ) : ℝ :=
  (thetaPairRadialEvenPolynomial (q^(2 : ℕ)) k).eval (2*q)+
    8*z*(thetaPairRadialEvenPolynomial (4*q^(2 : ℕ)) k).eval (5*q)

/-- Exact affine radial identification at signed even moment 0. -/
theorem thetaCuspTwoAtomAffineEvenMoment_0_eq (q z : ℝ) :
    thetaCuspTwoAtomAffineEvenMoment 0 q z = HTGeometry.twoAtomAffineEvenMoment0 q z := by
  unfold thetaCuspTwoAtomAffineEvenMoment
  simp [thetaPairRadialEvenPolynomial,HTGeometry.twoAtomAffineEvenMoment0]
  ring

/-- Exact affine radial identification at signed even moment 1. -/
theorem thetaCuspTwoAtomAffineEvenMoment_1_eq (q z : ℝ) :
    thetaCuspTwoAtomAffineEvenMoment 1 q z = HTGeometry.twoAtomAffineEvenMoment1 q z := by
  unfold thetaCuspTwoAtomAffineEvenMoment
  conv_lhs =>
    conv in thetaPairRadialEvenPolynomial (q^(2 : ℕ)) 1 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    conv in thetaPairRadialEvenPolynomial (4*q^(2 : ℕ)) 1 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_neg,eval_ofNat]
    ring_nf
  unfold HTGeometry.twoAtomAffineEvenMoment1 HTGeometry.twoAtomAffinePart HTGeometry.twoAtomOddNumerator1
  ring

/-- Exact affine radial identification at signed even moment 2. -/
theorem thetaCuspTwoAtomAffineEvenMoment_2_eq (q z : ℝ) :
    thetaCuspTwoAtomAffineEvenMoment 2 q z = HTGeometry.twoAtomAffineEvenMoment2 q z := by
  unfold thetaCuspTwoAtomAffineEvenMoment
  conv_lhs =>
    conv in thetaPairRadialEvenPolynomial (q^(2 : ℕ)) 2 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    conv in thetaPairRadialEvenPolynomial (4*q^(2 : ℕ)) 2 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_neg,eval_ofNat]
    ring_nf
  unfold HTGeometry.twoAtomAffineEvenMoment2 HTGeometry.twoAtomAffinePart HTGeometry.twoAtomOddNumerator2
  ring

/-- Exact affine radial identification at signed even moment 3. -/
theorem thetaCuspTwoAtomAffineEvenMoment_3_eq (q z : ℝ) :
    thetaCuspTwoAtomAffineEvenMoment 3 q z = HTGeometry.twoAtomAffineEvenMoment3 q z := by
  unfold thetaCuspTwoAtomAffineEvenMoment
  conv_lhs =>
    conv in thetaPairRadialEvenPolynomial (q^(2 : ℕ)) 3 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    conv in thetaPairRadialEvenPolynomial (4*q^(2 : ℕ)) 3 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_neg,eval_ofNat]
    ring_nf
  unfold HTGeometry.twoAtomAffineEvenMoment3 HTGeometry.twoAtomAffinePart HTGeometry.twoAtomOddNumerator3
  ring

/-- Exact affine radial identification at signed even moment 4. -/
theorem thetaCuspTwoAtomAffineEvenMoment_4_eq (q z : ℝ) :
    thetaCuspTwoAtomAffineEvenMoment 4 q z = HTGeometry.twoAtomAffineEvenMoment4 q z := by
  unfold thetaCuspTwoAtomAffineEvenMoment
  conv_lhs =>
    conv in thetaPairRadialEvenPolynomial (q^(2 : ℕ)) 4 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
            conv =>
              arg 2
              rw [thetaPairRadialEvenPolynomial]
            unfold thetaPairRadialEvenStep
            simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
              derivative_neg,derivative_pow,C_ofNat]
            ring_nf
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    conv in thetaPairRadialEvenPolynomial (4*q^(2 : ℕ)) 4 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
            conv =>
              arg 2
              rw [thetaPairRadialEvenPolynomial]
            unfold thetaPairRadialEvenStep
            simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
              derivative_neg,derivative_pow,C_ofNat]
            ring_nf
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_neg,eval_ofNat]
    ring_nf
  unfold HTGeometry.twoAtomAffineEvenMoment4 HTGeometry.twoAtomAffinePart HTGeometry.twoAtomOddNumerator4
  ring

/-- Exact affine radial identification at signed even moment 5. -/
theorem thetaCuspTwoAtomAffineEvenMoment_5_eq (q z : ℝ) :
    thetaCuspTwoAtomAffineEvenMoment 5 q z = HTGeometry.twoAtomAffineEvenMoment5 q z := by
  unfold thetaCuspTwoAtomAffineEvenMoment
  conv_lhs =>
    conv in thetaPairRadialEvenPolynomial (q^(2 : ℕ)) 5 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
            conv =>
              arg 2
              rw [thetaPairRadialEvenPolynomial]
              conv =>
                arg 2
                rw [thetaPairRadialEvenPolynomial]
              unfold thetaPairRadialEvenStep
              simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                derivative_neg,derivative_pow,C_ofNat]
              ring_nf
            unfold thetaPairRadialEvenStep
            simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
              derivative_neg,derivative_pow,C_ofNat]
            ring_nf
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    conv in thetaPairRadialEvenPolynomial (4*q^(2 : ℕ)) 5 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
            conv =>
              arg 2
              rw [thetaPairRadialEvenPolynomial]
              conv =>
                arg 2
                rw [thetaPairRadialEvenPolynomial]
              unfold thetaPairRadialEvenStep
              simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                derivative_neg,derivative_pow,C_ofNat]
              ring_nf
            unfold thetaPairRadialEvenStep
            simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
              derivative_neg,derivative_pow,C_ofNat]
            ring_nf
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_neg,eval_ofNat]
    ring_nf
  unfold HTGeometry.twoAtomAffineEvenMoment5 HTGeometry.twoAtomAffinePart HTGeometry.twoAtomOddNumerator5
  ring

/-- Exact affine radial identification at signed even moment 6. -/
theorem thetaCuspTwoAtomAffineEvenMoment_6_eq (q z : ℝ) :
    thetaCuspTwoAtomAffineEvenMoment 6 q z = HTGeometry.twoAtomAffineEvenMoment6 q z := by
  unfold thetaCuspTwoAtomAffineEvenMoment
  conv_lhs =>
    conv in thetaPairRadialEvenPolynomial (q^(2 : ℕ)) 6 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
            conv =>
              arg 2
              rw [thetaPairRadialEvenPolynomial]
              conv =>
                arg 2
                rw [thetaPairRadialEvenPolynomial]
                conv =>
                  arg 2
                  rw [thetaPairRadialEvenPolynomial]
                unfold thetaPairRadialEvenStep
                simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                  derivative_neg,derivative_pow,C_ofNat]
                ring_nf
              unfold thetaPairRadialEvenStep
              simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                derivative_neg,derivative_pow,C_ofNat]
              ring_nf
            unfold thetaPairRadialEvenStep
            simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
              derivative_neg,derivative_pow,C_ofNat]
            ring_nf
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    conv in thetaPairRadialEvenPolynomial (4*q^(2 : ℕ)) 6 =>
      rw [thetaPairRadialEvenPolynomial]
      conv =>
        arg 2
        rw [thetaPairRadialEvenPolynomial]
        conv =>
          arg 2
          rw [thetaPairRadialEvenPolynomial]
          conv =>
            arg 2
            rw [thetaPairRadialEvenPolynomial]
            conv =>
              arg 2
              rw [thetaPairRadialEvenPolynomial]
              conv =>
                arg 2
                rw [thetaPairRadialEvenPolynomial]
                conv =>
                  arg 2
                  rw [thetaPairRadialEvenPolynomial]
                unfold thetaPairRadialEvenStep
                simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                  derivative_neg,derivative_pow,C_ofNat]
                ring_nf
              unfold thetaPairRadialEvenStep
              simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
                derivative_neg,derivative_pow,C_ofNat]
              ring_nf
            unfold thetaPairRadialEvenStep
            simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
              derivative_neg,derivative_pow,C_ofNat]
            ring_nf
          unfold thetaPairRadialEvenStep
          simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
            derivative_neg,derivative_pow,C_ofNat]
          ring_nf
        unfold thetaPairRadialEvenStep
        simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
          derivative_neg,derivative_pow,C_ofNat]
        ring_nf
      unfold thetaPairRadialEvenStep
      simp [derivative_sub,derivative_mul,derivative_C,derivative_X,derivative_add,
        derivative_neg,derivative_pow,C_ofNat]
      ring_nf
    simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_neg,eval_ofNat]
    ring_nf
  unfold HTGeometry.twoAtomAffineEvenMoment6
  ring

/-- The source-identified radial affine determinant carries the positive fourth-coordinate margin. -/
theorem thetaCuspTwoAtomRadialAffineFourCorrectedDet_lower {q : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) :
    100000000000000000000 <
      GaloisForLFunctions.HTGeometry.hankelFourDet
        (thetaCuspTwoAtomAffineEvenMoment 0 q (1/HTGeometry.twoAtomLowerEnvelope q))
        (thetaCuspTwoAtomAffineEvenMoment 1 q (1/HTGeometry.twoAtomLowerEnvelope q))
        (thetaCuspTwoAtomAffineEvenMoment 2 q (1/HTGeometry.twoAtomLowerEnvelope q))
        (thetaCuspTwoAtomAffineEvenMoment 3 q (1/HTGeometry.twoAtomLowerEnvelope q))
        (thetaCuspTwoAtomAffineEvenMoment 4 q (1/HTGeometry.twoAtomLowerEnvelope q))
        (thetaCuspTwoAtomAffineEvenMoment 5 q (1/HTGeometry.twoAtomLowerEnvelope q))
        (thetaCuspTwoAtomAffineEvenMoment 6 q (1/HTGeometry.twoAtomLowerEnvelope q)+
          1000000000000*(11/2-q)*(2*q-3)^(2 : ℕ)) := by
  rw [thetaCuspTwoAtomAffineEvenMoment_0_eq,thetaCuspTwoAtomAffineEvenMoment_1_eq,
    thetaCuspTwoAtomAffineEvenMoment_2_eq,thetaCuspTwoAtomAffineEvenMoment_3_eq,
    thetaCuspTwoAtomAffineEvenMoment_4_eq,thetaCuspTwoAtomAffineEvenMoment_5_eq,
    thetaCuspTwoAtomAffineEvenMoment_6_eq]
  exact HTGeometry.twoAtomAffineEvenFourCorrectedDet_lower hq hqu

end
end RHTower
