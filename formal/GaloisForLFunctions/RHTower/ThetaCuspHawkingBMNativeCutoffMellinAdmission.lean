import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffOrbitSeparation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The original cutoff half-square has an admitted reflected Mellin moment with no source bound supplied. -/
open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

private theorem principal_shift (s : ℂ) (y : ℝ) :
    principal (s-1/2) ![0,y] =
      reflectedCompletedLambda (2*s-1)*(y:ℂ)^(1-s)+reflectedCompletedLambda (2*s)*(y:ℂ)^s := by
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,Bool.false_eq_true,if_false,if_true,mul_one]
  norm_num only
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [show (2:ℂ)*(s-1/2)=2*s-1 by ring,
    show (1:ℂ)+(2*s-1)=2*s by ring,
    show (1/2:ℂ)+(-1)*(s-1/2)=1-s by ring,
    show (1/2:ℂ)+1*(s-1/2)=s by ring]

/-- The unchanged two-Weyl cutoff height is continuous on the entire real line. -/
theorem nativeSquareCutoffHeight_continuous (q : XiZeroCopy) : Continuous (nativeSquareCutoffHeight q) := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  have hp : Continuous (fun y : ℝ => principal (center q) ![0,y]) := by
    have he : (fun y : ℝ => principal (center q) ![0,y]) = fun y : ℝ =>
      reflectedCompletedLambda (2*(q.1:ℂ)-1)*(y:ℂ)^(1-(q.1:ℂ))+
        reflectedCompletedLambda (2*(q.1:ℂ))*(y:ℂ)^(q.1:ℂ) := funext (principal_shift (q.1:ℂ))
    rw [he]
    exact (continuous_const.mul (Complex.continuous_ofReal_cpow_const (by
      change 0 < 1-(q.1:ℂ).re; linarith [hq.2]))).add
      (continuous_const.mul (Complex.continuous_ofReal_cpow_const hq.1))
  have hc : Continuous (fun y : ℝ => cutoff ![0,y]) := by
    change Continuous (fun y : ℝ => (Real.smoothTransition (y-2):ℂ))
    exact Complex.continuous_ofReal.comp ((Real.smoothTransition.contDiff (n := 1)).continuous.comp
      (continuous_id.sub continuous_const))
  exact hc.mul ((hp.pow 2).div_const 2)

/-- The full original cutoff half-square has one explicit quadratic height envelope. -/
theorem nativeSquareCutoffHeight_quadratic_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖nativeSquareCutoffHeight q y‖ ≤ C*y^(2 : ℕ) := by
  let B : ℝ := ‖reflectedCompletedLambda (2*(q.1:ℂ)-1)‖+‖reflectedCompletedLambda (2*(q.1:ℂ))‖
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨B^(2 : ℕ)/2,by positivity,?_⟩
  intro y
  by_cases hy : y ≤ 2
  · rw [nativeSquareCutoffHeight_zero q y hy,norm_zero]
    positivity
  · have hy2 : 2 < y := lt_of_not_ge hy
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hq := xi_divisor_support_re_mem_open_unit q.1
    have hpow (s : ℂ) (hs : s.re ≤ 1) : ‖(y:ℂ)^s‖ ≤ y := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy1 hs
    have hm := hpow (1-(q.1:ℂ)) (by change 1-(q.1:ℂ).re ≤ 1; linarith [hq.1])
    have hp := hpow (q.1:ℂ) hq.2.le
    have hprincipal : ‖principal (center q) ![0,y]‖ ≤ B*y := by
      change ‖principal ((q.1:ℂ)-1/2) ![0,y]‖ ≤ _
      rw [principal_shift]
      calc
        _ ≤ ‖reflectedCompletedLambda (2*(q.1:ℂ)-1)*(y:ℂ)^(1-(q.1:ℂ))‖+
            ‖reflectedCompletedLambda (2*(q.1:ℂ))*(y:ℂ)^(q.1:ℂ)‖ := norm_add_le _ _
        _ ≤ ‖reflectedCompletedLambda (2*(q.1:ℂ)-1)‖*y+
            ‖reflectedCompletedLambda (2*(q.1:ℂ))‖*y := by
          simp only [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
        _ = B*y := by dsimp [B]; ring
    have hc : ‖cutoff ![0,y]‖ ≤ 1 := by
      change ‖(Real.smoothTransition (y-2):ℂ)‖ ≤ 1
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    unfold nativeSquareCutoffHeight principalSquare
    rw [norm_mul,norm_div,norm_pow]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ ‖principal (center q) ![0,y]‖^(2 : ℕ)/2 := by nlinarith [sq_nonneg ‖principal (center q) ![0,y]‖]
      _ ≤ (B*y)^(2 : ℕ)/2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hprincipal
      _ = B^(2 : ℕ)/2*y^(2 : ℕ) := by ring

/-- The actual reflected cutoff moment is absolutely admitted in its common strict chamber. -/
theorem nativeSquareCutoffHeight_reflected_mellin_integrable (q : XiZeroCopy) (s : ℂ)
    (hs : 2 < s.re) :
    IntegrableOn (fun y : ℝ => (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y) (Ioi (2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := nativeSquareCutoffHeight_quadratic_bound q
  have hc : ContinuousOn (fun y : ℝ => (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y) (Ioi (2:ℝ)) := by
    intro y hy
    change (2:ℝ) < y at hy
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (by linarith : y ≠ 0))).mul
      (nativeSquareCutoffHeight_continuous q).continuousAt).continuousWithinAt
  have hg : IntegrableOn (fun y : ℝ => C*y^(1-s.re)) (Ioi (2:ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : 1-s.re < -1) (by norm_num : (0:ℝ)<2)).const_mul C
  apply hg.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ)<2) hy
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  calc
    _ ≤ y^(-s-1).re*(C*y^(2 : ℕ)) := mul_le_mul_of_nonneg_left (hb y) (Real.rpow_nonneg hy0.le _)
    _ = C*y^(1-s.re) := by
      rw [show (-s-1).re = -s.re-1 by simp,← Real.rpow_two,← mul_assoc,mul_comm (y^(-s.re-1)) C,
        mul_assoc,← Real.rpow_add hy0]
      congr 2
      ring

end
end RHTower.D4BMJointSource
