import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineHeightCorrection

/-!
# Uniform spline bounds on a positive real strip

On `d ≤ δ ≤ D` with `d > 0`, finite numerator coefficients have a common
upper bound. Reciprocal numerator and dual-primitive bounds decrease with δ;
the Blaschke coefficient bound does too. These estimates separate strip
constants from the frequency-window costs in exact spline correction.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- A fixed coefficient envelope on a bounded positive real strip. -/
def splineNumeratorEnvelope (D : ℝ) : ℝ :=
  (∑ j : Fin 9, (Nat.choose 8 j.val : ℝ)/256)*Real.exp (8*D)

lemma splineNumeratorBound_le_envelope {δ D : ℝ} (hδ : 0 ≤ δ) (hD : δ ≤ D) :
    splineNumeratorBound δ ≤ splineNumeratorEnvelope D := by
  unfold splineNumeratorBound splineNumeratorEnvelope
  rw [sum_mul]
  apply sum_le_sum
  intro j _
  have hc : 0 ≤ (Nat.choose 8 j.val : ℝ)/256 := by positivity
  have he : splineShift j*δ ≤ 8*D := by
    have hs := (le_abs_self (splineShift j)).trans (abs_splineShift_le j)
    exact (mul_le_mul_of_nonneg_right hs hδ).trans (mul_le_mul_of_nonneg_left hD (by norm_num))
  have ha : |splineCoefficient δ j|=((Nat.choose 8 j.val : ℝ)/256)*Real.exp (splineShift j*δ) := by
    simp only [splineCoefficient, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (Nat.cast_nonneg (Nat.choose 8 j.val) : (0 : ℝ) ≤ (Nat.choose 8 j.val : ℝ)), abs_of_pos (by norm_num : (0 : ℝ)<256),
      abs_of_pos (Real.exp_pos _)]
  rw [ha]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hc

lemma inverseSplineBound_pos {δ : ℝ} (hδ : 0 < δ) : 0 < inverseSplineBound δ := by
  have hd : 0 < 1-splineRatio δ := sub_pos.mpr (splineRatio_lt_one hδ)
  unfold inverseSplineBound
  exact mul_pos (splineInvScale_pos δ) (by positivity)

lemma inverseSplineBound_antitone {d δ : ℝ} (hd : 0 < d) (hdδ : d ≤ δ) :
    inverseSplineBound δ ≤ inverseSplineBound d := by
  have hr : splineRatio δ ≤ splineRatio d := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hdδ]
  have hden : 0 < 1-splineRatio d := sub_pos.mpr (splineRatio_lt_one hd)
  have hpow := pow_le_pow_left₀ hden.le (sub_le_sub_left hr 1) 8
  have hi : 1/(1-splineRatio δ)^8 ≤ 1/(1-splineRatio d)^8 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hden 8) hpow
  have hs : splineInvScale δ ≤ splineInvScale d := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    nlinarith only [hdδ]
  exact mul_le_mul hs hi (by positivity) (splineInvScale_pos d).le

lemma splineDualBound_le_strip {d δ s : ℝ} (hd : 0 < d) (hdδ : d ≤ δ) (hs : 0 < s) :
    splineDualBound δ s ≤ inverseSplineBound d/8 := by
  have hδ := hd.trans_le hdδ
  have he : splineDualBound δ s=inverseSplineBound δ/(s+8) := by
    unfold splineDualBound inverseSplineBound
    ring
  rw [he]
  calc
    _ ≤ inverseSplineBound δ/8 :=
      div_le_div_of_nonneg_left (inverseSplineBound_pos hδ).le (by norm_num) (by linarith only [hs])
    _ ≤ _ := div_le_div_of_nonneg_right (inverseSplineBound_antitone hd hdδ) (by norm_num)

lemma splineBlaschke_coefficient_bound_antitone {d δ : ℝ} (hd : 0 < d) (hdδ : d ≤ δ) :
    (1+splineRatio δ)^8*(1/(1-splineRatio δ)^8) ≤
      (1+splineRatio d)^8*(1/(1-splineRatio d)^8) := by
  have hr : splineRatio δ ≤ splineRatio d := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hdδ]
  have hden : 0 < 1-splineRatio d := sub_pos.mpr (splineRatio_lt_one hd)
  have hpow := pow_le_pow_left₀ hden.le (sub_le_sub_left hr 1) 8
  have hi : 1/(1-splineRatio δ)^8 ≤ 1/(1-splineRatio d)^8 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hden 8) hpow
  exact mul_le_mul
    (pow_le_pow_left₀ (add_nonneg zero_le_one (splineRatio_pos δ).le) (add_le_add le_rfl hr) 8) hi (by positivity) (by positivity)

#print axioms splineNumeratorBound_le_envelope
#print axioms splineDualBound_le_strip
#print axioms splineBlaschke_coefficient_bound_antitone
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
