import GaloisForLFunctions.ConjugateDiagonalGeometry.StripSourceCutoff
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiExpRegulatorError

/-!
# Polynomial source and regulator scales

One integer majorizing the fixed bump derivative norms determines every
stage. Both the logarithmic regulator scale and the number of theta atoms
are polynomial in height; neither uses zeros or a potential-error test.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- Fixed integer control for the vertically stretched cutoff. -/
def stripSourceIntegerControl : ℕ := ⌈stripSourceCutoffControl⌉₊

lemma stripSourceCutoffControl_le_integer :
    stripSourceCutoffControl ≤ (stripSourceIntegerControl : ℝ) := Nat.le_ceil _

lemma one_le_stripSourceIntegerControl : (1 : ℝ) ≤ (stripSourceIntegerControl : ℝ) :=
  one_le_stripSourceCutoffControl.trans stripSourceCutoffControl_le_integer

/-- Polynomial logarithmic scale for the positive regulator. -/
def polynomialSourceLogScale (n : ℕ) : ℝ :=
  (stripSourceIntegerControl : ℝ) * ((n : ℝ) + 1) ^ 20

/-- Positive source regulator prescribed by height alone. -/
def polynomialSourceRegulator (n : ℕ) : ℝ := Real.exp (-polynomialSourceLogScale n)

lemma polynomialSourceRegulator_pos (n : ℕ) : 0 < polynomialSourceRegulator n := Real.exp_pos _

/-- A polynomial number of literal integer theta atoms. -/
def polynomialThetaIntegerCutoff (n : ℕ) : ℕ :=
  (stripSourceIntegerControl + 4) * (n + 1) ^ 20

lemma polynomialSourceLogScale_pos (n : ℕ) : 0 < polynomialSourceLogScale n := by
  have hC : 0 < (stripSourceIntegerControl : ℝ) :=
    lt_of_lt_of_le zero_lt_one one_le_stripSourceIntegerControl
  unfold polynomialSourceLogScale
  positivity

lemma stripSourceCutoffControl_le_polynomialSourceLogScale (n : ℕ) :
    stripSourceCutoffControl ≤ polynomialSourceLogScale n := by
  have hp : 1 ≤ ((n : ℝ) + 1) ^ 20 := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n))
  exact stripSourceCutoffControl_le_integer.trans
    (le_mul_of_one_le_right (Nat.cast_nonneg stripSourceIntegerControl) hp)

lemma polynomialSourceLogScale_ge_four {n : ℕ} (hn : 1 ≤ n) :
    4 ≤ polynomialSourceLogScale n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (show 2 ≤ (n : ℝ) + 1 by linarith only [hn']) 20
  have hC := le_mul_of_one_le_left (by positivity : 0 ≤ ((n : ℝ) + 1) ^ 20)
    one_le_stripSourceIntegerControl
  change ((n : ℝ) + 1) ^ 20 ≤ polynomialSourceLogScale n at hC
  norm_num only [show (2 : ℝ) ^ 20 = 1048576 by norm_num] at hp
  linarith only [hp, hC]

lemma polynomialThetaIntegerCutoff_ge_logScale_add_four (n : ℕ) :
    polynomialSourceLogScale n + 4 ≤ (polynomialThetaIntegerCutoff n : ℝ) := by
  have hp : 1 ≤ ((n : ℝ) + 1) ^ 20 := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n))
  simp only [polynomialSourceLogScale, polynomialThetaIntegerCutoff, Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
  nlinarith only [hp]

/-- The squared prefix length pays three copies of the regulator scale. -/
lemma polynomialThetaIntegerCutoff_sq_ge (n : ℕ) :
    3 * polynomialSourceLogScale n ≤ ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2 := by
  have hK := polynomialSourceLogScale_pos n
  have hN := polynomialThetaIntegerCutoff_ge_logScale_add_four n
  have hsq := sq_nonneg (polynomialSourceLogScale n)
  have hsqN := pow_le_pow_left₀
    (show 0 ≤ polynomialSourceLogScale n + 5 by linarith only [hK])
    (show polynomialSourceLogScale n + 5 ≤ ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) by
      push_cast
      linarith only [hN]) 2
  nlinarith only [hsqN, hsq, hK]

private lemma exp_neg_le_reciprocal {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  have h := Real.log_le_sub_one_of_pos (Real.exp_pos x)
  rw [Real.log_exp] at h
  have hex : x ≤ Real.exp x := by linarith only [h]
  rw [Real.exp_neg, ← one_div]
  exact div_le_div_of_nonneg_left zero_le_one hx hex

/-- Cutoff control cancels against the fixed integer in the logarithmic scale. -/
lemma stripSourceControl_div_polynomialScale_le (n : ℕ) :
    stripSourceCutoffControl / polynomialSourceLogScale n ≤ 1 / ((n : ℝ) + 1) ^ 20 := by
  apply (div_le_div_iff₀ (polynomialSourceLogScale_pos n) (by positivity)).2
  simpa only [one_mul, polynomialSourceLogScale] using
    mul_le_mul_of_nonneg_right stripSourceCutoffControl_le_integer
      (by positivity : 0 ≤ ((n : ℝ) + 1) ^ 20)

/-- The regularization's constant term is bounded by the inverse polynomial scale. -/
lemma stripSourceControl_exp_half_le (n : ℕ) :
    stripSourceCutoffControl * Real.exp (-polynomialSourceLogScale n / 2) ≤
      2 / ((n : ℝ) + 1) ^ 20 := by
  have he : Real.exp (-polynomialSourceLogScale n / 2) ≤ 2 / polynomialSourceLogScale n := by
    calc
      Real.exp (-polynomialSourceLogScale n / 2) =
          Real.exp (-(polynomialSourceLogScale n / 2)) := congrArg Real.exp (by ring)
      _ ≤ 1 / (polynomialSourceLogScale n / 2) :=
        exp_neg_le_reciprocal (half_pos (polynomialSourceLogScale_pos n))
      _ = 2 / polynomialSourceLogScale n := by
        field_simp [(polynomialSourceLogScale_pos n).ne']
  have hM : 0 ≤ stripSourceCutoffControl := le_trans zero_le_one one_le_stripSourceCutoffControl
  calc
    stripSourceCutoffControl * Real.exp (-polynomialSourceLogScale n / 2) ≤
        stripSourceCutoffControl * (2 / polynomialSourceLogScale n) :=
      mul_le_mul_of_nonneg_left he hM
    _ = 2 * (stripSourceCutoffControl / polynomialSourceLogScale n) := by ring
    _ ≤ 2 * (1 / ((n : ℝ) + 1) ^ 20) :=
      mul_le_mul_of_nonneg_left (stripSourceControl_div_polynomialScale_le n) (by norm_num)
    _ = _ := by ring

/-- The integer tail pays regulator sensitivity and the full cutoff control. -/
lemma stripSourceControl_finite_tail_le (n : ℕ) :
    stripSourceCutoffControl *
      Real.exp (polynomialSourceLogScale n - ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) ≤
      1 / ((n : ℝ) + 1) ^ 20 := by
  have hK := polynomialSourceLogScale_pos n
  have hx := Real.log_le_sub_one_of_pos (Real.exp_pos (polynomialSourceLogScale n))
  rw [Real.log_exp] at hx
  have hM : stripSourceCutoffControl ≤ Real.exp (polynomialSourceLogScale n) :=
    (stripSourceCutoffControl_le_polynomialSourceLogScale n).trans (by linarith only [hx])
  calc
    stripSourceCutoffControl *
        Real.exp (polynomialSourceLogScale n - ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) ≤
      Real.exp (polynomialSourceLogScale n) *
        Real.exp (polynomialSourceLogScale n - ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le
    _ = Real.exp (2 * polynomialSourceLogScale n - ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-polynomialSourceLogScale n) :=
      Real.exp_le_exp.mpr (by linarith only [polynomialThetaIntegerCutoff_sq_ge n])
    _ ≤ 1 / polynomialSourceLogScale n := exp_neg_le_reciprocal hK
    _ ≤ 1 / ((n : ℝ) + 1) ^ 20 := by
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      exact le_mul_of_one_le_left (by positivity) one_le_stripSourceIntegerControl

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.stripSourceControl_exp_half_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.stripSourceControl_finite_tail_le
