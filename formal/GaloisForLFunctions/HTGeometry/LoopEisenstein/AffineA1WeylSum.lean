import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1XiEstimates
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Weights
import GaloisForLFunctions.HTGeometry.ExponentialLatticeWeight

/-!
# Absolute convergence of the affine A₁ Weyl sum

Garland's ξ coefficients have exponential growth in translation length. The
degree rotation contributes a strictly negative quadratic exponent. Completing
the square gives a geometric majorant for both infinite dihedral families.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

noncomputable section

/-- A term of Garland's affine Weyl expansion in the full Godement chamber. -/
def weylTerm (p : ℂ × ℂ) (t z r : ℝ) (w : Weyl) : ℂ :=
  xiCoefficient (godementParameter p) w *
    Complex.exp (weylExponent (godementParameter p) t z r w)

theorem weylTerm_ne_zero (p : ℂ × ℂ) (t z r : ℝ) (w : Weyl) :
    weylTerm p t z r w ≠ 0 :=
  mul_ne_zero (xiCoefficient_ne_zero p w) (Complex.exp_ne_zero _)

private theorem summable_quadratic_abs {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    Summable (fun m : ℤ => Real.exp (c + b * |(m : ℝ)| - a * (m : ℝ) ^ 2)) := by
  have hgeom : Summable (fun m : ℤ => Real.exp (-|(m : ℝ)|)) := by
    simpa only [neg_one_mul] using
      GaloisForLFunctions.HTGeometry.summable_exp_neg_abs_int (c := 1) zero_lt_one
  have hmajor := hgeom.mul_left (Real.exp (c + (b + 1) ^ 2 / (4 * a)))
  apply hmajor.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro m
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := sq_nonneg (2 * a * |(m : ℝ)| - (b + 1))
  simp only [sub_sq, mul_pow, sq_abs] at hsq
  have hcomplete : (b + 1) * |(m : ℝ)| - a * (m : ℝ) ^ 2 ≤
      (b + 1) ^ 2 / (4 * a) := by
    apply (le_div_iff₀ (show 0 < 4 * a by positivity)).mpr
    nlinarith only [hsq]
  linarith only [hcomplete]

private theorem translation_coefficient_bound (p : ℂ × ℂ) (m : ℤ) :
    ‖xiCoefficient (godementParameter p) (.r m)‖ ≤
      Real.exp ((2 * |(m : ℝ)| + 1) * coefficientRate p) := by
  have h := xiCoefficient_translation_norm_le p m
  have he : ((2 * m).natAbs : ℝ) = 2 * |(m : ℝ)| := by
    simp [Nat.cast_natAbs, Int.cast_abs, abs_mul]
  rw [he] at h
  apply h.trans (Real.exp_le_exp.mpr ?_)
  nlinarith only [coefficientRate_pos p]

private theorem reflection_coefficient_bound (p : ℂ × ℂ) (m : ℤ) :
    ‖xiCoefficient (godementParameter p) (.sr m)‖ ≤
      Real.exp ((2 * |(m : ℝ)| + 1) * coefficientRate p) := by
  have h := xiCoefficient_reflection_norm_le p m
  have he : ((2 * m + 1).natAbs : ℝ) = |2 * (m : ℝ) + 1| := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [he] at h
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hlength : |2 * (m : ℝ) + 1| ≤ 2 * |(m : ℝ)| + 1 := by
    apply abs_le.mpr
    constructor
    · linarith only [neg_abs_le (m : ℝ)]
    · linarith only [le_abs_self (m : ℝ)]
  exact mul_le_mul_of_nonneg_right hlength (coefficientRate_pos p).le

/-- A Gaussian majorant for the complete translation summand, including its ξ denominator. -/
theorem norm_weylTerm_translation_le (p : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    ‖weylTerm p t z r (.r m)‖ ≤
      Real.exp (translationConstant p t z + coefficientRate p +
        (2 * coefficientRate p + |translationLinear p t r|) * |(m : ℝ)| -
          gaussianRate p r * (m : ℝ) ^ 2) := by
  rw [weylTerm, norm_mul, norm_exp_weylExponent_translation]
  calc
    _ ≤ Real.exp ((2 * |(m : ℝ)| + 1) * coefficientRate p) *
        Real.exp (translationConstant p t z + translationLinear p t r * m -
          gaussianRate p r * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (translation_coefficient_bound p m) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlinear : translationLinear p t r * (m : ℝ) ≤
          |translationLinear p t r| * |(m : ℝ)| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith only [hlinear]

/-- The second dihedral family admits the same form of Gaussian majorant. -/
theorem norm_weylTerm_reflection_le (p : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    ‖weylTerm p t z r (.sr m)‖ ≤
      Real.exp (reflectionConstant p t z + coefficientRate p +
        (2 * coefficientRate p + |reflectionLinear p t r|) * |(m : ℝ)| -
          gaussianRate p r * (m : ℝ) ^ 2) := by
  rw [weylTerm, norm_mul, norm_exp_weylExponent_reflection]
  calc
    _ ≤ Real.exp ((2 * |(m : ℝ)| + 1) * coefficientRate p) *
        Real.exp (reflectionConstant p t z + reflectionLinear p t r * m -
          gaussianRate p r * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (reflection_coefficient_bound p m) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlinear : reflectionLinear p t r * (m : ℝ) ≤
          |reflectionLinear p t r| * |(m : ℝ)| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith only [hlinear]

theorem summable_norm_translation (p : ℂ × ℂ) (t z r : ℝ) :
    Summable (fun m : ℤ => ‖weylTerm p t z r (.r m)‖) := by
  exact (summable_quadratic_abs (gaussianRate_pos p r)
    (2 * coefficientRate p + |translationLinear p t r|)
    (translationConstant p t z + coefficientRate p)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_weylTerm_translation_le p t z r)

theorem summable_norm_reflection (p : ℂ × ℂ) (t z r : ℝ) :
    Summable (fun m : ℤ => ‖weylTerm p t z r (.sr m)‖) := by
  exact (summable_quadratic_abs (gaussianRate_pos p r)
    (2 * coefficientRate p + |reflectionLinear p t r|)
    (reflectionConstant p t z + coefficientRate p)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_weylTerm_reflection_le p t z r)

/-- Absolute convergence over the entire infinite affine Weyl group. -/
theorem summable_norm_weylTerm (p : ℂ × ℂ) (t z r : ℝ) :
    Summable (fun w : Weyl => ‖weylTerm p t z r w‖) := by
  apply (DihedralGroup.equivSum.symm.summable_iff).mp
  exact Summable.sum _ (summable_norm_translation p t z r) (summable_norm_reflection p t z r)

theorem summable_weylTerm (p : ℂ × ℂ) (t z r : ℝ) : Summable (weylTerm p t z r) :=
  (summable_norm_weylTerm p t z r).of_norm

/-- The convergent affine Weyl expansion with its literal completed-zeta denominators. -/
def weylSum (p : ℂ × ℂ) (t z r : ℝ) : ℂ := ∑' w : Weyl, weylTerm p t z r w

theorem hasSum_weylTerm (p : ℂ × ℂ) (t z r : ℝ) :
    HasSum (weylTerm p t z r) (weylSum p t z r) :=
  (summable_weylTerm p t z r).hasSum

/-- The Weyl expansion is exactly its translation series plus its reflection series. -/
theorem weylSum_eq_two_series (p : ℂ × ℂ) (t z r : ℝ) :
    weylSum p t z r = (∑' m : ℤ, weylTerm p t z r (.r m)) +
      ∑' m : ℤ, weylTerm p t z r (.sr m) := by
  rw [weylSum, ← DihedralGroup.equivSum.symm.tsum_eq (weylTerm p t z r)]
  exact Summable.tsum_sum (summable_norm_translation p t z r).of_norm
    (summable_norm_reflection p t z r).of_norm

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
