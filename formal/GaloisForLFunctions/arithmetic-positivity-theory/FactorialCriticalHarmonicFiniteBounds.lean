import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalHarmonicOscillationBounds

/-!
# Finite critical harmonic phase bounds

Exact trigonometric phases sharpen the two-step integration-by-parts estimate
at the harmonics needed in the complete signed prime budget.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false


private theorem sqrt_three_bounds : (1 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 7/4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

private theorem defect_le_of_phase (m : ℕ) (s c B : ℝ)
    (hs : Real.sin (Real.pi * ((m+1 : ℕ) : ℝ) / 6) ≤ s)
    (hc : c ≤ Real.cos (Real.pi * ((m+1 : ℕ) : ℝ) / 6))
    (hcost : (Real.pi * ((m+1 : ℕ) : ℝ) / 6) * s + 2 * (1-c) ≤
      (B-1) * (Real.pi * ((m+1 : ℕ) : ℝ) / 6)^2) :
    factorialCriticalHarmonicDefect (m+1) ≤ B := by
  let θ := Real.pi * ((m+1 : ℕ) : ℝ) / 6
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have h := factorialCriticalHarmonicDefect_phase_upper_scaled m
  have hsin := mul_le_mul_of_nonneg_left hs hθ.le
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hθ)).mp
  change factorialCriticalHarmonicDefect (m+1) * θ^2 ≤
    θ^2 + θ * Real.sin θ + 2 * (1 - Real.cos θ) at h
  change c ≤ Real.cos θ at hc
  change θ * Real.sin θ ≤ θ * s at hsin
  change θ * s + 2 * (1-c) ≤ (B-1) * θ^2 at hcost
  nlinarith only [h, hsin, hc, hcost]

theorem factorialCriticalHarmonicDefect_seven_le :
    factorialCriticalHarmonicDefect 7 ≤ 7/6 := by
  apply defect_le_of_phase 6 (-1/2) (-7/8) (7/6)
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 7 / 6 = Real.pi / 6 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_six]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 7 / 6 = Real.pi / 6 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_six]
    linarith [sqrt_three_bounds.2]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

theorem factorialCriticalHarmonicDefect_nine_le :
    factorialCriticalHarmonicDefect 9 ≤ 1 := by
  apply defect_le_of_phase 8 (-1) 0 1
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 9 / 6 = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 9 / 6 = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two]
    norm_num
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three]

theorem factorialCriticalHarmonicDefect_ten_le :
    factorialCriticalHarmonicDefect 10 ≤ 1 := by
  apply defect_le_of_phase 9 (-1/2) (1/2) 1
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 10 / 6 = -(Real.pi / 3) + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_neg, Real.sin_pi_div_three]
    linarith [sqrt_three_bounds.1]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 10 / 6 = -(Real.pi / 3) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_three]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three]

theorem factorialCriticalHarmonicDefect_eleven_le :
    factorialCriticalHarmonicDefect 11 ≤ 1 := by
  apply defect_le_of_phase 10 (-1/2) 0 1
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 11 / 6 = -(Real.pi / 6) + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_neg, Real.sin_pi_div_six]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 11 / 6 = -(Real.pi / 6) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_six]
    positivity
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three]

theorem factorialCriticalHarmonicDefect_thirteen_le :
    factorialCriticalHarmonicDefect 13 ≤ 7/6 := by
  apply defect_le_of_phase 12 (1/2) 0 (7/6)
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 13 / 6 = Real.pi / 6 + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_pi_div_six]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 13 / 6 = Real.pi / 6 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_div_six]
    positivity
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

theorem factorialCriticalHarmonicDefect_fourteen_le :
    factorialCriticalHarmonicDefect 14 ≤ 7/6 := by
  apply defect_le_of_phase 13 (7/8) (1/2) (7/6)
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 14 / 6 = Real.pi / 3 + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_pi_div_three]
    linarith [sqrt_three_bounds.2]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 14 / 6 = Real.pi / 3 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_div_three]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

theorem factorialCriticalHarmonicDefect_fifteen_le :
    factorialCriticalHarmonicDefect 15 ≤ 7/6 := by
  apply defect_le_of_phase 14 1 0 (7/6)
  · exact Real.sin_le_one _
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 15 / 6 = Real.pi / 2 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_div_two]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_d2, sq_nonneg (Real.pi-157/50)]

theorem factorialCriticalHarmonicDefect_seventeen_le :
    factorialCriticalHarmonicDefect 17 ≤ 7/6 := by
  apply defect_le_of_phase 16 (1/2) (-7/8) (7/6)
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 17 / 6 = (Real.pi - Real.pi / 6) + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_pi_sub, Real.sin_pi_div_six]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 17 / 6 = (Real.pi - Real.pi / 6) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_sub, Real.cos_pi_div_six]
    linarith [sqrt_three_bounds.2]
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

theorem factorialCriticalHarmonicDefect_eighteen_le :
    factorialCriticalHarmonicDefect 18 ≤ 7/6 := by
  apply defect_le_of_phase 17 0 (-1) (7/6)
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    rw [show Real.pi * 18 / 6 = Real.pi + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_pi]
  · exact Real.neg_one_le_cos _
  · norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

end GaloisForLFunctions.ArithmeticPositivityTheory
