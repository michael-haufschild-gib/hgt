import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CrossTowerCollarAndFiniteEulerLatticePositivity

/-!
# The center-density kernel in pole gauge

Dividing the exact archimedean collar by the two pole weights gives the sum of
an inverse-difference kernel and an inverse-sum kernel. This identity retains
both sides of every logarithmic row and its zero diagonal.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticCastelnuovoSeveri

private theorem collarWeight_div_sqrt_mul_of_lt {n j : ℕ}
    (hn : 1 ≤ n) (hnj : n < j) :
    collarWeight n j / (Real.sqrt n * Real.sqrt j) =
      (1 / 2 : ℝ) * (1 / ((j : ℝ) - n) + 1 / ((n : ℝ) + j)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnjR : (n : ℝ) < j := by exact_mod_cast hnj
  have hj0 : (0 : ℝ) < j := hn0.trans hnjR
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
  have hdiff : (j : ℝ) - n ≠ 0 := (sub_pos.mpr hnjR).ne'
  have hsum : (n : ℝ) + j ≠ 0 := (add_pos hn0 hj0).ne'
  have hsq : (j : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    nlinarith only [hn0, hnjR]
  rw [collarWeight_eq_of_lt hn hnj, Real.sqrt_mul hn0.le]
  field_simp [hsn, hsj, hdiff, hsum, hsq]
  ring

/-- The literal collar in pole gauge is an exact symmetric harmonic kernel. -/
theorem collarWeight_div_sqrt_mul {n j : ℕ}
    (hn : 1 ≤ n) (hj : 1 ≤ j) (hnj : n ≠ j) :
    collarWeight n j / (Real.sqrt n * Real.sqrt j) =
      (1 / 2 : ℝ) * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) := by
  rcases lt_or_gt_of_ne hnj with hlt | hgt
  · rw [collarWeight_div_sqrt_mul_of_lt hn hlt,
      abs_of_neg (sub_neg.mpr (show (n : ℝ) < j by exact_mod_cast hlt)), neg_sub]
  · rw [collarWeight_comm, mul_comm (Real.sqrt n),
      collarWeight_div_sqrt_mul_of_lt hj hgt,
      abs_of_pos (sub_pos.mpr (show (j : ℝ) < n by exact_mod_cast hgt)),
      add_comm (j : ℝ)]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

