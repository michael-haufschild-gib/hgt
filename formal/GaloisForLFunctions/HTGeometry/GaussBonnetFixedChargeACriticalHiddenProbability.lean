import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHiddenProfile

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A symbolic scale that makes the signed hidden mode a strictly positive perturbation. -/
def egbFixedChargeACriticalHiddenScale (n : ℕ) : ℝ :=
  (2 * (1 + ∑ i, |egbFixedChargeACriticalHiddenProfile n i|))⁻¹

/-- The hidden mode receives a strictly positive amplitude. -/
theorem egbFixedChargeACriticalHiddenScale_pos (n : ℕ) :
    0 < egbFixedChargeACriticalHiddenScale n := by
  unfold egbFixedChargeACriticalHiddenScale
  have h : 0 ≤ ∑ i, |egbFixedChargeACriticalHiddenProfile n i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  positivity

/-- Every coordinate perturbation is strictly smaller than one half. -/
theorem egbFixedChargeACriticalHiddenScale_coordinate_bound (n : ℕ)
    (i : Fin (2 ^ (n + 3))) :
    |egbFixedChargeACriticalHiddenScale n * egbFixedChargeACriticalHiddenProfile n i| < 1 / 2 := by
  have hc := egbFixedChargeACriticalHiddenScale_pos n
  have hs : 0 ≤ ∑ j, |egbFixedChargeACriticalHiddenProfile n j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hi := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
      abs_nonneg (egbFixedChargeACriticalHiddenProfile n j)) (Finset.mem_univ i)
  have he : egbFixedChargeACriticalHiddenScale n *
      (2 * (1 + ∑ j, |egbFixedChargeACriticalHiddenProfile n j|)) = 1 := by
    unfold egbFixedChargeACriticalHiddenScale
    field_simp
  rw [abs_mul, abs_of_pos hc]
  nlinarith [mul_le_mul_of_nonneg_left hi hc.le]

/-- A full-support probability law carrying a nonzero hidden Fourier perturbation. -/
def egbFixedChargeACriticalHiddenProbability (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (1 + egbFixedChargeACriticalHiddenScale n * egbFixedChargeACriticalHiddenProfile n i) /
    (2 : ℝ) ^ (n + 3)

/-- Every probability lies strictly between one half and three halves of the uniform mass. -/
theorem egbFixedChargeACriticalHiddenProbability_envelope (n : ℕ)
    (i : Fin (2 ^ (n + 3))) :
    (1 / 2 : ℝ) / (2 : ℝ) ^ (n + 3) < egbFixedChargeACriticalHiddenProbability n i ∧
      egbFixedChargeACriticalHiddenProbability n i < (3 / 2 : ℝ) / (2 : ℝ) ^ (n + 3) := by
  have h := egbFixedChargeACriticalHiddenScale_coordinate_bound n i
  have hl := neg_abs_le (egbFixedChargeACriticalHiddenScale n * egbFixedChargeACriticalHiddenProfile n i)
  have hu := le_abs_self (egbFixedChargeACriticalHiddenScale n * egbFixedChargeACriticalHiddenProfile n i)
  have hn : 0 < (2 : ℝ) ^ (n + 3) := pow_pos (by norm_num) _
  unfold egbFixedChargeACriticalHiddenProbability
  constructor <;> apply div_lt_div_of_pos_right _ hn <;> linarith

/-- All coordinates are positive, with no positivity assumption supplied by a caller. -/
theorem egbFixedChargeACriticalHiddenProbability_pos (n : ℕ)
    (i : Fin (2 ^ (n + 3))) : 0 < egbFixedChargeACriticalHiddenProbability n i :=
  lt_trans (by positivity) (egbFixedChargeACriticalHiddenProbability_envelope n i).1

/-- The hidden probability law has total mass exactly one. -/
theorem egbFixedChargeACriticalHiddenProbability_mass (n : ℕ) :
    ∑ i, egbFixedChargeACriticalHiddenProbability n i = 1 := by
  unfold egbFixedChargeACriticalHiddenProbability
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    egbFixedChargeACriticalHiddenProfile_mass_zero]
  simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (pow_ne_zero _ (by norm_num))

/-- A strict excess at the first coordinate certifies nonuniformity. -/
theorem egbFixedChargeACriticalHiddenProbability_first_gt_uniform (n : ℕ) :
    ((2 : ℝ) ^ (n + 3))⁻¹ < egbFixedChargeACriticalHiddenProbability n 0 := by
  have hp := mul_pos (egbFixedChargeACriticalHiddenScale_pos n)
    (egbFixedChargeACriticalHiddenProfile_first_pos n)
  have hn : 0 < (2 : ℝ) ^ (n + 3) := pow_pos (by norm_num) _
  rw [← one_div]
  change 1 / (2 : ℝ) ^ (n + 3) <
    (1 + egbFixedChargeACriticalHiddenScale n * egbFixedChargeACriticalHiddenProfile n 0) /
      (2 : ℝ) ^ (n + 3)
  exact div_lt_div_of_pos_right (by linarith) hn

end
end GaloisForLFunctions.HTGeometry
