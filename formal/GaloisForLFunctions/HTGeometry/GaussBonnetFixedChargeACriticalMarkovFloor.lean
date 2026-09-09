import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovSharpMixing

/-!
Positive transition floors for the Markov dynamics derived from the critical
Gibbs kernel of arXiv:2609.00025. The first harmonic controls the second strongly
enough to make the exact lower envelope increase after every step.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Candidate lower envelope after m+1 transitions, proved below. -/
def egbFixedChargeACriticalMarkovFloor (m : ℕ) : ℝ :=
  1 - 2 * (2 / 3 : ℝ) ^ (m + 1) + 2 * (1 / 6 : ℝ) ^ (m + 1)

/-- The first harmonic dominates four copies of the second at every positive step count. -/
theorem egbFixedChargeACriticalMarkov_harmonic_domination (m : ℕ) :
    4 * (1 / 6 : ℝ) ^ (m + 1) ≤ (2 / 3 : ℝ) ^ (m + 1) := by
  have h : (1 / 6 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ m :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) m
  rw [pow_succ, pow_succ]
  nlinarith

/-- The exact lower envelope strictly increases at every transition. -/
theorem egbFixedChargeACriticalMarkovFloor_strictMono :
    StrictMono egbFixedChargeACriticalMarkovFloor := by
  apply strictMono_nat_of_lt_succ
  intro m
  have h := egbFixedChargeACriticalMarkov_harmonic_domination m
  have hp : 0 < (1 / 6 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
  unfold egbFixedChargeACriticalMarkovFloor
  rw [pow_succ (2 / 3 : ℝ) (m + 1), pow_succ (1 / 6 : ℝ) (m + 1)]
  nlinarith

/-- After two transitions the scaled floor is at least one sixth, for all later steps too. -/
theorem egbFixedChargeACriticalMarkovFloor_two_step (m : ℕ) :
    (1 / 6 : ℝ) ≤ egbFixedChargeACriticalMarkovFloor (m + 1) := by
  have h := egbFixedChargeACriticalMarkovFloor_strictMono.monotone (show 1 ≤ m + 1 by omega)
  have he : egbFixedChargeACriticalMarkovFloor 1 = (1 / 6 : ℝ) := by
    norm_num [egbFixedChargeACriticalMarkovFloor]
  rwa [he] at h

/-- Every transition entry lies above the harmonic lower envelope. -/
theorem egbFixedChargeACriticalMarkovMatrix_lower_floor
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalMarkovFloor m ≤
      (2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re := by
  rw [egbFixedChargeACriticalMarkovMatrix_pow_real]
  let x := 2 * (egbFixedChargeAFourierGrid (n + 3) i - egbFixedChargeAFourierGrid (n + 3) j)
  have hc : -1 ≤ Real.cos x := Real.neg_one_le_cos x
  have h4 : Real.cos (4 * (egbFixedChargeAFourierGrid (n + 3) i -
      egbFixedChargeAFourierGrid (n + 3) j)) = 2 * Real.cos x ^ 2 - 1 := by
    rw [show 4 * (egbFixedChargeAFourierGrid (n + 3) i - egbFixedChargeAFourierGrid (n + 3) j) =
      2 * x by dsimp [x]; ring, Real.cos_two_mul]
  rw [h4]
  have hd := egbFixedChargeACriticalMarkov_harmonic_domination m
  have hb : 0 ≤ (1 / 6 : ℝ) ^ (m + 1) := by positivity
  have hi : 0 ≤ (2 / 3 : ℝ) ^ (m + 1) +
      2 * (1 / 6 : ℝ) ^ (m + 1) * (Real.cos x - 1) := by nlinarith
  have hp := mul_nonneg (by linarith : 0 ≤ 2 * (Real.cos x + 1)) hi
  change 1 - 2 * (2 / 3 : ℝ) ^ (m + 1) + 2 * (1 / 6 : ℝ) ^ (m + 1) ≤
    1 + 2 * (2 / 3 : ℝ) ^ (m + 1) * Real.cos x +
      2 * (1 / 6 : ℝ) ^ (m + 1) * (2 * Real.cos x ^ 2 - 1)
  nlinarith

/-- Every pair of states has a positive transition floor from the second step onward. -/
theorem egbFixedChargeACriticalMarkovMatrix_two_step_minorization
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    1 / (6 * (2 : ℝ) ^ (n + 3)) ≤
      ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 2)) i j).re := by
  have h := (egbFixedChargeACriticalMarkovFloor_two_step m).trans
    (egbFixedChargeACriticalMarkovMatrix_lower_floor n (m + 1) i j)
  have hn : 0 < (2 : ℝ) ^ (n + 3) := pow_pos (by norm_num) _
  have hd := div_le_div_of_nonneg_right h hn.le
  have hc : (1 / 6 : ℝ) / (2 : ℝ) ^ (n + 3) = 1 / (6 * (2 : ℝ) ^ (n + 3)) := by ring
  rw [hc] at hd
  simpa only [mul_div_cancel_left₀ _ (ne_of_gt hn)] using hd

end

end GaloisForLFunctions.HTGeometry
