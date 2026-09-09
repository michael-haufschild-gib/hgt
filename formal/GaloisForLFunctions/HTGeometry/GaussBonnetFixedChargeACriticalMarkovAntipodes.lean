import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovFloor

/-!
Antipodal entries attain the critical Gibbs Markov transition floor exactly.
Together with the diagonal upper envelope this identifies both ends of the
entire transition range without evaluating any finite matrix numerically.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The grid point halfway around the period from zero. -/
def egbFixedChargeACriticalMarkovAntipode (n : ℕ) : Fin (2 ^ (n + 3)) :=
  ⟨2 ^ (n + 2), by
    have hp : 0 < (2 : ℕ) ^ (n + 2) := pow_pos (by omega) _
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ (2 : ℕ) (n + 2)]
    omega⟩

/-- The selected grid point has exactly angle π/2. -/
theorem egbFixedChargeACriticalMarkovAntipode_grid (n : ℕ) :
    egbFixedChargeAFourierGrid (n + 3) (egbFixedChargeACriticalMarkovAntipode n) = Real.pi / 2 := by
  simp only [egbFixedChargeAFourierGrid, egbFixedChargeACriticalMarkovAntipode,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [show n + 3 = (n + 2) + 1 by omega, pow_succ (2 : ℝ) (n + 2)]
  field_simp

/-- Antipodal transitions attain the full lower envelope after every positive number of steps. -/
theorem egbFixedChargeACriticalMarkovMatrix_antipodal_entry
    (n m : ℕ) :
    (2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1))
      0 (egbFixedChargeACriticalMarkovAntipode n)).re = egbFixedChargeACriticalMarkovFloor m := by
  rw [egbFixedChargeACriticalMarkovMatrix_pow_real, egbFixedChargeACriticalMarkovAntipode_grid]
  have hz : egbFixedChargeAFourierGrid (n + 3) 0 = 0 := by simp [egbFixedChargeAFourierGrid]
  rw [hz, show 2 * (0 - Real.pi / 2) = -Real.pi by ring,
    show 4 * (0 - Real.pi / 2) = 2 * (-Real.pi) by ring,
    Real.cos_two_mul, Real.cos_neg, Real.cos_pi]
  unfold egbFixedChargeACriticalMarkovFloor
  ring

/-- Exact classification of every uniform lower bound on the transition entries. -/
theorem egbFixedChargeACriticalMarkovMatrix_sharp_lower_bound
    (n m : ℕ) (B : ℝ) :
    (∀ i j : Fin (2 ^ (n + 3)), B ≤
      (2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re) ↔
        B ≤ egbFixedChargeACriticalMarkovFloor m := by
  constructor
  · intro h
    have ha := h 0 (egbFixedChargeACriticalMarkovAntipode n)
    rwa [egbFixedChargeACriticalMarkovMatrix_antipodal_entry] at ha
  · intro h i j
    exact h.trans (egbFixedChargeACriticalMarkovMatrix_lower_floor n m i j)

/-- Every transition between every pair of states is strictly positive from the second step onward. -/
theorem egbFixedChargeACriticalMarkovMatrix_two_step_pos
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    0 < ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 2)) i j).re := by
  have h : 0 < 1 / (6 * (2 : ℝ) ^ (n + 3)) := by positivity
  exact h.trans_le (egbFixedChargeACriticalMarkovMatrix_two_step_minorization n m i j)

end

end GaloisForLFunctions.HTGeometry
