import GaloisForLFunctions.RHTower.SoninSemilocalPoissonFrequencyCollapse

/-!
# Exact archimedean Jacobi normalization recurrences

This module verifies the two factorial identities that drive the induction in the exact
archimedean transform law.  They identify the paper's recurrence coefficient
`a_n = sqrt((n + 1/2)(n + 1))` with both adjacent normalization ratios.
-/

noncomputable section

namespace RHTower

/-- The archimedean Jacobi recurrence coefficient `a_n`. -/
def semilocalArchimedeanJacobiCoefficient (n : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ) + 1 / 2) * ((n : ℝ) + 1))

theorem semilocalArchimedeanJacobiCoefficient_pos (n : ℕ) :
    0 < semilocalArchimedeanJacobiCoefficient n := by
  unfold semilocalArchimedeanJacobiCoefficient
  positivity

theorem semilocalArchimedeanJacobiCoefficient_sq (n : ℕ) :
    semilocalArchimedeanJacobiCoefficient n ^ (2 : ℕ) =
      ((n : ℝ) + 1 / 2) * ((n : ℝ) + 1) := by
  unfold semilocalArchimedeanJacobiCoefficient
  rw [Real.sq_sqrt]
  positivity

/-- Square of the closed factorial normalization `c_n`. -/
theorem semilocalArchimedeanJacobiNormalization_sq (n : ℕ) :
    semilocalArchimedeanJacobiNormalization n ^ (2 : ℕ) =
      (Nat.factorial (2 * n) : ℝ) /
        (((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) ^ (2 : ℕ)) := by
  unfold semilocalArchimedeanJacobiNormalization
  rw [div_pow, Real.sq_sqrt]
  positivity

/-- The forward induction identity `c_(n+1) a_n = c_n (n+1/2)`. -/
theorem semilocalArchimedeanJacobiNormalization_succ_mul_coefficient (n : ℕ) :
    semilocalArchimedeanJacobiNormalization (n + 1) *
        semilocalArchimedeanJacobiCoefficient n =
      semilocalArchimedeanJacobiNormalization n * ((n : ℝ) + 1 / 2) := by
  have hleft : 0 ≤ semilocalArchimedeanJacobiNormalization (n + 1) *
      semilocalArchimedeanJacobiCoefficient n :=
    mul_nonneg (semilocalArchimedeanJacobiNormalization_pos _).le
      (semilocalArchimedeanJacobiCoefficient_pos n).le
  have hright : 0 ≤ semilocalArchimedeanJacobiNormalization n * ((n : ℝ) + 1 / 2) := by
    exact mul_nonneg (semilocalArchimedeanJacobiNormalization_pos _).le (by positivity)
  suffices (semilocalArchimedeanJacobiNormalization (n + 1) *
        semilocalArchimedeanJacobiCoefficient n) ^ (2 : ℕ) =
      (semilocalArchimedeanJacobiNormalization n * ((n : ℝ) + 1 / 2)) ^ (2 : ℕ) by
    nlinarith
  rw [mul_pow, mul_pow,
    semilocalArchimedeanJacobiNormalization_sq,
    semilocalArchimedeanJacobiNormalization_sq,
    semilocalArchimedeanJacobiCoefficient_sq]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Nat.factorial_succ]
  rw [show 2 * n + 1 = 2 * n + 1 by rfl]
  rw [show n + 1 = n + 1 by rfl, Nat.factorial_succ]
  push_cast
  field_simp
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  ring

/-- The backward induction identity `(n+1)c_(n+1) = a_n c_n`. -/
theorem semilocalArchimedeanJacobi_succ_mul_normalization (n : ℕ) :
    ((n : ℝ) + 1) * semilocalArchimedeanJacobiNormalization (n + 1) =
      semilocalArchimedeanJacobiCoefficient n *
        semilocalArchimedeanJacobiNormalization n := by
  have hleft : 0 ≤ ((n : ℝ) + 1) *
      semilocalArchimedeanJacobiNormalization (n + 1) :=
    mul_nonneg (by positivity) (semilocalArchimedeanJacobiNormalization_pos _).le
  have hright : 0 ≤ semilocalArchimedeanJacobiCoefficient n *
      semilocalArchimedeanJacobiNormalization n :=
    mul_nonneg (semilocalArchimedeanJacobiCoefficient_pos n).le
      (semilocalArchimedeanJacobiNormalization_pos _).le
  suffices (((n : ℝ) + 1) *
        semilocalArchimedeanJacobiNormalization (n + 1)) ^ (2 : ℕ) =
      (semilocalArchimedeanJacobiCoefficient n *
        semilocalArchimedeanJacobiNormalization n) ^ (2 : ℕ) by
    nlinarith
  rw [mul_pow, mul_pow,
    semilocalArchimedeanJacobiNormalization_sq,
    semilocalArchimedeanJacobiNormalization_sq,
    semilocalArchimedeanJacobiCoefficient_sq]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Nat.factorial_succ]
  rw [show 2 * n + 1 = 2 * n + 1 by rfl]
  rw [show n + 1 = n + 1 by rfl, Nat.factorial_succ]
  push_cast
  field_simp
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  ring

end RHTower
