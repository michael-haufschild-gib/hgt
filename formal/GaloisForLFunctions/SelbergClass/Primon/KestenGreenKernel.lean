import GaloisForLFunctions.SelbergClass.Primon.KestenGreenBoundaryFactorization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The exact half-line prime Green kernel

In even-character coordinates the Green kernel is
`q/(1-q²) (q^|n-m| - q^(n+m+1))`. It is strictly positive, obeys the
one-dimensional Markov factorization, and has an explicit geometric
boundary defect. Diagonal entries increase to the bulk covariance.
-/

open _root_.RHTower Filter Topology
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- A matrix entry of the actual square-coordinate Green operator. -/
def kestenGreenEntry (p : Nat.Primes) (n m : ℕ) : ℝ :=
  inner ℝ (kestenCharacterState n) (kestenGreenOperator p (kestenCharacterState m))

private theorem inner_character_prime (p : Nat.Primes) (n : ℕ) :
    inner ℝ (kestenCharacterState n) (kestenPrimeState p) = primeReciprocal p ^ n := by
  rw [inner_kestenCharacterState]
  simp [kestenPrimeState, primeHardyKernel, hardyKernel_apply]

private theorem gap_pos (p : Nat.Primes) : 0 < 1 - primeReciprocal p ^ 2 :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))

/-- The Green kernel is stationary geometric covariance minus its reflected boundary term. -/
theorem kestenGreenEntry_eq (p : Nat.Primes) (n m : ℕ) :
    kestenGreenEntry p n m = primeReciprocal p / (1 - primeReciprocal p ^ 2) *
      (primeReciprocal p ^ Nat.dist n m - primeReciprocal p ^ (n + m + 1)) := by
  rw [kestenGreenEntry, kestenGreenOperator_boundary_correction, inner_sub_right,
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterState n)
      (kestenGeometricCovariance p (kestenCharacterState m)) (primeReciprocal p),
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterState n) (kestenPrimeState p)
      (primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) *
        inner ℝ (kestenPrimeState p) (kestenCharacterState m)),
    inner_kestenGeometricCovariance_characters,
    real_inner_comm (kestenCharacterState m) (kestenPrimeState p),
    inner_character_prime, inner_character_prime]
  simp only [pow_add, pow_one, div_eq_mul_inv]
  ring

/-- Actual Hardy coordinates of a Green column are given by the closed kernel. -/
theorem hardyCoordinate_kestenGreenOperator_character (p : Nat.Primes) (n m : ℕ) :
    hardyLikelihoodUnitary.symm (kestenGreenOperator p (kestenCharacterState m)) n =
      primeReciprocal p / (1 - primeReciprocal p ^ 2) *
        (primeReciprocal p ^ Nat.dist n m - primeReciprocal p ^ (n + m + 1)) := by
  rw [← inner_kestenCharacterState]
  exact kestenGreenEntry_eq p n m

theorem kestenGreenEntry_symm (p : Nat.Primes) (n m : ℕ) :
    kestenGreenEntry p n m = kestenGreenEntry p m n := by
  rw [kestenGreenEntry_eq, kestenGreenEntry_eq, Nat.dist_comm n m, Nat.add_comm n m]

/-- Moving away from a fixed source multiplies its diagonal covariance by a geometric lag. -/
theorem kestenGreenEntry_add (p : Nat.Primes) (n k : ℕ) :
    kestenGreenEntry p n (n + k) =
      primeReciprocal p ^ (k + 1) / (1 - primeReciprocal p ^ 2) *
        (1 - primeReciprocal p ^ (2 * n + 1)) := by
  rw [kestenGreenEntry_eq, Nat.dist_eq_sub_of_le (Nat.le_add_right n k), Nat.add_sub_cancel_left]
  rw [show n + (n + k) + 1 = k + (2 * n + 1) by omega]
  simp only [pow_add, pow_one, div_eq_mul_inv]
  ring

/-- The diagonal records the exact distance from the half-line boundary. -/
theorem kestenGreenEntry_diagonal (p : Nat.Primes) (n : ℕ) :
    kestenGreenEntry p n n = primeReciprocal p / (1 - primeReciprocal p ^ 2) *
      (1 - primeReciprocal p ^ (2 * n + 1)) := by
  simpa only [Nat.add_zero, zero_add, pow_one] using kestenGreenEntry_add p n 0

/-- Every matrix entry is strictly positive. -/
theorem kestenGreenEntry_pos (p : Nat.Primes) (n m : ℕ) : 0 < kestenGreenEntry p n m := by
  have h (a k : ℕ) : 0 < kestenGreenEntry p a (a + k) := by
    rw [kestenGreenEntry_add]
    exact mul_pos (div_pos (pow_pos (primeReciprocal_pos p) _) (gap_pos p))
      (sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by omega)))
  rcases le_total n m with hnm | hmn
  · simpa only [Nat.add_sub_of_le hnm] using h n (m - n)
  · rw [kestenGreenEntry_symm]
    simpa only [Nat.add_sub_of_le hmn] using h m (n - m)

/-- Three ordered depths satisfy the exact Markov covariance identity. -/
theorem kestenGreenEntry_markov (p : Nat.Primes) (n i j : ℕ) :
    kestenGreenEntry p n (n + i + j) * kestenGreenEntry p (n + i) (n + i) =
      kestenGreenEntry p n (n + i) * kestenGreenEntry p (n + i) (n + i + j) := by
  have h := kestenGreenEntry_add p n (i + j)
  rw [← Nat.add_assoc] at h
  rw [h, kestenGreenEntry_diagonal, kestenGreenEntry_add p n i,
    kestenGreenEntry_add p (n + i) j]
  simp only [pow_add, pow_one, div_eq_mul_inv]
  ring

/-- The deficit from bulk diagonal covariance decays by an exact squared geometric factor. -/
theorem kestenGreenEntry_diagonal_defect (p : Nat.Primes) (n : ℕ) :
    primeReciprocal p / (1 - primeReciprocal p ^ 2) - kestenGreenEntry p n n =
      primeReciprocal p ^ (2 * (n + 1)) / (1 - primeReciprocal p ^ 2) := by
  rw [kestenGreenEntry_diagonal, show 2 * (n + 1) = (2 * n + 1) + 1 by omega, pow_succ]
  ring

/-- Each new diagonal entry gains exactly `q^(2n+2)`. -/
theorem kestenGreenEntry_diagonal_step (p : Nat.Primes) (n : ℕ) :
    kestenGreenEntry p (n + 1) (n + 1) - kestenGreenEntry p n n =
      primeReciprocal p ^ (2 * (n + 1)) := by
  have h₀ := kestenGreenEntry_diagonal_defect p n
  have h₁ := kestenGreenEntry_diagonal_defect p (n + 1)
  rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 by omega, pow_add] at h₁
  have he : primeReciprocal p ^ (2 * (n + 1)) / (1 - primeReciprocal p ^ 2) -
      primeReciprocal p ^ (2 * (n + 1)) * primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) =
        primeReciprocal p ^ (2 * (n + 1)) := by
    field_simp [(gap_pos p).ne']
  linarith only [h₀, h₁, he]

theorem strictMono_kestenGreenEntry_diagonal (p : Nat.Primes) :
    StrictMono (fun n : ℕ => kestenGreenEntry p n n) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := pow_pos (primeReciprocal_pos p) (2 * (n + 1))
  rw [← kestenGreenEntry_diagonal_step] at h
  exact sub_pos.mp h

theorem kestenGreenEntry_diagonal_lt_bulk (p : Nat.Primes) (n : ℕ) :
    kestenGreenEntry p n n < primeReciprocal p / (1 - primeReciprocal p ^ 2) := by
  have h := div_pos (pow_pos (primeReciprocal_pos p) (2 * (n + 1))) (gap_pos p)
  rw [← kestenGreenEntry_diagonal_defect] at h
  exact sub_pos.mp h

/-- Translating both depths leaves an exact geometric deficit from stationary covariance. -/
theorem kestenGreenEntry_translation_defect (p : Nat.Primes) (n m N : ℕ) :
    primeReciprocal p / (1 - primeReciprocal p ^ 2) * primeReciprocal p ^ Nat.dist n m -
      kestenGreenEntry p (n + N) (m + N) =
        primeReciprocal p ^ (n + m + 2 * N + 2) / (1 - primeReciprocal p ^ 2) := by
  rw [kestenGreenEntry_eq, Nat.dist_add_add_right,
    show (n + N) + (m + N) + 1 = n + m + 2 * N + 1 by omega,
    show n + m + 2 * N + 2 = (n + m + 2 * N + 1) + 1 by omega, pow_succ]
  ring

/-- Every translated Green matrix entry converges to the stationary geometric kernel. -/
theorem tendsto_kestenGreenEntry_translation (p : Nat.Primes) (n m : ℕ) :
    Tendsto (fun N : ℕ => kestenGreenEntry p (n + N) (m + N)) atTop
      (𝓝 (primeReciprocal p / (1 - primeReciprocal p ^ 2) * primeReciprocal p ^ Nat.dist n m)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (primeReciprocal p))
    (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide : (2 : ℕ) ≠ 0))
  have h := (tendsto_const_nhds (x := primeReciprocal p / (1 - primeReciprocal p ^ 2) *
    primeReciprocal p ^ Nat.dist n m)).sub
    (hp.const_mul (primeReciprocal p ^ (n + m + 2) / (1 - primeReciprocal p ^ 2)))
  have he (N : ℕ) : kestenGreenEntry p (n + N) (m + N) =
      primeReciprocal p / (1 - primeReciprocal p ^ 2) * primeReciprocal p ^ Nat.dist n m -
        (primeReciprocal p ^ (n + m + 2) / (1 - primeReciprocal p ^ 2)) *
          (primeReciprocal p ^ 2) ^ N := by
    have hd := kestenGreenEntry_translation_defect p n m N
    rw [show n + m + 2 * N + 2 = (n + m + 2) + 2 * N by omega, pow_add, pow_mul] at hd
    linear_combination -hd
  simpa only [mul_zero, sub_zero] using h.congr (fun N => (he N).symm)

/-- Deep diagonal Green responses increase to the stationary geometric variance. -/
theorem tendsto_kestenGreenEntry_diagonal (p : Nat.Primes) :
    Tendsto (fun n : ℕ => kestenGreenEntry p n n) atTop
      (𝓝 (primeReciprocal p / (1 - primeReciprocal p ^ 2))) := by
  simpa only [Nat.zero_add, Nat.dist_self, pow_zero, mul_one] using
    tendsto_kestenGreenEntry_translation p 0 0

end
end GaloisForLFunctions.SelbergClass.Primon
