import GaloisForLFunctions.SelbergClass.Primon.KestenGreenKernel

/-!
# Exact Schur conditioning of the prime Green kernel

Removing one observed depth by a scalar Schur complement separates past
and future. The remaining future covariance depends only on the offsets,
not on the observed depth or its boundary variance. Each new depth has
innovation variance exactly `q=1/p`.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Propagation from a fixed depth is its diagonal covariance times a geometric factor. -/
theorem kestenGreenEntry_propagation (p : Nat.Primes) (n k : ℕ) :
    kestenGreenEntry p n (n + k) = primeReciprocal p ^ k * kestenGreenEntry p n n := by
  rw [kestenGreenEntry_add, kestenGreenEntry_diagonal, pow_succ]
  ring

/-- Each successor variance is the propagated variance plus one fresh variance `q`. -/
theorem kestenGreenEntry_variance_recursion (p : Nat.Primes) (n : ℕ) :
    kestenGreenEntry p (n + 1) (n + 1) =
      primeReciprocal p + primeReciprocal p ^ 2 * kestenGreenEntry p n n := by
  rw [kestenGreenEntry_diagonal, kestenGreenEntry_diagonal,
    show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
  have hgap : 1 - primeReciprocal p ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le
      (primeReciprocal_lt_one p) (by decide : (2 : ℕ) ≠ 0))).ne'
  field_simp
  ring

/-- The one-step scalar Schur complement is exactly the prime reciprocal. -/
theorem kestenGreenEntry_successor_schur (p : Nat.Primes) (n : ℕ) :
    kestenGreenEntry p (n + 1) (n + 1) -
      kestenGreenEntry p n (n + 1) ^ 2 / kestenGreenEntry p n n = primeReciprocal p := by
  rw [kestenGreenEntry_variance_recursion, kestenGreenEntry_propagation, pow_one]
  field_simp [(kestenGreenEntry_pos p n n).ne']
  ring

/-- A future block splits into its inherited boundary variance and a depth-independent remainder. -/
theorem kestenGreenEntry_future_decomposition (p : Nat.Primes) (n i j : ℕ) :
    kestenGreenEntry p (n + i) (n + j) =
      primeReciprocal p ^ (i + j) * kestenGreenEntry p n n +
        primeReciprocal p / (1 - primeReciprocal p ^ 2) *
          (primeReciprocal p ^ Nat.dist i j - primeReciprocal p ^ (i + j)) := by
  have hd : Nat.dist (n + i) (n + j) = Nat.dist i j := by
    rw [Nat.add_comm n i, Nat.add_comm n j, Nat.dist_add_add_right]
  rw [kestenGreenEntry_eq, hd, kestenGreenEntry_diagonal,
    show (n + i) + (n + j) + 1 = (2 * n + 1) + (i + j) by omega, pow_add]
  ring

/-- Conditioning on one depth removes all memory of its boundary variance from the future block. -/
theorem kestenGreenEntry_future_schur (p : Nat.Primes) (n i j : ℕ) :
    kestenGreenEntry p (n + i) (n + j) -
      kestenGreenEntry p (n + i) n * kestenGreenEntry p n (n + j) / kestenGreenEntry p n n =
        primeReciprocal p / (1 - primeReciprocal p ^ 2) *
          (primeReciprocal p ^ Nat.dist i j - primeReciprocal p ^ (i + j)) := by
  rw [kestenGreenEntry_symm p (n + i) n, kestenGreenEntry_propagation,
    kestenGreenEntry_propagation, kestenGreenEntry_future_decomposition]
  have hc : (primeReciprocal p ^ i * kestenGreenEntry p n n) *
      (primeReciprocal p ^ j * kestenGreenEntry p n n) / kestenGreenEntry p n n =
        primeReciprocal p ^ (i + j) * kestenGreenEntry p n n := by
    rw [pow_add]
    field_simp [(kestenGreenEntry_pos p n n).ne']
  rw [hc]
  ring

/-- A scalar Schur complement at an intermediate depth annihilates past-future covariance. -/
theorem kestenGreenEntry_past_future_schur (p : Nat.Primes) (n i j : ℕ) :
    kestenGreenEntry p n (n + i + j) -
      kestenGreenEntry p n (n + i) * kestenGreenEntry p (n + i) (n + i + j) /
        kestenGreenEntry p (n + i) (n + i) = 0 := by
  have h := kestenGreenEntry_markov p n i j
  apply (sub_eq_zero.mpr ?_)
  exact (eq_div_iff (kestenGreenEntry_pos p (n + i) (n + i)).ne').mpr h

end
end GaloisForLFunctions.SelbergClass.Primon
