import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSchedule

/-!
# Dyadic assembly of the block estimates

An interval `[A, A·2^R)` splits into the `R` dyadic blocks `[A·2^r, A·2^(r+1))`, so a sum over it is
the sum of the block sums and its norm is at most the sum of the block norms.  Each block has
`M = 2N` with `N = A·2^r`, hence satisfies the length constraint of the per-block estimate, and the
tail bound becomes a finite sum of the per-block savings.

The decomposition itself is stated for an arbitrary commutative monoid: it is the iterated form of
`Finset.sum_Ico_consecutive` and has no arithmetic content.
-/

namespace RHTower.Sieve

open Finset

/-- **Dyadic decomposition of an interval sum.**  Iterating `Finset.sum_Ico_consecutive` splits
`[A, A·2^R)` into the blocks `[A·2^r, A·2^(r+1))`. -/
theorem sum_Ico_dyadic {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) (R : ℕ) :
    ∑ n ∈ Finset.Ico A (A * 2 ^ R), f n
      = ∑ r ∈ Finset.range R, ∑ n ∈ Finset.Ico (A * 2 ^ r) (A * 2 ^ (r + 1)), f n := by
  induction R with
  | zero => simp
  | succ R ih =>
      have hmono : A * 2 ^ R ≤ A * 2 ^ (R + 1) := by
        exact Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hstart : A ≤ A * 2 ^ R := by
        calc A = A * 1 := (Nat.mul_one A).symm
          _ ≤ A * 2 ^ R := Nat.mul_le_mul_left A (Nat.one_le_two_pow)
      rw [Finset.sum_range_succ, ← ih,
        Finset.sum_Ico_consecutive f hstart hmono]

/-- **Triangle inequality across the dyadic blocks.** -/
theorem norm_sum_Ico_dyadic_le {E : Type*} [NormedAddCommGroup E] (A : ℕ)
    (f : ℕ → E) (R : ℕ) :
    ‖∑ n ∈ Finset.Ico A (A * 2 ^ R), f n‖
      ≤ ∑ r ∈ Finset.range R, ‖∑ n ∈ Finset.Ico (A * 2 ^ r) (A * 2 ^ (r + 1)), f n‖ := by
  rw [sum_Ico_dyadic A f R]
  exact norm_sum_le _ _

/-- **Dyadic tail estimate.**  If every dyadic block above `A` admits an order `k` at the classical
scale, the tail of the Dirichlet sum on the line `Re s = 1` is bounded by the sum of the block
savings. -/
theorem dirichlet_tail_dyadic_le {t : ℝ} (ht : 0 < t) {A R : ℕ} (hA : 1 ≤ A) (k : ℕ → ℕ)
    (hk : ∀ r < R, 2 ≤ k r)
    (hfac : ∀ r < R, Nat.factorial (k r - 1) ≤ A * 2 ^ r)
    (hlow : ∀ r < R, 8 * Real.pi * ((A * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r < R, t ≤ 2 * Real.pi * 2 ^ (k r) * ((A * 2 ^ r : ℕ) : ℝ) ^ (k r - 1)
      * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico A (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ ∑ r ∈ Finset.range R,
          2560 * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ (k r)))) := by
  refine le_trans (norm_sum_Ico_dyadic_le A _ R) ?_
  refine Finset.sum_le_sum fun r hr => ?_
  have hrR : r < R := Finset.mem_range.mp hr
  have hN : 1 ≤ A * 2 ^ r := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  have hspan : A * 2 ^ (r + 1) = 2 * (A * 2 ^ r) := by ring
  rw [hspan]
  exact dirichlet_block_saving_of_small_factorial ht hN (by omega) (by omega) (hk r hrR)
    (hfac r hrR) (hlow r hrR) (hhigh r hrR)

end RHTower.Sieve
