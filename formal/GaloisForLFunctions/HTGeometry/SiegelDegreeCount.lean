import Mathlib.Tactic

/-!
# The arithmetic of the Siegel degree count

The inequality that makes a Siegel-type count close.  Clearing denominators from a polynomial of
degree at most `(n+1)·m` in the values of `n+1` meromorphic functions raises the comparison constant
to the power `(n+1)·m`, so the Schwarz gain forces the jet order `N` to grow only linearly in `m`,
say `N = A·m`.  The number of conditions is then at most `K·(A·m)^n` — `K` centres, each imposing
the vanishing of the complex Taylor jets of order below `N` in `n` variables — while the number of
free coefficients is at least `(m+1)^(n+1)`.

Since `n < n+1`, the coefficients win for every large `m`: this is the one place where the dimension
of the torus enters, and it is why the bound is `trdeg ≤ dim` and not something weaker.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Siegel degree inequality.**  Once the degree exceeds `K·A^n`, there are more coefficients
than conditions. -/
theorem siegel_count_lt {K A n : ℕ} (_hn : 1 ≤ n) {m : ℕ} (hm : K * A ^ n < m) :
    K * (A * m) ^ n < (m + 1) ^ (n + 1) := by
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
  have hrw : K * (A * m) ^ n = K * A ^ n * m ^ n := by
    rw [mul_pow]
    ring
  rw [hrw]
  have hstep : K * A ^ n * m ^ n < m * m ^ n :=
    (Nat.mul_lt_mul_right (Nat.pow_pos hmpos)).mpr hm
  refine lt_of_lt_of_le hstep ?_
  have hmm : m * m ^ n = m ^ (n + 1) := by
    rw [pow_succ]
    ring
  rw [hmm]
  exact Nat.pow_le_pow_left (Nat.le_succ m) (n + 1)

/-- **A degree that makes the count close exists.** -/
theorem exists_siegel_degree (K A n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 0 < m ∧ K * (A * m) ^ n < (m + 1) ^ (n + 1) := by
  refine ⟨K * A ^ n + 1, Nat.succ_pos _, siegel_count_lt hn (Nat.lt_succ_self _)⟩

/-- **All large degrees make the count close.** -/
theorem eventually_siegel_count (K A n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, K * A ^ n < m → K * (A * m) ^ n < (m + 1) ^ (n + 1) :=
  fun _ hm => siegel_count_lt hn hm

end GaloisForLFunctions.HTGeometry
