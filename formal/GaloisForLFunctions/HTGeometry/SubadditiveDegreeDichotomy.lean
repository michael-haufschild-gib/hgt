import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The two branches of a subadditive degree sequence

A subadditive sequence of natural numbers which vanishes at one positive index is bounded: the
value at `k·N` is zero, and every index is `k·N` plus a remainder below `N`.

A subadditive sequence which is *exactly* additive along the multiples of one positive index grows
at least linearly with slope `d N / N`: rounding up to the next multiple costs at most `N·d 1`.

These are the two branches of the dichotomy for the degree of a twisted product of operator
matrices.  Once one knows that some stage has non-vanishing leading products, the degree along that
stage is exactly additive, and then either it is zero — the bounded phase — or it is positive and
the normalized limit is `d N / N > 0`.

* `eq_zero_of_mul_of_eq_zero`, `le_sup_of_subadditive_of_eq_zero` — the bounded branch;
* `le_mul_of_subadditive`, `mul_le_of_subadditive_of_exact` — the linear branch.
-/

namespace GaloisForLFunctions.HTGeometry

variable {d : ℕ → ℕ}

theorem le_mul_of_subadditive (hsub : ∀ n m, d (n + m) ≤ d n + d m) (hd0 : d 0 = 0) (m : ℕ) :
    d m ≤ m * d 1 := by
  induction m with
  | zero => rw [hd0]; omega
  | succ m ih =>
      have h := hsub m 1
      have : d (m + 1) ≤ d m + d 1 := h
      have hm : m * d 1 + d 1 = (m + 1) * d 1 := by ring
      omega

theorem eq_zero_of_mul_of_eq_zero (hsub : ∀ n m, d (n + m) ≤ d n + d m) (hd0 : d 0 = 0)
    {N : ℕ} (hd : d N = 0) (k : ℕ) : d (k * N) = 0 := by
  induction k with
  | zero => rw [Nat.zero_mul, hd0]
  | succ k ih =>
      have hidx : (k + 1) * N = k * N + N := by ring
      have h := hsub (k * N) N
      rw [← hidx] at h
      omega

/-- **The bounded branch.**  A subadditive sequence vanishing at a positive index is bounded by its
values below that index. -/
theorem le_sup_of_subadditive_of_eq_zero (hsub : ∀ n m, d (n + m) ≤ d n + d m) (hd0 : d 0 = 0)
    {N : ℕ} (hN : 0 < N) (hd : d N = 0) (n : ℕ) :
    d n ≤ (Finset.range N).sup d := by
  have hdecomp : n = (n / N) * N + n % N := by
    rw [Nat.div_add_mod' n N]
  have hmod : n % N < N := Nat.mod_lt _ hN
  have hle : d n ≤ d ((n / N) * N) + d (n % N) := by
    conv_lhs => rw [hdecomp]
    exact hsub _ _
  rw [eq_zero_of_mul_of_eq_zero hsub hd0 hd (n / N)] at hle
  have hle2 : d n ≤ d (n % N) := by omega
  exact le_trans hle2 (Finset.le_sup (f := d) (Finset.mem_range.mpr hmod))

/-- **The linear branch.**  A subadditive sequence which is exactly additive along the multiples of
`N` grows at least linearly with slope `d N / N`. -/
theorem mul_le_of_subadditive_of_exact (hsub : ∀ n m, d (n + m) ≤ d n + d m) (hd0 : d 0 = 0)
    {N : ℕ} (hN : 0 < N) (hexact : ∀ k, d (k * N) = k * d N) (n : ℕ) :
    n * d N ≤ N * (d n + N * d 1) := by
  classical
  set k : ℕ := (n + N - 1) / N with hk
  have hdm : k * N + (n + N - 1) % N = n + N - 1 := by
    rw [hk]
    exact Nat.div_add_mod' (n + N - 1) N
  have hmodlt : (n + N - 1) % N < N := Nat.mod_lt _ hN
  have hkN : n ≤ k * N := by omega
  have hgap : k * N - n < N := by omega
  have hstep : d (k * N) ≤ d n + d (k * N - n) := by
    have hidx : n + (k * N - n) = k * N := by omega
    have := hsub n (k * N - n)
    rw [hidx] at this
    exact this
  have hgapbound : d (k * N - n) ≤ N * d 1 := by
    refine le_trans (le_mul_of_subadditive hsub hd0 _) ?_
    exact Nat.mul_le_mul_right _ (le_of_lt hgap)
  rw [hexact k] at hstep
  have hchain : n * d N ≤ (k * N) * d N := Nat.mul_le_mul_right _ hkN
  calc n * d N ≤ (k * N) * d N := hchain
    _ = N * (k * d N) := by ring
    _ ≤ N * (d n + N * d 1) := Nat.mul_le_mul_left _ (by omega)

end GaloisForLFunctions.HTGeometry
