import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The harmonic primitive ladder is exact sequence algebra

Discrete Abel summation against a weight `w` exchanges a primitive of `w f` for a difference
quotient of the receiver:

`∑_{n ≤ M+1} f_n w_n A_n = g_{M+1} A_{M+1} − g_0 A_1 + ∑_{n ≤ M} g_n w_n (𝒟A)_n`,

where `g` is any primitive of `w f` and `(𝒟A)_n = (A_n − A_{n+1})/w_n`.  Iterating gives the exact
ladder identity: after `k` steps the pairing is a sum of `k` endpoint terms plus the pairing of the
`k`-th primitive against the `k`-th difference quotient.  Nothing asymptotic enters, so no finite
number of Abel integrations can change the pairing; it can only move mass between the endpoints and
the interior.
-/

namespace RHTower

noncomputable section

/-- The weighted pairing `∑_{n ≤ M} f_n w_n A_n`. -/
def abelPairing (f w A : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, f n * w n * A n

/-- The weighted backward difference quotient `(A_n − A_{n+1})/w_n`. -/
def discreteDeriv (w A : ℕ → ℝ) (n : ℕ) : ℝ := (A n - A (n + 1)) / w n

/-- Discrete summation by parts against an arbitrary primitive. -/
theorem sum_telescope_abel (g A : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 (M + 1), (g n - g (n - 1)) * A n
      = g (M + 1) * A (M + 1) - g 0 * A 1
        + ∑ n ∈ Finset.Icc 1 M, g n * (A n - A (n + 1)) := by
  induction M with
  | zero => simp [sub_mul]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

/-- **(24.69) The exact Abel recursion.** -/
theorem abelPairing_recursion {f w A g : ℕ → ℝ} (hw : ∀ n, 1 ≤ n → w n ≠ 0)
    (hg : ∀ n, 1 ≤ n → g n - g (n - 1) = w n * f n) (M : ℕ) :
    abelPairing f w A (M + 1)
      = g (M + 1) * A (M + 1) - g 0 * A 1 + abelPairing g w (discreteDeriv w A) M := by
  have h1 : ∀ n ∈ Finset.Icc 1 (M + 1), f n * w n * A n = (g n - g (n - 1)) * A n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [hg n hn.1]
    ring
  rw [abelPairing, Finset.sum_congr rfl h1, sum_telescope_abel]
  congr 1
  rw [abelPairing]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hwn := hw n hn.1
  rw [discreteDeriv]
  field_simp

/-- **(24.70) The exact ladder identity.**  After `k` Abel steps the pairing is `k` endpoint terms
plus the pairing of the `k`-th primitive against the `k`-th difference quotient. -/
theorem abelPairing_ladder {w : ℕ → ℝ} (hw : ∀ n, 1 ≤ n → w n ≠ 0) (F A : ℕ → ℕ → ℝ)
    (hF : ∀ j n, 1 ≤ n → F (j + 1) n - F (j + 1) (n - 1) = w n * F j n)
    (hA : ∀ j, A (j + 1) = discreteDeriv w (A j)) {k N : ℕ} (hk : k ≤ N) :
    abelPairing (F 0) w (A 0) N
      = ∑ j ∈ Finset.range k, (F (j + 1) (N - j) * A j (N - j) - F (j + 1) 0 * A j 1)
        + abelPairing (F k) w (A k) (N - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN : k ≤ N := by omega
    have hsplit : N - k = (N - (k + 1)) + 1 := by omega
    have hstep := abelPairing_recursion (f := F k) (w := w) (A := A k) (g := F (k + 1))
      hw (fun n hn => hF k n hn) (N - (k + 1))
    rw [ih hkN, hsplit, hstep, ← hA k, Finset.sum_range_succ, ← hsplit]
    ring

end

end RHTower
