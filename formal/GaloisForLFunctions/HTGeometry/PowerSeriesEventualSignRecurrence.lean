import Mathlib

/-!
# Eventual-sign recurrence for real power series

A real power series whose coefficients are eventually nonpositive is bounded on `[0,1)` by the sum of
absolute values of its finitely many earlier coefficients
(`tsum_mul_pow_le_sum_range_abs_of_eventually_nonpos`).  Contrapositively, a series whose value
exceeds every such finite prefix bound (for radii approaching `1`) must have positive coefficients
infinitely often (`frequently_pos_of_forall_exists_tsum_gt`).

This is the coefficient-recurrence engine behind Abel-summation positivity laws: once an Abel or
Hankel-type series is shown to blow up as the radius approaches the boundary, its coefficient sequence
is forced to be positive at cofinally many indices, independently of any analytic continuation of the
generating function.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- **Prefix bound for eventually-nonpositive power series.**  If `c q ≤ 0` for all `q ≥ Q`, then for
every `u ∈ [0,1]` the Abel sum `∑' q, c q u^q` is at most `∑_{q<Q} |c q|`: the nonpositive tail only
decreases the sum, and each of the finitely many earlier terms is bounded by `|c q|`. -/
theorem tsum_mul_pow_le_sum_range_abs_of_eventually_nonpos {c : ℕ → ℝ} {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hsum : Summable (fun q => c q * u ^ q))
    {Q : ℕ} (hQ : ∀ q, Q ≤ q → c q ≤ 0) :
    ∑' q, c q * u ^ q ≤ ∑ q ∈ Finset.range Q, |c q| := by
  rw [← Summable.sum_add_tsum_nat_add Q hsum]
  have htail : ∑' q, c (q + Q) * u ^ (q + Q) ≤ 0 := by
    apply tsum_nonpos
    intro q
    exact mul_nonpos_of_nonpos_of_nonneg (hQ _ (Nat.le_add_left Q q)) (by positivity)
  have hpre : ∑ q ∈ Finset.range Q, c q * u ^ q ≤ ∑ q ∈ Finset.range Q, |c q| := by
    apply Finset.sum_le_sum
    intro q _
    calc c q * u ^ q ≤ |c q * u ^ q| := le_abs_self _
      _ = |c q| * u ^ q := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ q)]
      _ ≤ |c q| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hu hu1) (abs_nonneg _)
      _ = |c q| := mul_one _
  linarith

/-- **Coefficient recurrence from boundary blow-up.**  If a real power series with radius of
convergence at least `1` exceeds every finite prefix bound `∑_{q<Q} |c q|` for some radius `u < 1`,
then its coefficients are positive at infinitely many indices.  This is the contrapositive of the
prefix bound: eventual nonpositivity would cap the Abel sum. -/
theorem frequently_pos_of_forall_exists_tsum_gt {c : ℕ → ℝ}
    (hsum : ∀ u : ℝ, 0 ≤ u → u < 1 → Summable (fun q => c q * u ^ q))
    (hub : ∀ Q : ℕ, ∃ u : ℝ, 0 ≤ u ∧ u < 1 ∧
      ∑ q ∈ Finset.range Q, |c q| < ∑' q, c q * u ^ q) :
    ∃ᶠ q in Filter.atTop, 0 < c q := by
  rw [Filter.frequently_atTop]
  intro Q
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨u, hu, hu1, hgt⟩ := hub Q
  have hbound := tsum_mul_pow_le_sum_range_abs_of_eventually_nonpos hu hu1.le (hsum u hu hu1)
    (Q := Q) (fun q hq => hcon q hq)
  linarith

end GaloisForLFunctions.HTGeometry
