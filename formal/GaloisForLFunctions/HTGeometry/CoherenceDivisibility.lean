/-
Coherence of a class carries a divisibility constraint, not only an approximation one.

A `√d`-class contributes its full size to the frontier sum only when all its members' phases align.
Writing `x = N√d` and `k` for the nearest integer to `x`, a member `(m, q)` contributes the phase
`x·m/q = k·m/q + O(ε m/q)` where `ε = |x - k|`.  The rational part `k m / q` is either an integer or
at distance at least `1/q` from every integer:

    **for `q ≥ 1` and `q ∤ j`,  dist(j/q, ℤ) ≥ 1/q** ,

since `|j/q - k'| = |j - k'q|/q` and `j - k'q` is a nonzero integer.

So a member `(m, q)` can be coherent only when `q ∣ k m`.  The campaign's counting attacks (cycles
250–251) addressed the approximation side `|N√d - k| ≤ ε` alone; the divisibility side `q ∣ k m` is a
purely arithmetic constraint that has not been used.  Since a class has `≍ L` members with distinct
`q ≤ L`, full coherence demands `q ∣ k m` **simultaneously across the class**, which is a congruence
condition on `k` — hence on the integer nearest to `N√d`.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace HTGeometry

/-! ### The divisibility dichotomy -/

/-- **A rational with denominator `q` is either an integer or `1/q`-far from every integer.** -/
theorem dist_rat_int_lower {q : ℕ} (hq : 0 < q) {j : ℤ} (hdvd : ¬ ((q : ℤ) ∣ j)) (k : ℤ) :
    1 / (q : ℝ) ≤ |(j : ℝ) / (q : ℝ) - (k : ℝ)| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hne : j - k * (q : ℤ) ≠ 0 := by
    intro hz
    exact hdvd ⟨k, by linarith [hz]⟩
  have hone : (1 : ℝ) ≤ |(j : ℝ) - (k : ℝ) * (q : ℝ)| := by
    have h : (1 : ℤ) ≤ |j - k * (q : ℤ)| := Int.one_le_abs hne
    calc (1 : ℝ) ≤ ((|j - k * (q : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |(j : ℝ) - (k : ℝ) * (q : ℝ)| := by push_cast; ring_nf
  rw [div_le_iff₀ hq0] at *
  have hrw : |(j : ℝ) / (q : ℝ) - (k : ℝ)| * (q : ℝ) = |(j : ℝ) - (k : ℝ) * (q : ℝ)| := by
    rw [show (j : ℝ) / (q : ℝ) - (k : ℝ) = ((j : ℝ) - (k : ℝ) * (q : ℝ)) / (q : ℝ) by
      field_simp, abs_div, abs_of_pos hq0, div_mul_cancel₀ _ (ne_of_gt hq0)]
  rw [hrw]
  linarith

/-- **Contrapositive: a rational strictly closer than `1/q` to an integer has `q` dividing its
numerator.** -/
theorem dvd_of_close {q : ℕ} (hq : 0 < q) {j : ℤ} {k : ℤ}
    (h : |(j : ℝ) / (q : ℝ) - (k : ℝ)| < 1 / (q : ℝ)) : (q : ℤ) ∣ j := by
  by_contra hdvd
  exact absurd (dist_rat_int_lower hq hdvd k) (not_le.mpr h)

/-! ### The coherence criterion for a class member -/

/-- The perturbation a class member's phase inherits from the approximation error. -/
theorem member_phase_split {x : ℝ} {k : ℤ} {m q : ℕ} (hq : 0 < q) {ε : ℝ}
    (hx : |x - (k : ℝ)| ≤ ε) :
    |x * (m : ℝ) / (q : ℝ) - (k : ℝ) * (m : ℝ) / (q : ℝ)| ≤ ε * (m : ℝ) / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hrw : x * (m : ℝ) / (q : ℝ) - (k : ℝ) * (m : ℝ) / (q : ℝ)
      = (x - (k : ℝ)) * (m : ℝ) / (q : ℝ) := by ring
  rw [hrw, abs_div, abs_mul, abs_of_pos hq0, abs_of_nonneg hm0]
  apply div_le_div_of_nonneg_right'
  · exact mul_le_mul_of_nonneg_right hx hm0
  · exact hq0
where
  div_le_div_of_nonneg_right' {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
    rw [div_le_div_iff_of_pos_right hc]; exact hab

/-- **The coherence criterion.**  If a member's phase is within `1/q` of an integer *after* the
approximation error is accounted for, then `q` divides `k·m`. -/
theorem coherent_member_forces_dvd {q m : ℕ} (hq : 0 < q) {k k' : ℤ}
    (h : |((k * m : ℤ) : ℝ) / (q : ℝ) - (k' : ℝ)| < 1 / (q : ℝ)) :
    (q : ℤ) ∣ (k * m : ℤ) :=
  dvd_of_close hq h

/-- **The dichotomy, stated for the class.**  Each member is either exactly aligned — `q ∣ k m` — or
its rational phase is at distance at least `1/q` from the integers, a gap the approximation error
must cover. -/
theorem member_dichotomy {q : ℕ} (hq : 0 < q) (m : ℕ) (k : ℤ) :
    ((q : ℤ) ∣ (k * m : ℤ)) ∨ ∀ k' : ℤ, 1 / (q : ℝ) ≤ |((k * m : ℤ) : ℝ) / (q : ℝ) - (k' : ℝ)| := by
  by_cases hdvd : (q : ℤ) ∣ (k * m : ℤ)
  · exact Or.inl hdvd
  · exact Or.inr fun k' => dist_rat_int_lower hq hdvd k'

/-- **The unused constraint.**  Full coherence of a class with members of denominators `q₁, …, q_r`
requires `q_i ∣ k m_i` for every `i` — a simultaneous congruence condition on the integer nearest to
`N√d`, independent of how well `N√d` is approximated. -/
theorem simultaneous_divisibility_required {r : ℕ} (q m : Fin r → ℕ) (hq : ∀ i, 0 < q i) (k : ℤ)
    (k' : Fin r → ℤ)
    (hall : ∀ i, |((k * m i : ℤ) : ℝ) / ((q i : ℕ) : ℝ) - ((k' i : ℤ) : ℝ)| < 1 / ((q i : ℕ) : ℝ)) :
    ∀ i, ((q i : ℕ) : ℤ) ∣ (k * m i : ℤ) :=
  fun i => dvd_of_close (hq i) (hall i)

end HTGeometry
