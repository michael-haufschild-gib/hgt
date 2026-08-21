import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.CompleteLattice.Finset

/-!
# The S-unit hyperplane sup bound and the positive-part contraction

Two elementary inequalities from

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

§VII.

* §VII (8).  The logarithmic S-unit map `L : O_S^* → ℝ^S`, `L(u)_v = log |u_v|`, has range inside
  the hyperplane `H = {y : ∑_{v ∈ S} y_v = 0}` (the product formula).  On `H` one has
  `Sup_S y_v ≥ (1/(2n)) ∑_S |y_v|` with `n = card S`, which is the inequality that turns the word
  metric of the finitely generated abelian group `O_S^*` into the geometric decay
  `Sup_S |q_v| ≥ exp(d(q,1))` used in Lemma VII.1 and Lemma VII.2.
* §VII (43).  The contraction `|a⁺ - b⁺| ≤ |a - b|` of positive parts, used to compare the cutoff
  weights `ε_Λ(x + ε)` and `ε_Λ(x)`.
-/

namespace GaloisForLFunctions.RHTower

open Finset

/-- **§VII (8).**  On the hyperplane `∑_{v ∈ S} y_v = 0` the largest coordinate already carries a
definite proportion `1/(2 · card S)` of the total `ℓ¹` mass. -/
theorem connes_sum_abs_le_card_mul_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (y : ι → ℝ) (hy : ∑ v ∈ s, y v = 0) :
    ∑ v ∈ s, |y v| ≤ 2 * (s.card : ℝ) * s.sup' hs y := by
  set M : ℝ := s.sup' hs y with hM
  have hle : ∀ v ∈ s, y v ≤ M := fun v hv => Finset.le_sup' y hv
  have hMnonneg : 0 ≤ M := by
    by_contra hneg
    push Not at hneg
    have : ∑ v ∈ s, y v < 0 := by
      calc ∑ v ∈ s, y v ≤ ∑ _v ∈ s, M := Finset.sum_le_sum hle
        _ = (s.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
        _ < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast Finset.card_pos.mpr hs) hneg
    rw [hy] at this
    exact lt_irrefl 0 this
  have habs : ∀ v, |y v| = 2 * max (y v) 0 - y v := by
    intro v
    rcases le_total 0 (y v) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  have hsum : ∑ v ∈ s, |y v| = 2 * ∑ v ∈ s, max (y v) 0 := by
    simp_rw [habs]
    rw [Finset.sum_sub_distrib, hy, ← Finset.mul_sum]
    ring
  have hbound : ∑ v ∈ s, max (y v) 0 ≤ (s.card : ℝ) * M := by
    calc ∑ v ∈ s, max (y v) 0 ≤ ∑ _v ∈ s, M :=
          Finset.sum_le_sum fun v hv => max_le (hle v hv) hMnonneg
      _ = (s.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  nlinarith [hbound]

/-- **§VII (8), quotient form.**  The largest coordinate dominates `1/(2 card S)` of the `ℓ¹` mass. -/
theorem connes_sup'_ge_sum_abs_div {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (y : ι → ℝ) (hy : ∑ v ∈ s, y v = 0) :
    (∑ v ∈ s, |y v|) / (2 * (s.card : ℝ)) ≤ s.sup' hs y := by
  have hcard : (0:ℝ) < 2 * (s.card : ℝ) := by
    have : (0:ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
    linarith
  rw [div_le_iff₀ hcard]
  simpa [mul_comm] using connes_sum_abs_le_card_mul_sup' s hs y hy

/-- **§VII (43).**  The positive part is a contraction. -/
theorem connes_abs_posPart_sub_posPart_le (a b : ℝ) : |max a 0 - max b 0| ≤ |a - b| :=
  abs_sup_sub_sup_le_abs a b 0

end GaloisForLFunctions.RHTower
