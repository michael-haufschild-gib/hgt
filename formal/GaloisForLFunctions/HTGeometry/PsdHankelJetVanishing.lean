import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Vanishing of a semidefinite Hankel jet sequence

A root of multiplicity `m` of a null state of a nonnegative form produces the divided descendants
`F/(u-r)^k`, whose Gram entries depend only on the sum of the two indices.  Writing that Hankel
sequence as `M`, the Cauchy–Schwarz inequality of the semidefinite form reads

`M (p+q)² ≤ M (2p)·M (2q)`,

and the null state itself gives `M j = 0` for `1 ≤ j ≤ m`.  Then every entry below the terminal one
vanishes: `M j = 0` for `1 ≤ j < 2m`.  The mechanism is a one-step bootstrap — each new null
descendant extends the vanishing range by one — and it is what makes the divided-jet Gram matrix
diagonal with a single terminal entry.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry


/-! ## The discriminant inequality -/

/-- **A nonnegative real quadratic has nonpositive discriminant.** -/
theorem sq_le_of_quadratic_nonneg {a b c : ℝ}
    (h : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * c) : b ^ 2 ≤ a * c := by
  have hc : 0 ≤ c := by
    by_contra hneg
    rw [not_le] at hneg
    have hcpos : (0 : ℝ) < -c := by linarith
    have hpos : (0 : ℝ) < (|a| + 1) / (-c) := by positivity
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k ^ 2 = (|a| + 1) / (-c) :=
      ⟨Real.sqrt ((|a| + 1) / (-c)), Real.sq_sqrt hpos.le⟩
    have hsum : 0 ≤ 2 * a + 2 * (k ^ 2 * c) := by
      have h1 := h k
      have h2 := h (-k)
      nlinarith [h1, h2]
    have hcne : c ≠ 0 := ne_of_lt hneg
    have hkc : k ^ 2 * c = -(|a| + 1) := by
      rw [hk]
      field_simp
    rw [hkc] at hsum
    have hle : a ≤ |a| := le_abs_self a
    linarith
  rcases eq_or_lt_of_le hc with hc0 | hc0
  · have hczero : c = 0 := hc0.symm
    have hb : b = 0 := by
      by_contra hne
      have hq := h (-(a + 1) / (2 * b))
      rw [hczero, mul_zero, add_zero] at hq
      have h2 : (2 : ℝ) * b ≠ 0 := by simpa using hne
      have hcalc : a + 2 * (-(a + 1) / (2 * b)) * b = -1 := by
        field_simp
        ring
      rw [hcalc] at hq
      linarith
    rw [hb, hczero]
    norm_num
  · have hq := h (-b / c)
    have hne : c ≠ 0 := ne_of_gt hc0
    have hcalc : a + 2 * (-b / c) * b + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp
      ring
    rw [hcalc] at hq
    have h2 : b ^ 2 / c ≤ a := by linarith
    calc b ^ 2 = (b ^ 2 / c) * c := by field_simp
      _ ≤ a * c := mul_le_mul_of_nonneg_right h2 hc0.le

/-! ## Cauchy--Schwarz for a nonnegative symmetric form -/

/-- **Cauchy--Schwarz for a nonnegative real symmetric form.**  The hypothesis records the
expansion of the form along a one-parameter combination, which is all the bilinearity the
inequality uses. -/
theorem symmBilin_sq_le {X : Type*} {S : X → X → ℝ} {comb : ℝ → X → X → X}
    (hexp : ∀ (t : ℝ) (u v : X), S (comb t u v) (comb t u v)
      = S u u + 2 * t * S u v + t ^ 2 * S v v)
    (hpsd : ∀ x : X, 0 ≤ S x x) (u v : X) : S u v ^ 2 ≤ S u u * S v v := by
  have hquad : ∀ t : ℝ, 0 ≤ S u u + 2 * t * S u v + t ^ 2 * S v v := by
    intro t
    rw [← hexp t u v]
    exact hpsd _
  rcases eq_or_lt_of_le (hpsd v) with hv | hv
  · have hvv : S v v = 0 := hv.symm
    have huv : S u v = 0 := by
      by_contra hne
      have hq := hquad (-(S u u + 1) / (2 * S u v))
      rw [hvv, mul_zero, add_zero] at hq
      have h2 : (2 : ℝ) * S u v ≠ 0 := by
        simpa using hne
      have hcalc : S u u + 2 * (-(S u u + 1) / (2 * S u v)) * S u v = -1 := by
        field_simp
        ring
      rw [hcalc] at hq
      linarith
    rw [huv, hvv]
    norm_num
  · have hq := hquad (-(S u v) / S v v)
    have hne : S v v ≠ 0 := ne_of_gt hv
    have hcalc : S u u + 2 * (-(S u v) / S v v) * S u v + (-(S u v) / S v v) ^ 2 * S v v
        = S u u - S u v ^ 2 / S v v := by
      field_simp
      ring
    rw [hcalc] at hq
    have h2 : S u v ^ 2 / S v v ≤ S u u := by linarith
    calc S u v ^ 2 = (S u v ^ 2 / S v v) * S v v := by field_simp
      _ ≤ S u u * S v v := by
          exact mul_le_mul_of_nonneg_right h2 hv.le

/-- **The semidefinite Hankel bootstrap.**  A Hankel sequence whose Cauchy–Schwarz inequality holds
up to index `m` and which vanishes on `1 ≤ j ≤ m` vanishes on all of `1 ≤ j < 2m`. -/
theorem psdHankel_jet_vanishing {M : ℕ → ℝ} {m : ℕ}
    (hCS : ∀ p q : ℕ, p ≤ m → q ≤ m → M (p + q) ^ 2 ≤ M (2 * p) * M (2 * q))
    (hbase : ∀ j : ℕ, 1 ≤ j → j ≤ m → M j = 0) :
    ∀ j : ℕ, 1 ≤ j → j < 2 * m → M j = 0 := by
  have key : ∀ k : ℕ, k < m → ∀ j : ℕ, 1 ≤ j → j ≤ m + k → M j = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ j hj1 hj2
      exact hbase j hj1 (by omega)
    | succ k ih =>
      intro hk j hj1 hj2
      rcases le_or_gt j (m + k) with h | h
      · exact ih (by omega) j hj1 h
      · have hjeq : j = k + 1 + m := by omega
        have hzero : M (2 * (k + 1)) = 0 := ih (by omega) (2 * (k + 1)) (by omega) (by omega)
        have hcs := hCS (k + 1) m (by omega) le_rfl
        rw [hzero, zero_mul] at hcs
        have hval : M (k + 1 + m) = 0 := by
          nlinarith [sq_nonneg (M (k + 1 + m))]
        rw [hjeq]
        exact hval
  intro j hj1 hj2
  rcases Nat.eq_zero_or_pos m with hm | hm
  · omega
  · exact key (m - 1) (by omega) j hj1 (by omega)

/-- **The divided-jet Gram law.**  Off the terminal corner every entry of the Gram matrix of the
divided descendants vanishes. -/
theorem psdHankel_gram_off_terminal {M : ℕ → ℝ} {m : ℕ}
    (hCS : ∀ p q : ℕ, p ≤ m → q ≤ m → M (p + q) ^ 2 ≤ M (2 * p) * M (2 * q))
    (hbase : ∀ j : ℕ, 1 ≤ j → j ≤ m → M j = 0)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpm : p ≤ m) (hqm : q ≤ m)
    (hne : ¬(p = m ∧ q = m)) :
    M (p + q) = 0 := by
  refine psdHankel_jet_vanishing hCS hbase (p + q) (by omega) ?_
  rcases Nat.lt_or_ge p m with h | h
  · omega
  · have hpm' : p = m := le_antisymm hpm h
    have hqm' : q < m := by
      rcases Nat.lt_or_ge q m with h' | h'
      · exact h'
      · exact absurd ⟨hpm', le_antisymm hqm h'⟩ hne
    omega

end GaloisForLFunctions.HTGeometry

end
