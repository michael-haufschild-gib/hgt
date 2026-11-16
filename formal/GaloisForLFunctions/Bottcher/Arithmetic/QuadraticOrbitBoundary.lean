import GaloisForLFunctions.Bottcher.Arithmetic.UnicriticalOrbitBounds

/-!
# The unique quadratic critical-orbit boundary parameter

A bounded quadratic critical orbit reaches modulus two only for `c = -2`.
Every other bounded critical orbit stays strictly inside the disk, and the
shifted parameter `c+1` always has modulus strictly below two. These bounds
apply to all bounded orbits, without arithmetic or preperiodicity assumptions.
-/

noncomputable section
open Set Bornology
namespace Bottcher.Arithmetic

private theorem quadratic_parameter_on_boundary (c : ℂ) (hc : ‖c‖ = 2)
    (hnext : ‖c ^ 2 + c‖ ≤ 2) : c = -2 := by
  rw [show c ^ 2 + c = c * (c + 1) by ring, norm_mul, hc] at hnext
  have hplus : ‖c + 1‖ ^ 2 ≤ 1 := by
    nlinarith only [hnext, norm_nonneg (c + 1)]
  have hsq : c.re ^ 2 + c.im ^ 2 = 4 := by
    have h : ‖c‖ ^ 2 = 4 := by rw [hc]; norm_num
    simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← pow_two] using h
  have hplus' : (c.re + 1) ^ 2 + c.im ^ 2 ≤ 1 := by
    simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, add_zero, ← pow_two] using hplus
  have hre2 : (c.re + 2) ^ 2 = 0 := by
    nlinarith only [hsq, hplus', sq_nonneg c.im, sq_nonneg (c.re + 2)]
  have hre : c.re = -2 := by have h := sq_eq_zero_iff.mp hre2; linarith only [h]
  have him : c.im = 0 := by
    have h : c.im ^ 2 = 0 := by nlinarith only [hsq, hre]
    exact sq_eq_zero_iff.mp h
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- The sole exception to the strict radius-two bound is the endpoint parameter. -/
theorem quadraticOrbit_unbounded_or_endpoint_or_strict (c : ℂ) :
    ¬ IsBounded (range (criticalOrbit 0 c)) ∨ c = -2 ∨
      ∀ n, ‖criticalOrbit 0 c n‖ < 2 := by
  by_cases hb : IsBounded (range (criticalOrbit 0 c))
  · right
    by_cases hc : c = -2
    · exact Or.inl hc
    · right
      have h : ∀ n, ‖criticalOrbit 0 c n‖ ≤ 2 := by
        simpa only [Nat.zero_add, pow_one] using (bounded_criticalOrbit_iff 0 c).mp hb
      have hc' : ‖c‖ < 2 := by
        have h1 : ‖c‖ ≤ 2 := by simpa only [criticalOrbit_one] using h 1
        apply lt_of_le_of_ne h1
        intro he
        apply hc
        apply quadratic_parameter_on_boundary c he
        simpa only [criticalOrbit_succ, criticalOrbit_zero, Nat.zero_add,
          zero_pow (by omega : 2 ≠ 0), zero_add] using h 2
      intro n
      apply lt_of_le_of_ne (h n)
      intro he
      have hr := norm_sub_norm_le (criticalOrbit 0 c n ^ 2) (-c)
      simp only [norm_neg, sub_neg_eq_add, norm_pow, he] at hr
      have hn := h (n + 1)
      rw [criticalOrbit_succ] at hn
      norm_num only [Nat.zero_add] at hn
      linarith only [hr, hn, hc']
  · exact Or.inl hb

/-- The shifted quadratic parameter lies strictly inside the radius-two disk whenever its orbit is bounded. -/
theorem quadraticOrbit_unbounded_or_shift_bound (c : ℂ) :
    ¬ IsBounded (range (criticalOrbit 0 c)) ∨ ‖c + 1‖ < 2 := by
  rcases quadraticOrbit_unbounded_or_endpoint_or_strict c with hb | hc | h
  · exact Or.inl hb
  · right
    subst c
    norm_num
  · right
    by_cases hc : ‖c‖ < 1
    · have ht := norm_add_le c 1
      norm_num only [norm_one] at ht
      linarith only [ht, hc]
    · have h2 := h 2
      simp only [criticalOrbit_succ, criticalOrbit_zero,
        zero_pow (by omega : 2 ≠ 0), zero_add] at h2
      rw [show c ^ 2 + c = c * (c + 1) by ring, norm_mul] at h2
      nlinarith only [h2, not_lt.mp hc, norm_nonneg (c + 1)]

/-- The endpoint critical orbit is `0, -2, 2, 2, ...`. -/
theorem quadraticOrbit_endpoint_tail (n : ℕ) : criticalOrbit 0 (-2 : ℂ) (n + 2) = 2 := by
  induction n with
  | zero => norm_num [criticalOrbit_succ, criticalOrbit_zero]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, criticalOrbit_succ, ih]
    norm_num

/-- Boundary contact within a bounded quadratic critical orbit characterizes the endpoint. -/
theorem quadraticOrbit_bounded_boundary_iff (c : ℂ) :
    (IsBounded (range (criticalOrbit 0 c)) ∧ ∃ n, ‖criticalOrbit 0 c n‖ = 2) ↔ c = -2 := by
  constructor
  · rintro ⟨hb, n, hn⟩
    rcases quadraticOrbit_unbounded_or_endpoint_or_strict c with h | h | h
    · exact (h hb).elim
    · exact h
    · exact (ne_of_lt (h n) hn).elim
  · rintro rfl
    constructor
    · apply (bounded_criticalOrbit_iff 0 (-2)).mpr
      intro n
      rcases n with _ | n
      · simp only [criticalOrbit_zero, norm_zero, Nat.zero_add, pow_one, zero_le_two]
      · rcases n with _ | n
        · norm_num [criticalOrbit_one]
        · rw [show n + 1 + 1 = n + 2 by omega, quadraticOrbit_endpoint_tail]
          norm_num
    · refine ⟨1, ?_⟩
      norm_num [criticalOrbit_one]

end Bottcher.Arithmetic

