import Mathlib

/-!
# The Euclidean cone signatures

A parabolic (zero-curvature) orbifold structure on the sphere is a finite list of cone orders
`ν ≥ 2` together with a number `c` of cusps satisfying

`c + ∑ (1 - 1/ν) = 2`.

There are exactly six solutions: `(∞, ∞)`, `(2, 2, ∞)`, `(2, 2, 2, 2)`, `(2, 3, 6)`, `(2, 4, 4)`
and `(3, 3, 3)`.

The proof is elementary: each cone contributes at least `1/2` and less than `1`, which bounds the
number of cones by `4 - 2c`, and the remaining short cases are finite arithmetic.  The only
substantive step is the classification of the triples with `1/a + 1/b + 1/c = 1`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Euclidean cone triples.**  The only weakly increasing triples of integers at least `2`
with reciprocal sum `1` are `(2,3,6)`, `(2,4,4)` and `(3,3,3)`. -/
theorem euclidean_cone_triple {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (heq : (1 : ℚ) / a + 1 / b + 1 / c = 1) :
    (a = 2 ∧ b = 3 ∧ c = 6) ∨ (a = 2 ∧ b = 4 ∧ c = 4) ∨ (a = 3 ∧ b = 3 ∧ c = 3) := by
  have hb : 2 ≤ b := le_trans ha hab
  have hc : 2 ≤ c := le_trans hb hbc
  have ha0 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) ha
  have hb0 : (0 : ℚ) < (b : ℚ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hb
  have hc0 : (0 : ℚ) < (c : ℚ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hc
  have hab' : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  have hbc' : (b : ℚ) ≤ (c : ℚ) := by exact_mod_cast hbc
  have h1 : (1 : ℚ) / (b : ℚ) ≤ 1 / (a : ℚ) := by
    rw [div_le_div_iff hb0 ha0]; linarith
  have h2 : (1 : ℚ) / (c : ℚ) ≤ 1 / (b : ℚ) := by
    rw [div_le_div_iff hc0 hb0]; linarith
  have hpc : (0 : ℚ) < 1 / (c : ℚ) := by positivity
  have hpb : (0 : ℚ) < 1 / (b : ℚ) := by positivity
  have hale : a ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have h4 : (4 : ℚ) ≤ (a : ℚ) := by exact_mod_cast hcon
    have hle : (1 : ℚ) / (a : ℚ) ≤ 1 / 4 := by
      rw [div_le_div_iff ha0 (by norm_num)]; linarith
    linarith
  interval_cases a
  · -- `a = 2`
    have hble : b ≤ 4 := by
      by_contra hcon
      push_neg at hcon
      have h5 : (5 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hcon
      have hle : (1 : ℚ) / (b : ℚ) ≤ 1 / 5 := by
        rw [div_le_div_iff hb0 (by norm_num)]; linarith
      have hlec : (1 : ℚ) / (c : ℚ) ≤ 1 / 5 := le_trans h2 hle
      norm_num at heq
      linarith
    have hbge : 3 ≤ b := by
      by_contra hcon
      push_neg at hcon
      have hb2 : b = 2 := by omega
      subst hb2
      norm_num at heq
      have : (1 : ℚ) / (c : ℚ) = 0 := by linarith
      simp only [div_eq_zero_iff, one_ne_zero, false_or] at this
      exact absurd this (ne_of_gt hc0)
    interval_cases b
    · -- `b = 3`
      left
      refine ⟨rfl, rfl, ?_⟩
      have hcq : (c : ℚ) = 6 := by
        have h : (1 : ℚ) / (c : ℚ) = 1 / 6 := by norm_num at heq ⊢; linarith
        field_simp at h
        linarith
      exact_mod_cast hcq
    · -- `b = 4`
      right; left
      refine ⟨rfl, rfl, ?_⟩
      have hcq : (c : ℚ) = 4 := by
        have h : (1 : ℚ) / (c : ℚ) = 1 / 4 := by norm_num at heq ⊢; linarith
        field_simp at h
        linarith
      exact_mod_cast hcq
  · -- `a = 3`
    have hble : b ≤ 3 := by
      by_contra hcon
      push_neg at hcon
      have h4 : (4 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hcon
      have hle : (1 : ℚ) / (b : ℚ) ≤ 1 / 4 := by
        rw [div_le_div_iff hb0 (by norm_num)]; linarith
      have hlec : (1 : ℚ) / (c : ℚ) ≤ 1 / 4 := le_trans h2 hle
      norm_num at heq
      linarith
    have hb3 : b = 3 := le_antisymm hble hb
    subst hb3
    right; right
    refine ⟨rfl, rfl, ?_⟩
    have hcq : (c : ℚ) = 3 := by
      have h : (1 : ℚ) / (c : ℚ) = 1 / 3 := by norm_num at heq ⊢; linarith
      field_simp at h
      linarith
    exact_mod_cast hcq

end GaloisForLFunctions.HTGeometry
