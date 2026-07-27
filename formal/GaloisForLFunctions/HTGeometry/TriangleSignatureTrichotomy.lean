import GaloisForLFunctions.HTGeometry.HurwitzTriangleSumBound
import GaloisForLFunctions.HTGeometry.ParabolicSignatureClassification

/-!
# The trichotomy of triangle signatures

The corpus has the hyperbolic half of the reciprocal-sum trichotomy — the Hurwitz `41/42` bound and
its unique minimizer `(2,3,7)` — and now the parabolic half.  The spherical half is the same
argument run once more, and the three together classify every ordered triple of cone orders.

* **`spherical_triple_classification`** — `1/a + 1/b + 1/c > 1` for `2 ≤ a ≤ b ≤ c` holds exactly for
  the dihedral family `(2,2,c)` and the three Platonic triples `(2,3,3)`, `(2,3,4)`, `(2,3,5)`;
* **`triangle_signature_trichotomy`** — every ordered triple is spherical from that list, parabolic
  from the six-signature list, or hyperbolic with reciprocal sum at most `41/42`.
-/

namespace GaloisForLFunctions.HTGeometry

private theorem cast_lt_of_one_div_lt {x : ℕ} {n : ℚ} (hn : 0 < n) (h : 1 / n < 1 / (x : ℚ)) :
    (x : ℚ) < n := by
  by_contra hcon
  push Not at hcon
  have : 1 / (x : ℚ) ≤ 1 / n := one_div_le_one_div_of_le hn hcon
  linarith

/-- **The spherical triples.**  For weakly increasing cone orders at least two, a reciprocal sum
greater than one occurs exactly for the dihedral family and the three Platonic triples. -/
theorem spherical_triple_classification {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hsum : 1 < 1 / (a : ℚ) + 1 / b + 1 / c) :
    (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3 ∧ c = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 4) ∨
      (a = 2 ∧ b = 3 ∧ c = 5) := by
  have hb : 2 ≤ b := le_trans ha hab
  have hc : 2 ≤ c := le_trans hb hbc
  have ha0 : (0 : ℚ) < (a : ℚ) := by
    have : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
    linarith
  have hb0 : (0 : ℚ) < (b : ℚ) := by
    have : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  have hba : 1 / (b : ℚ) ≤ 1 / a := one_div_le_one_div_of_le ha0 (by exact_mod_cast hab)
  have hcb : 1 / (c : ℚ) ≤ 1 / b := one_div_le_one_div_of_le hb0 (by exact_mod_cast hbc)
  have ha2 : a = 2 := by
    have hlt : 1 / (3 : ℚ) < 1 / (a : ℚ) := by linarith
    have : (a : ℚ) < 3 := cast_lt_of_one_div_lt (by norm_num) hlt
    have : a < 3 := by exact_mod_cast this
    omega
  subst ha2
  have hpair : 1 / (2 : ℚ) < 1 / (b : ℚ) + 1 / c := by
    have h2 : (1 : ℚ) / ((2 : ℕ) : ℚ) = 1 / 2 := by norm_num
    rw [h2] at hsum
    linarith
  have hble : b < 4 := by
    have hlt : 1 / (4 : ℚ) < 1 / (b : ℚ) := by linarith
    have : (b : ℚ) < 4 := cast_lt_of_one_div_lt (by norm_num) hlt
    exact_mod_cast this
  interval_cases b
  · left; exact ⟨rfl, rfl⟩
  · have hcgt : 1 / (6 : ℚ) < 1 / (c : ℚ) := by
      have h3 : (1 : ℚ) / ((3 : ℕ) : ℚ) = 1 / 3 := by norm_num
      rw [h3] at hpair
      linarith
    have : (c : ℚ) < 6 := cast_lt_of_one_div_lt (by norm_num) hcgt
    have hclt : c < 6 := by exact_mod_cast this
    have hc3 : 3 ≤ c := hbc
    interval_cases c
    · right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; right; exact ⟨rfl, rfl, rfl⟩

/-- **Trichotomy of triangle signatures.**  Every weakly increasing triple of cone orders at least
two is spherical with one of the four listed shapes, parabolic with one of the three listed shapes,
or hyperbolic — and in the hyperbolic case the reciprocal sum is at most `41/42`. -/
theorem triangle_signature_trichotomy {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (((a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3 ∧ c = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 4) ∨
        (a = 2 ∧ b = 3 ∧ c = 5)) ∧ 1 < 1 / (a : ℚ) + 1 / b + 1 / c) ∨
      (((a = 2 ∧ b = 3 ∧ c = 6) ∨ (a = 2 ∧ b = 4 ∧ c = 4) ∨ (a = 3 ∧ b = 3 ∧ c = 3)) ∧
        1 / (a : ℚ) + 1 / b + 1 / c = 1) ∨
      (1 / (a : ℚ) + 1 / b + 1 / c ≤ 41 / 42) := by
  rcases lt_trichotomy (1 / (a : ℚ) + 1 / b + 1 / c) 1 with h | h | h
  · exact Or.inr (Or.inr (hurwitz_triple_sum_le (by omega) hab hbc h))
  · refine Or.inr (Or.inl ⟨?_, h⟩)
    have h' : ((a : ℚ))⁻¹ + ((b : ℚ))⁻¹ + ((c : ℚ))⁻¹ = 1 := by simpa [one_div] using h
    exact parabolic_triple_classification ha hab hbc h'
  · exact Or.inl ⟨spherical_triple_classification ha hab hbc h, h⟩

end GaloisForLFunctions.HTGeometry
