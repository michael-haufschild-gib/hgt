/-
Doc 24 §3 (task #143): the corrected counting lemma's finite arithmetic.

The analytic/sign-variation input is the bound

  `Z_c(J^d_{Pg}) ≤ 2 + T`,

where `T` is the number of copy/flip crossings of the margin through `1` along the
ordered critical points.  This file formalizes the bookkeeping tail used in doc 24:
if `T ≤ 1`, then the evenness of non-real zeros improves `Z ≤ 3` to `Z ≤ 2`; with
Hurwitz visibility (`Z > 0`) the count is exactly one conjugate pair.
-/
import Mathlib

namespace RHTower

/-- Even natural counts cannot sit strictly between two and four. -/
theorem even_nat_le_two_of_le_three {Z : ℕ} (hZ : Z ≤ 3) (heven : Even Z) : Z ≤ 2 := by
  rcases heven with ⟨k, hk⟩
  subst hk
  omega

/-- Corrected counting bound when the margin has no copy/flip crossing. -/
theorem corrected_counting_bound_no_crossing {Z T : ℕ}
    (hbound : Z ≤ 2 + T) (hT : T = 0) : Z ≤ 2 := by
  subst T
  omega

/-- Corrected counting bound when the margin has at most one copy/flip crossing. -/
theorem corrected_counting_bound_at_most_one_crossing {Z T : ℕ}
    (hbound : Z ≤ 2 + T) (hT : T ≤ 1) (heven : Even Z) : Z ≤ 2 := by
  exact even_nat_le_two_of_le_three (le_trans hbound (by omega)) heven

/-- The doc 24 `T = 1` specialization: `Z ≤ 2 + 1`, plus evenness, gives `Z ≤ 2`. -/
theorem corrected_counting_bound_single_crossing {Z T : ℕ}
    (hbound : Z ≤ 2 + T) (hT : T = 1) (heven : Even Z) : Z ≤ 2 := by
  exact corrected_counting_bound_at_most_one_crossing hbound (by omega) heven

/-- Visibility plus evenness turns the bound `Z ≤ 2` into exactly one conjugate pair. -/
theorem even_count_eq_two_of_visible_and_le_two {Z : ℕ}
    (hvisible : 0 < Z) (heven : Even Z) (hZ : Z ≤ 2) : Z = 2 := by
  rcases heven with ⟨k, hk⟩
  subst hk
  omega

/-- Corrected counting lemma, no-crossing exact-pair form with Hurwitz visibility. -/
theorem corrected_counting_exact_pair_of_no_crossing {Z T : ℕ}
    (hvisible : 0 < Z) (heven : Even Z) (hbound : Z ≤ 2 + T) (hT : T = 0) : Z = 2 := by
  exact even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_no_crossing hbound hT)

/-- Corrected counting lemma, single-crossing exact-pair form with Hurwitz visibility. -/
theorem corrected_counting_exact_pair_of_single_crossing {Z T : ℕ}
    (hvisible : 0 < Z) (heven : Even Z) (hbound : Z ≤ 2 + T) (hT : T = 1) : Z = 2 := by
  exact even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_single_crossing hbound hT heven)

end RHTower
