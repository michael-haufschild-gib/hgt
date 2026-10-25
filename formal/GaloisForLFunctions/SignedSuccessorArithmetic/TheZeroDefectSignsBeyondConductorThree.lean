import GaloisForLFunctions.SignedSuccessorArithmetic.TheShiftFloorsAreExact
import GaloisForLFunctions.SignedSuccessorArithmetic.TheTwoScaleDeficitIsQuantized

/-!
# The zero-defect signs beyond conductor three

A sign has zero doubling defect when no `n` has `f(n) = f(n+1)` and `f(2n) = f(2n+1)`; such signs
attain the one-third floor with equality in the two-scale identity at every scale. The
conductor-three twins have zero defect. This file settles the branch `f(2) = 1` and exhibits a
zero-defect sign outside conductor three.

* **The `f(2) = 1` branch is empty.** The forced values `f(3) = f(5) = −1`, `f(13) = 1` give
  `f(17) = −1` at the step `16 → 17`, and then `25 → 26` and `50 → 51` are both agreements:
  `f(25) = f(26) = 1` and `f(50) = f(51) = 1` (`zeroDefect_two_eq_neg_one`). Every zero-defect sign
  has `f(2) = −1`, and the rule becomes `f(n) = f(n+1) ⇒ f(2n+1) = f(n)`
  (`zeroDefect_odd_of_agree`).
* **A zero-defect sign of conductor two.** The twin `T(n) = (−1)^{v₂(n)}` has zero defect
  (`zeroDefect_twoTwin`) and differs from both conductor-three twins at `5`
  (`twoTwin_ne_chi3Twin`): the extremal signs of the one-third floor are not all twins of `χ₃`.
* **The branches at `3`.** `f(3) = −1` forces `f(5) = −1` (the conductor-three pattern), and
  `f(3) = 1` forces `f(7) = 1` (`zeroDefect_branches`); the value `f(5)` then separates `T` from
  the twin `χ₃` with `f(3) = 1`.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

variable (f : CMSign)

/-- Zero defect: an agreement at `n` forces a flip at `2n`. -/
theorem succSign_two_mul_of_zeroDefect (hf : ZeroDefect f) {n : ℕ} (hn : 0 < n)
    (hσ : succSign f n = 1) : succSign f (2 * n) = -1 := by
  have h := hf n hn
  refine (Int.units_eq_one_or _).resolve_left fun h' => ?_
  simp [agree, hσ, h'] at h

/-- **The `f(2) = 1` branch of zero defect is empty.** -/
theorem zeroDefect_two_eq_neg_one (hf : ZeroDefect f) : f 2 = -1 := by
  refine (Int.units_eq_one_or _).resolve_left fun h2 => ?_
  obtain ⟨f3, f5, -, -, f13⟩ := zeroDefect_of_two_eq_one f hf h2
  have m : ∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a * f b := fun a b ha hb => f.map_mul ha hb
  have f4 : f 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, m 2 2 (by norm_num) (by norm_num), h2,
    mul_one]
  have f8 : f 8 = 1 := by rw [show (8 : ℕ) = 2 * 4 from rfl, m 2 4 (by norm_num) (by norm_num), h2,
    f4, mul_one]
  have f16 : f 16 = 1 := by rw [show (16 : ℕ) = 2 * 8 from rfl, m 2 8 (by norm_num) (by norm_num),
    h2, f8, mul_one]
  have f9 : f 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, m 3 3 (by norm_num) (by norm_num), f3]; simp
  -- `σ(8) = 1`, so `σ(16) = −1`: `f(17) = −1`
  have f17 : f 17 = -1 := by
    have := succSign_two_mul_of_zeroDefect f hf (n := 8) (by norm_num) (by simp [succSign, f8, f9])
    simpa [succSign, f16] using this
  have f25 : f 25 = 1 := by
    rw [show (25 : ℕ) = 5 * 5 from rfl, m 5 5 (by norm_num) (by norm_num), f5]; simp
  have f26 : f 26 = 1 := by rw [show (26 : ℕ) = 2 * 13 from rfl, m 2 13 (by norm_num) (by norm_num),
    h2, f13, mul_one]
  have f50 : f 50 = 1 := by rw [show (50 : ℕ) = 2 * 25 from rfl, m 2 25 (by norm_num) (by norm_num),
    h2, f25, mul_one]
  have f51 : f 51 = 1 := by
    rw [show (51 : ℕ) = 3 * 17 from rfl, m 3 17 (by norm_num) (by norm_num), f3, f17]; simp
  -- `σ(25) = 1` forces `σ(50) = −1`, but `f(50) = f(51) = 1`
  have := succSign_two_mul_of_zeroDefect f hf (n := 25) (by norm_num) (by simp [succSign, f25, f26])
  simp [succSign, f50, f51] at this

/-- **The zero-defect rule at `f(2) = −1`.** An agreement at `n` copies `f(n)` to `2n+1`. -/
theorem zeroDefect_odd_of_agree (hf : ZeroDefect f) {n : ℕ} (hn : 0 < n) (ha : f n = f (n + 1)) :
    f (2 * n + 1) = f n := by
  have h2 := zeroDefect_two_eq_neg_one f hf
  have hσ : succSign f n = 1 := by rw [succSign, ha, Int.units_mul_self]
  have h := succSign_two_mul_of_zeroDefect f hf hn hσ
  rw [succSign, f.map_mul two_pos hn, h2] at h
  rcases Int.units_eq_one_or (f n) with e | e <;>
    rcases Int.units_eq_one_or (f (2 * n + 1)) with e' | e' <;> simp_all

/-- **A zero-defect sign of conductor two.** -/
theorem zeroDefect_twoTwin : ZeroDefect twoTwin := by
  intro n hn
  have := agreeAt_mul_agreeAt_two_mul_twoTwin odd_one n hn
  rwa [agreeAt_one] at this

theorem twoTwin_five : twoTwin 5 = 1 := twoTwin_of_odd (by norm_num)

/-- The conductor-two twin is not a conductor-three twin: they differ at `5`. -/
theorem twoTwin_ne_chi3Twin (ε : ℤˣ) : twoTwin 5 ≠ chi3Twin ε 5 := by
  rw [twoTwin_five, show (5 : ℕ) = 3 * 1 + 2 from rfl, chi3Twin_three_mul_add_two]
  exact (units_neg_one_ne_one).symm

/-- **The branches at `3`.** A zero-defect sign has `f(2) = −1`; then `f(3) = −1` forces
`f(5) = −1`, and `f(3) = 1` forces `f(7) = 1`. -/
theorem zeroDefect_branches (hf : ZeroDefect f) :
    f 2 = -1 ∧ (f 3 = -1 → f 5 = -1) ∧ (f 3 = 1 → f 7 = 1) := by
  have h2 := zeroDefect_two_eq_neg_one f hf
  refine ⟨h2, fun h3 => ?_, fun h3 => ?_⟩
  · have := zeroDefect_odd_of_agree f hf (n := 2) (by norm_num) (by rw [h2, h3])
    rwa [h2] at this
  · have f4 : f 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, f.map_mul (by norm_num) (by norm_num), h2]; simp
    have := zeroDefect_odd_of_agree f hf (n := 3) (by norm_num) (by rw [h3, f4])
    rwa [h3] at this

end GaloisForLFunctions.SignedSuccessorArithmetic
