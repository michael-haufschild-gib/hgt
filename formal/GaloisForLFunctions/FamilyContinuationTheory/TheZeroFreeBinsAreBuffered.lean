import Mathlib

/-!
# The zero-free bins are buffered

For a row of the family let `M j` be the largest real part of its zeros up to the height `3 j T₁`,
with a floor `lo`. The numbers `M 1, …, M I` lie in `[lo, hi]`; if `(I − 1) e > hi − lo`, two
consecutive windows differ by at most `e` (`exists_small_increment`). Rounding `M i` down to the
grid `lo + e ℕ` gives the bin `a` of the row:

`a ≤ M i < a + e`  and  `M (i + 1) < a + 2e`  (`exists_buffered_bin`).

The zeros up to the height of the window `i` lie left of `a + e`, and the next larger window, the
buffer, has none right of `a + 2e`. With the floor `51/100`, the ceiling `1` and `I = ⌈1/e⌉ + 2`
this is the choice of the bin in the zero detector (`exists_detector_bin`).
-/

namespace GaloisForLFunctions.FamilyContinuationTheory

/-- Among `I` numbers in `[lo, hi]` with `(I − 1) e > hi − lo`, two consecutive ones differ by at
most `e`. -/
theorem exists_small_increment {I : ℕ} {e lo hi : ℝ} (hI1 : 1 ≤ I)
    (hI : hi - lo < ((I : ℝ) - 1) * e) {M : ℕ → ℝ} (hlo : ∀ j, lo ≤ M j)
    (hhi : ∀ j, M j ≤ hi) : ∃ i : ℕ, 1 ≤ i ∧ i < I ∧ M (i + 1) - M i ≤ e := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  -- every increment exceeds `e`, so `M (k + 1) ≥ M 1 + k e`
  have key : ∀ k : ℕ, k + 1 ≤ I → M 1 + k * e ≤ M (k + 1) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hcon (k + 1) (by omega) (by omega)
      push_cast
      linarith
  have h := key (I - 1) (by omega)
  have hcast : ((I - 1 : ℕ) : ℝ) = (I : ℝ) - 1 := by
    rw [Nat.cast_sub hI1]
    simp
  rw [hcast, Nat.sub_add_cancel hI1] at h
  linarith [hlo 1, hhi I]

/-- **The bin of a row.** There are a window `i < I` and a grid point `a = lo + e k` with
`a ≤ M i < a + e` and `M (i + 1) < a + 2e`. -/
theorem exists_buffered_bin {I : ℕ} {e lo hi : ℝ} (he : 0 < e) (hI1 : 1 ≤ I)
    (hI : hi - lo < ((I : ℝ) - 1) * e) {M : ℕ → ℝ} (hlo : ∀ j, lo ≤ M j)
    (hhi : ∀ j, M j ≤ hi) :
    ∃ i k : ℕ, 1 ≤ i ∧ i < I ∧ lo + e * k ≤ M i ∧ M i < lo + e * k + e ∧
      M (i + 1) < lo + e * k + 2 * e := by
  obtain ⟨i, hi1, hiI, hinc⟩ := exists_small_increment hI1 hI hlo hhi
  have hnn : 0 ≤ (M i - lo) / e := div_nonneg (by linarith [hlo i]) he.le
  have hcancel : e * ((M i - lo) / e) = M i - lo := by field_simp
  have hfloor : e * (⌊(M i - lo) / e⌋₊ : ℝ) ≤ M i - lo :=
    (mul_le_mul_of_nonneg_left (Nat.floor_le hnn) he.le).trans hcancel.le
  have hceil : M i - lo < e * (⌊(M i - lo) / e⌋₊ : ℝ) + e := by
    have h := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one ((M i - lo) / e)) he
    rw [hcancel] at h
    linarith
  exact ⟨i, ⌊(M i - lo) / e⌋₊, hi1, hiI, by linarith, by linarith, by linarith⟩

/-- **The bin in the zero detector**: floor `51/100`, ceiling `1`, `I = ⌈1/e⌉ + 2` windows. -/
theorem exists_detector_bin {e : ℝ} (he : 0 < e) {M : ℕ → ℝ} (hlo : ∀ j, 51 / 100 ≤ M j)
    (hhi : ∀ j, M j ≤ 1) :
    ∃ i k : ℕ, 1 ≤ i ∧ i < ⌈1 / e⌉₊ + 2 ∧ 51 / 100 + e * k ≤ M i ∧
      M i < 51 / 100 + e * k + e ∧ M (i + 1) < 51 / 100 + e * k + 2 * e := by
  refine exists_buffered_bin he (by omega) ?_ hlo hhi
  have h1 : 1 / e ≤ (⌈1 / e⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (1 : ℝ) ≤ (⌈1 / e⌉₊ : ℝ) * e := by
    have h3 := mul_le_mul_of_nonneg_right h1 he.le
    have h4 : 1 / e * e = 1 := by field_simp
    linarith
  push_cast
  nlinarith

end GaloisForLFunctions.FamilyContinuationTheory
