import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfAnAbcTriple

/-!
# Real elliptic branch geometry and the Frey numerator

The square factor of the fiber over `1728` gives the sharp lower bound for the real
Legendre invariant. Homogenization gives an exact square remainder for the numerator
of a Frey--Legendre invariant, and applies to the elliptic shape of Brizard elastica.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

open GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The real Legendre quadratic is strictly positive. -/
theorem legendre_quadratic_pos (m : ℝ) : 0 < m ^ 2 - m + 1 := by
  nlinarith only [sq_nonneg (m - 1 / 2)]

/-- The difference from the elliptic value `1728` is an explicit square quotient. -/
theorem legendreJ_sub_1728 {m : ℝ} (h0 : m ≠ 0) (h1 : m ≠ 1) :
    legendreJ m - 1728 =
      64 * ((m + 1) * (m - 2) * (2 * m - 1)) ^ 2 / (m ^ 2 * (1 - m) ^ 2) := by
  rw [legendreJ]
  have h1' : 1 - m ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp
  ring

/-- Every nonsingular real Legendre curve has invariant at least `1728`. -/
theorem legendreJ_lower_bound {m : ℝ} (h0 : m ≠ 0) (h1 : m ≠ 1) :
    1728 ≤ legendreJ m := by
  have h := legendreJ_sub_1728 h0 h1
  have hnonneg : 0 ≤
      64 * ((m + 1) * (m - 2) * (2 * m - 1)) ^ 2 / (m ^ 2 * (1 - m) ^ 2) := by
    positivity
  linarith only [h, hnonneg]

/-- The minimum fiber consists exactly of the three real elliptic parameters. -/
theorem legendreJ_eq_1728_iff (m : ℝ) :
    legendreJ m = 1728 ↔ m = -1 ∨ m = 2 ∨ m = 1 / 2 := by
  by_cases h0 : m = 0
  · subst m
    norm_num [legendreJ]
  by_cases h1 : m = 1
  · subst m
    norm_num [legendreJ]
  constructor
  · intro h
    have he := legendreJ_sub_1728 h0 h1
    rw [h, sub_self] at he
    have hden : m ^ 2 * (1 - m) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 h0) (pow_ne_zero 2 (sub_ne_zero.mpr h1.symm))
    have hnum : ((m + 1) * (m - 2) * (2 * m - 1)) ^ 2 = 0 := by
      have hmul := (div_eq_zero_iff.mp he.symm).resolve_right hden
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    rcases mul_eq_zero.mp (sq_eq_zero_iff.mp hnum) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith only [h])
      · exact Or.inr (Or.inl (by linarith only [h]))
    · exact Or.inr (Or.inr (by linarith only [h]))
  · rintro (rfl | rfl | rfl) <;> norm_num [legendreJ]

/-- The totalized real invariant is either singular or belongs to the sharp range. -/
theorem legendreJ_range (m : ℝ) :
    (m = 0 ∨ m = 1) ∨ 1728 ≤ legendreJ m := by
  by_cases h0 : m = 0
  · exact Or.inl (Or.inl h0)
  by_cases h1 : m = 1
  · exact Or.inl (Or.inr h1)
  exact Or.inr (legendreJ_lower_bound h0 h1)

/-- Homogenizing the elliptic branch identity produces an exact square for every triple. -/
theorem abcInvariant_square_remainder {R : Type*} [CommRing R] (a b : R) :
    4 * (a ^ 2 + a * b + b ^ 2) ^ 3 - 27 * (a * b * (a + b)) ^ 2 =
      ((a - b) * (a + 2 * b) * (2 * a + b)) ^ 2 := by
  ring

/-- The homogeneous Frey numerator dominates its denominator with sharp constant `27/4`. -/
theorem abcInvariant_sharp_lower_bound (a b : ℝ) :
    27 * (a * b * (a + b)) ^ 2 ≤ 4 * (a ^ 2 + a * b + b ^ 2) ^ 3 := by
  have h := abcInvariant_square_remainder a b
  nlinarith only [h, sq_nonneg ((a - b) * (a + 2 * b) * (2 * a + b))]

/-- Brizard's parameter invariant has the same sharp real range as its Legendre modulus. -/
theorem parameterJ_range (P : Parameters) :
    (P.modulus = 0 ∨ P.modulus = 1) ∨ 1728 ≤ parameterJ P := by
  rw [parameterJ_eq_legendreJ]
  exact legendreJ_range P.modulus

/-- The square elliptic shape occurs at exactly the three real branch parameters. -/
theorem parameterJ_eq_1728_iff (P : Parameters) :
    parameterJ P = 1728 ↔ P.modulus = -1 ∨ P.modulus = 2 ∨ P.modulus = 1 / 2 := by
  rw [parameterJ_eq_legendreJ, legendreJ_eq_1728_iff]

end GaloisForLFunctions.KodairaParshinAbc
