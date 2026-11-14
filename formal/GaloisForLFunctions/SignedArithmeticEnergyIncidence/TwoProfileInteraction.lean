import GaloisForLFunctions.SignedArithmeticEnergyIncidence.SignedIncidenceForms
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!+# Two-profile interaction and normalized negative directions

The polarization of an arbitrary incidence matrix depends only on its symmetric
part. Choosing the relative sign of two profiles gives the exact energy deficit
`E(f) + E(g) - 2 |B(f,g)|`. Normalization by the square root of the absolute
energy extends this identity to positive, negative, and zero diagonal energies.
This is the two-component mechanism of Corollary 5 of arXiv:2611.10726.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

variable {ι : Type*} [Fintype ι]

/-- Symmetric polarization, including matrices whose antisymmetric part is nonzero. -/
def incidenceCross (c : ι → ι → ℝ) (f g : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, c i j * (f i * g j + g i * f j)) / 2

theorem incidenceCross_comm (c : ι → ι → ℝ) (f g : ι → ℝ) :
    incidenceCross c f g = incidenceCross c g f := by
  unfold incidenceCross
  simp only [add_comm]

/-- Every two-profile restriction is an explicitly known binary quadratic form. -/
theorem incidenceEnergy_two_profiles (c : ι → ι → ℝ) (f g : ι → ℝ) (a b : ℝ) :
    incidenceEnergy c (fun i => a * f i + b * g i) =
      a ^ 2 * incidenceEnergy c f + 2 * a * b * incidenceCross c f g +
        b ^ 2 * incidenceEnergy c g := by
  unfold incidenceEnergy incidenceCross
  have hp (i j : ι) : c i j * (a * f i + b * g i) * (a * f j + b * g j) =
      a ^ 2 * (c i j * f i * f j) +
        a * b * (c i j * (f i * g j + g i * f j)) +
          b ^ 2 * (c i j * g i * g j) := by ring
  simp only [hp, sum_add_distrib, ← mul_sum]
  ring

/-- The lower of the two relative signs has an exact, attained energy. -/
theorem incidenceEnergy_exists_sign_min (c : ι → ι → ℝ) (f g : ι → ℝ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      incidenceEnergy c (fun i => f i - ε * g i) =
        incidenceEnergy c f + incidenceEnergy c g - 2 * |incidenceCross c f g| := by
  by_cases h : 0 ≤ incidenceCross c f g
  · refine ⟨1, Or.inl rfl, ?_⟩
    have he := incidenceEnergy_two_profiles c f g 1 (-1)
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, one_pow, neg_one_sq] at he
    simp only [one_mul, he, abs_of_nonneg h]
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have he := incidenceEnergy_two_profiles c f g 1 1
    simp only [one_mul, one_pow] at he
    simp only [neg_one_mul, sub_neg_eq_add, he, abs_of_neg (lt_of_not_ge h)]
    ring

/-- A two-sign witness is negative exactly when its interaction exceeds its total diagonal budget. -/
theorem incidenceEnergy_two_sign_negative_iff (c : ι → ι → ℝ) (f g : ι → ℝ) :
    (∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      incidenceEnergy c (fun i => f i - ε * g i) < 0) ↔
      incidenceEnergy c f + incidenceEnergy c g < 2 * |incidenceCross c f g| := by
  constructor
  · rintro ⟨ε, rfl | rfl, h⟩
    · have he := incidenceEnergy_two_profiles c f g 1 (-1)
      simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, one_pow, neg_one_sq] at he h
      rw [he] at h
      linarith only [h, le_abs_self (incidenceCross c f g)]
    · have he := incidenceEnergy_two_profiles c f g 1 1
      simp only [one_mul, one_pow] at he
      simp only [neg_one_mul, sub_neg_eq_add, he] at h
      linarith only [h, neg_le_abs (incidenceCross c f g)]
  · intro h
    obtain ⟨ε, hε, he⟩ := incidenceEnergy_exists_sign_min c f g
    exact ⟨ε, hε, he.trans_lt (by linarith only [h])⟩

/-- Absolute-energy normalization is defined even on the radical. -/
def incidenceNormalize (c : ι → ι → ℝ) (f : ι → ℝ) : ι → ℝ :=
  fun i => f i / Real.sqrt |incidenceEnergy c f|

theorem incidenceEnergy_normalize (c : ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy c (incidenceNormalize c f) =
      incidenceEnergy c f / |incidenceEnergy c f| := by
  calc
    _ = incidenceEnergy c f / (Real.sqrt |incidenceEnergy c f|) ^ 2 := by
      have hp (i j : ι) :
          c i j * (f i / Real.sqrt |incidenceEnergy c f|) *
            (f j / Real.sqrt |incidenceEnergy c f|) =
          (c i j * f i * f j) / (Real.sqrt |incidenceEnergy c f|) ^ 2 := by ring
      change (∑ i, ∑ j, c i j * (f i / Real.sqrt |incidenceEnergy c f|) *
        (f j / Real.sqrt |incidenceEnergy c f|)) = _
      simp only [hp, ← sum_div]
      rfl
    _ = _ := by rw [Real.sq_sqrt (abs_nonneg _)]

theorem incidenceCross_normalize (c : ι → ι → ℝ) (f g : ι → ℝ) :
    incidenceCross c (incidenceNormalize c f) (incidenceNormalize c g) =
      incidenceCross c f g /
        (Real.sqrt |incidenceEnergy c f| * Real.sqrt |incidenceEnergy c g|) := by
  have hp (i j : ι) :
      c i j * (incidenceNormalize c f i * incidenceNormalize c g j +
        incidenceNormalize c g i * incidenceNormalize c f j) =
      (c i j * (f i * g j + g i * f j)) /
        (Real.sqrt |incidenceEnergy c f| * Real.sqrt |incidenceEnergy c g|) := by
    unfold incidenceNormalize
    ring
  unfold incidenceCross
  simp only [hp, ← sum_div]
  ring

/-- Exact normalized deficit, valid without positivity or nonvanishing assumptions. -/
theorem incidenceEnergy_normalized_sign_min (c : ι → ι → ℝ) (f g : ι → ℝ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      incidenceEnergy c (fun i => incidenceNormalize c f i - ε * incidenceNormalize c g i) =
        incidenceEnergy c f / |incidenceEnergy c f| +
          incidenceEnergy c g / |incidenceEnergy c g| -
            2 * (|incidenceCross c f g| /
              (Real.sqrt |incidenceEnergy c f| * Real.sqrt |incidenceEnergy c g|)) := by
  obtain ⟨ε, hε, he⟩ := incidenceEnergy_exists_sign_min c
    (incidenceNormalize c f) (incidenceNormalize c g)
  refine ⟨ε, hε, ?_⟩
  simpa only [incidenceEnergy_normalize, incidenceCross_normalize, abs_div,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using he

/-- The normalized two-sign test has an exact threshold even for indefinite diagonal data. -/
theorem incidenceEnergy_normalized_sign_negative_iff (c : ι → ι → ℝ) (f g : ι → ℝ) :
    (∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      incidenceEnergy c (fun i => incidenceNormalize c f i - ε * incidenceNormalize c g i) < 0) ↔
      incidenceEnergy c f / |incidenceEnergy c f| +
        incidenceEnergy c g / |incidenceEnergy c g| <
          2 * (|incidenceCross c f g| /
            (Real.sqrt |incidenceEnergy c f| * Real.sqrt |incidenceEnergy c g|)) := by
  simpa only [incidenceEnergy_normalize, incidenceCross_normalize, abs_div,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using
      incidenceEnergy_two_sign_negative_iff c (incidenceNormalize c f) (incidenceNormalize c g)

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
