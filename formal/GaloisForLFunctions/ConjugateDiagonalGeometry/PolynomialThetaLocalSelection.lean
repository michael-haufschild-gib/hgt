import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialThetaLocalMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceLocalTrace

/-!
# Uniform arithmetic localization of the actual divisor

One prescribed finite theta source brackets all shrinking-disc counts in a
growing height window. Integer multiplicity then turns a fixed positive
threshold into a two-radius detector, without isolating any individual zero.
-/

open Complex Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower

/-- Uniform arithmetic inner and outer count bounds, with the source stage fixed before the center. -/
theorem exists_polynomialThetaLocalReading_mass_sandwich :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ, 1 ≤ n → ∀ c : ℂ,
      (0 ≤ c.re ∧ c.re ≤ 1) → |c.im| ≤ (n : ℝ) / 2 →
      (xiBallOrderSum c (polynomialSourceLocalRadius n) : ℝ) ≤
          polynomialThetaLocalReading n c + E / ((n : ℝ) + 1) ^ 2 ∧
        polynomialThetaLocalReading n c - E / ((n : ℝ) + 1) ^ 2 ≤
          (xiBallOrderSum c (2 * polynomialSourceLocalRadius n) : ℝ) := by
  obtain ⟨E, hE, hb⟩ := exists_polynomialThetaLocalReading_error_bound
  refine ⟨E, hE, fun n hn c hc hcy => ?_⟩
  have he := abs_le.mp (hb n hn c hc hcy)
  have hm := sourceLocalTrace_mass_sandwich c (polynomialSourceLocalRadius_pos n)
  constructor <;> linarith only [he.1, he.2, hm.1, hm.2]

/-- One finite-source threshold resolves every shrinking neighborhood in the full center window. -/
theorem polynomialThetaLocalReading_uniform_zero_detector :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : ℂ,
      (0 ≤ c.re ∧ c.re ≤ 1) → |c.im| ≤ (n : ℝ) / 2 →
      ((∃ z ∈ closedBall c (polynomialSourceLocalRadius n), xi z = 0) →
        (1 / 2 : ℝ) < polynomialThetaLocalReading n c) ∧
      ((1 / 2 : ℝ) < polynomialThetaLocalReading n c →
        ∃ z ∈ closedBall c (2 * polynomialSourceLocalRadius n), xi z = 0) := by
  obtain ⟨E, hE, hb⟩ := exists_polynomialThetaLocalReading_error_bound
  refine ⟨max 1 ⌈4 * E⌉₊, fun n hn c hc hcy => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnE : 4 * E ≤ (n : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈4 * E⌉₊).trans hn)
  have hsmall : E / ((n : ℝ) + 1) ^ 2 < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    nlinarith only [hnE, hn0, sq_nonneg (n : ℝ)]
  have he := abs_le.mp (hb n hn1 c hc hcy)
  constructor
  · rintro ⟨z, hz, hzero⟩
    have htrace := one_le_sourceLocalTrace_of_zero c (polynomialSourceLocalRadius_pos n) hz hzero
    linarith only [he.1, hsmall, htrace]
  · intro hreading
    apply exists_zero_of_sourceLocalTrace_pos c (polynomialSourceLocalRadius_pos n)
    linarith only [he.2, hsmall, hreading]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_polynomialThetaLocalReading_mass_sandwich
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.polynomialThetaLocalReading_uniform_zero_detector
