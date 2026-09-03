import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateReflection
import GaloisForLFunctions.RHTower.Sieve.MaynardBoxFactorization

/-!
# Reflection of literal Heath--Brown cores

Every factor in a literal Heath--Brown box has real arithmetic coefficients.  Hence the full
core and signed box term commute with complex conjugation, and their norms at an ordinate equal
their norms at the corresponding positive ordinate.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- A literal unsigned Heath--Brown core commutes with complex conjugation. -/
theorem conj_heathBrownDyadicCoreProduct
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) :
    (starRingEnd ℂ) (heathBrownDyadicCoreProduct L X k m a b q s) =
      heathBrownDyadicCoreProduct L X k m a b q ((starRingEnd ℂ) s) := by
  simp only [heathBrownDyadicCoreProduct, map_mul, map_prod,
    conj_LSeries_complexCoeff]

/-- A literal signed Heath--Brown box term commutes with complex conjugation. -/
theorem conj_heathBrownBoxTerm
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) (s : ℂ) :
    (starRingEnd ℂ) (heathBrownBoxTerm L X k box s) =
      heathBrownBoxTerm L X k box ((starRingEnd ℂ) s) := by
  simp only [heathBrownBoxTerm, heathBrownDyadicTermProduct_eq_scalar_mul_core,
    map_mul, conj_heathBrownDyadicCoreProduct]
  simp

/-- The norm of a literal Heath--Brown core is unchanged by reflecting its ordinate. -/
theorem norm_heathBrownDyadicCoreProduct_line_neg
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (sigma t : ℝ) :
    ‖heathBrownDyadicCoreProduct L X k m a b q
        ((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ =
      ‖heathBrownDyadicCoreProduct L X k m a b q
        ((sigma : ℂ) + (t : ℝ) * Complex.I)‖ := by
  have h := congrArg norm
    (conj_heathBrownDyadicCoreProduct L X k m a b q
      ((sigma : ℂ) + (t : ℝ) * Complex.I))
  have hs : (starRingEnd ℂ) ((sigma : ℂ) + (t : ℝ) * Complex.I) =
      (sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [Complex.norm_conj, hs] at h
  exact h.symm

/-- A core may be reflected to the positive ordinate `|t|` without changing its norm. -/
theorem norm_heathBrownDyadicCoreProduct_line_abs
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (sigma t : ℝ) :
    ‖heathBrownDyadicCoreProduct L X k m a b q
        ((sigma : ℂ) + (|t| : ℝ) * Complex.I)‖ =
      ‖heathBrownDyadicCoreProduct L X k m a b q
        ((sigma : ℂ) + (t : ℝ) * Complex.I)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    exact norm_heathBrownDyadicCoreProduct_line_neg L X k m a b q sigma t

/-- A signed box term may likewise be reflected to the positive ordinate `|t|`. -/
theorem norm_heathBrownBoxTerm_line_abs
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) (sigma t : ℝ) :
    ‖heathBrownBoxTerm L X k box
        ((sigma : ℂ) + (|t| : ℝ) * Complex.I)‖ =
      ‖heathBrownBoxTerm L X k box
        ((sigma : ℂ) + (t : ℝ) * Complex.I)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    have h := congrArg norm
      (conj_heathBrownBoxTerm box ((sigma : ℂ) + (t : ℝ) * Complex.I))
    have hs : (starRingEnd ℂ) ((sigma : ℂ) + (t : ℝ) * Complex.I) =
        (sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [Complex.norm_conj, hs] at h
    exact h.symm

end RHTower.Sieve
