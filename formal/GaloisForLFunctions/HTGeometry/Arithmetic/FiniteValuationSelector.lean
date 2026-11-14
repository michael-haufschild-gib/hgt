import GaloisForLFunctions.HTGeometry.Arithmetic.SquareDenominator
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationProducts
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationSums
import Mathlib.Tactic.Linarith

/-!
# Finite conjunctions selected by square denominators

Reciprocal factors `1/(1+R(D/Rᵏ)²)` are integral at every prime where `R`
has odd valuation. A failed precision test makes its factor highly divisible.
Multiplication combines tests, and summation combines possible witnesses.
If the final square-denominator test succeeds, some witness passes all tests.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

open Finset

/-- Weight of one candidate in a finite family of local tests. -/
def valuationSelectorWeight {J : Type*} (s : Finset J) (k : J → ℕ)
    (R : ℚ) (D : J → ℚ) : ℚ :=
  ∏ j ∈ s, (1 + R * (D j / R ^ k j) ^ 2)⁻¹

/-- Sum of the weights of all candidates. -/
def valuationSelectorSum {G J : Type*} (g : Finset G) (s : Finset J)
    (k : J → ℕ) (R : ℚ) (D : G → J → ℚ) : ℚ :=
  ∑ a ∈ g, valuationSelectorWeight s k R (D a)

variable {p : ℕ} [Fact p.Prime]

theorem valuationSelectorWeight_ne_zero {J : Type*} (s : Finset J) (k : J → ℕ)
    {R : ℚ} (hR : ¬ Even (padicValRat p R)) (D : J → ℚ) :
    valuationSelectorWeight s k R D ≠ 0 := by
  exact prod_ne_zero_iff.mpr (fun j _ => inv_ne_zero (odd_factor_ne_zero hR _))

theorem valuationSelectorWeight_integral {J : Type*} (s : Finset J) (k : J → ℕ)
    {R : ℚ} (hR : ¬ Even (padicValRat p R)) (D : J → ℚ) :
    0 ≤ padicValRat p (valuationSelectorWeight s k R D) := by
  rw [valuationSelectorWeight, val_finset_prod s _
    (fun j _ => inv_ne_zero (odd_factor_ne_zero hR _))]
  exact sum_nonneg (fun j _ => odd_factor_inv_integral hR _)

/-- A failed test at positive precision forces the reciprocal factor to
have valuation at least that of the selector parameter. -/
theorem failed_selector_factor_high {R D : ℚ} {k : ℕ}
    (hR : ¬ Even (padicValRat p R)) (hpos : 0 < padicValRat p R)
    (hk : 1 ≤ k) (hD : D ≠ 0) (hfail : padicValRat p D < k) :
    padicValRat p R ≤ padicValRat p (1 + R * (D / R ^ k) ^ 2)⁻¹ := by
  have hR0 : R ≠ 0 := by
    intro h
    exact hR (by simp [h])
  rw [padicValRat.inv, odd_factor_val hR (div_ne_zero hD (pow_ne_zero k hR0)),
    padicValRat.div hD (pow_ne_zero k hR0), padicValRat.pow]
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hprod := mul_nonneg (sub_nonneg.mpr hk')
    (sub_nonneg.mpr (show 1 ≤ padicValRat p R by omega))
  have hbound : padicValRat p R +
      2 * (padicValRat p D - (k : ℤ) * padicValRat p R) ≤ -padicValRat p R := by
    nlinarith only [hprod, hfail]
  have hmin := (min_le_right 0 _).trans hbound
  omega

/-- One failed test makes the whole candidate weight highly divisible. -/
theorem valuationSelectorWeight_high_of_failure {J : Type*} (s : Finset J) (k : J → ℕ)
    {R : ℚ} (hR : ¬ Even (padicValRat p R)) (hpos : 0 < padicValRat p R)
    (D : J → ℚ) {j : J} (hj : j ∈ s) (hk : 1 ≤ k j)
    (hD : D j ≠ 0) (hfail : padicValRat p (D j) < k j) :
    padicValRat p R ≤ padicValRat p (valuationSelectorWeight s k R D) := by
  rw [valuationSelectorWeight, val_finset_prod s _
    (fun i _ => inv_ne_zero (odd_factor_ne_zero hR _))]
  exact (failed_selector_factor_high hR hpos hk hD hfail).trans
    (single_le_sum (fun i _ => odd_factor_inv_integral hR _) hj)

/-- Soundness of the finite selector: a successful square-denominator test
forces a candidate satisfying every requested local precision. -/
theorem finiteValuationSelector_sound {G J : Type*} (g : Finset G) (s : Finset J)
    (k : J → ℕ) (hk : ∀ j ∈ s, 1 ≤ k j) {R : ℚ} (D : G → J → ℚ)
    (hR : ¬ Even (padicValRat p R))
    (hΘ : valuationSelectorSum g s k R D ≠ 0)
    (hpass : SquareDenominator (R / valuationSelectorSum g s k R D ^ 2)) :
    0 < padicValRat p R ∧
      ∃ a ∈ g, ∀ j ∈ s, D a j = 0 ∨ (k j : ℤ) ≤ padicValRat p (D a j) := by
  have hR0 : R ≠ 0 := by
    intro h
    exact hR (by simp [h])
  have hΘval : 0 ≤ padicValRat p (valuationSelectorSum g s k R D) :=
    val_finset_sum_nonneg g _ (fun a _ => valuationSelectorWeight_integral s k hR (D a))
  have hB := (squareDenominator_iff _).mp hpass p (Fact.out : p.Prime)
  rw [padicValRat.div hR0 (pow_ne_zero 2 hΘ), padicValRat.pow] at hB
  have hRodd := hR
  rw [Int.even_iff] at hRodd
  have hBnonneg : 0 ≤ padicValRat p R - 2 *
      padicValRat p (valuationSelectorSum g s k R D) := by
    rcases hB with h | h
    · exact h
    · rw [Int.even_iff] at h
      norm_cast at h
      omega
  have hpos : 0 < padicValRat p R := by omega
  refine ⟨hpos, ?_⟩
  by_contra hnone
  push Not at hnone
  have hall : ∀ a ∈ g, padicValRat p R ≤
      padicValRat p (valuationSelectorWeight s k R (D a)) := by
    intro a ha
    obtain ⟨j, hj, hD, hfail⟩ := hnone a ha
    exact valuationSelectorWeight_high_of_failure s k hR hpos (D a)
      hj (hk j hj) hD hfail
  have hhigh : padicValRat p R ≤ padicValRat p (valuationSelectorSum g s k R D) :=
    val_finset_sum_ge g _ _ (fun a ha => Or.inr (hall a ha)) hΘ
  omega

#print axioms finiteValuationSelector_sound

end GaloisForLFunctions.HTGeometry.Arithmetic
