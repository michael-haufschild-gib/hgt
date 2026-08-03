import GaloisForLFunctions.HTGeometry.BesselOrderIntensity
import GaloisForLFunctions.HTGeometry.RationalExponentialProgressionGrowth

/-!
# Bessel order growth versus the Dreyfus progression normal form

This module closes the analytic-growth half of the Dreyfus argument: neither the real-order
Schlaefli carrier nor its reflected intensity can have the rational-exponential normal form that
the classification theorem supplies to a differentially algebraic linear-shift solution.
-/

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- The Bessel order sequence on every positive integer ray is outside the exact
rational-exponential progression class. -/
theorem realModifiedBesselKOrder_not_rationalExponentialProgression
    {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    ¬ HasRationalExponentialProgressionRepresentation
      (fun n => (realModifiedBesselKOrder s (x + n) : ℂ)) := by
  intro hrep
  obtain ⟨C, A, d, hC, hA, hupper⟩ := hrep.eventually_upper
  have hupperReal : ∀ᶠ n : ℕ in Filter.atTop,
      realModifiedBesselKOrder s (x + n) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n := by
    filter_upwards [hupper] with n hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (realModifiedBesselKOrder_pos hs _)] at hn
    exact hn
  exact realModifiedBesselKOrder_not_eventually_polynomialExponential_upper
    hs hx hC hA d hupperReal

/-- The order sequence is outside the Dreyfus normal form on every positive integer-period
progression, not only on the unit progression. -/
theorem realModifiedBesselKOrder_not_rationalExponentialPeriodicProgression
    {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x)
    {ell : ℕ} (hell : 1 ≤ ell) :
    ¬ HasRationalExponentialProgressionRepresentation
      (fun n => (realModifiedBesselKOrder s (x + (ell * n : ℕ)) : ℂ)) := by
  intro hrep
  obtain ⟨C, A, d, hC, hA, hupper⟩ := hrep.eventually_upper
  have hupperReal : ∀ᶠ n : ℕ in Filter.atTop,
      realModifiedBesselKOrder s (x + (ell * n : ℕ)) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n := by
    filter_upwards [hupper] with n hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (realModifiedBesselKOrder_pos hs _)] at hn
    exact hn
  exact realModifiedBesselKOrder_not_eventually_polynomialExponential_upper_multiple
    hs hx hell hC hA d hupperReal

/-- The reflected Bessel intensity sequence is likewise outside the exact
rational-exponential progression class. -/
theorem realModifiedBesselOrderIntensity_not_rationalExponentialProgression
    {s x : ℝ} (hs : 0 < s) (hx : 3 ≤ x) :
    ¬ HasRationalExponentialProgressionRepresentation
      (fun n => ((realModifiedBesselKOrder s (x + n) *
        realModifiedBesselKOrder s (x - 2 + n) : ℝ) : ℂ)) := by
  intro hrep
  obtain ⟨C, A, d, hC, hA, hupper⟩ := hrep.eventually_upper
  have hupperReal : ∀ᶠ n : ℕ in Filter.atTop,
      realModifiedBesselKOrder s (x + n) *
          realModifiedBesselKOrder s (x - 2 + n) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n := by
    filter_upwards [hupper] with n hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos
      (realModifiedBesselKOrder_pos hs _)
      (realModifiedBesselKOrder_pos hs _))] at hn
    exact hn
  exact realModifiedBesselOrderIntensity_not_eventually_polynomialExponential_upper
    hs hx hC hA d hupperReal

/-- The reflected intensity is outside the Dreyfus normal form on every positive integer-period
progression. -/
theorem realModifiedBesselOrderIntensity_not_rationalExponentialPeriodicProgression
    {s x : ℝ} (hs : 0 < s) (hx : 3 ≤ x)
    {ell : ℕ} (hell : 1 ≤ ell) :
    ¬ HasRationalExponentialProgressionRepresentation
      (fun n => ((realModifiedBesselKOrder s (x + (ell * n : ℕ)) *
        realModifiedBesselKOrder s (x - 2 + (ell * n : ℕ)) : ℝ) : ℂ)) := by
  intro hrep
  obtain ⟨C, A, d, hC, hA, hupper⟩ := hrep.eventually_upper
  have hupperReal : ∀ᶠ n : ℕ in Filter.atTop,
      realModifiedBesselKOrder s (x + (ell * n : ℕ)) *
          realModifiedBesselKOrder s (x - 2 + (ell * n : ℕ)) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n := by
    filter_upwards [hupper] with n hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos
      (realModifiedBesselKOrder_pos hs _)
      (realModifiedBesselKOrder_pos hs _))] at hn
    exact hn
  exact
    realModifiedBesselOrderIntensity_not_eventually_polynomialExponential_upper_multiple
      hs hx hell hC hA d hupperReal

end

end HTGeometry
end GaloisForLFunctions
