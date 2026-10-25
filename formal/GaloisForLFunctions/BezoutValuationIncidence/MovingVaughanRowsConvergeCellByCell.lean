import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanLimitRowsAreIndependentInTwoCells
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicRemaindersInAllVaughanRows

/-!
Divergent cutoffs recover the actual Vaughan frame at every fixed cell. The
harmonic smooth coefficient tends to zero, so the same cell limits hold for
the smooth-subtracted rows.
-/

open Finset Filter RHTower ArithmeticFunction
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem tendsto_vaughan_first_centered_cell {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ → ℕ} (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (n : ℕ) :
    Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n 0)
      atTop (𝓝 (pmPowerDampedCenteredDivisorPrefix ε n)) := by
  have heq : ∀ᶠ t : ℕ in atTop,
      pmPronicVaughanPiece ε (U t) (V t) n 0 =
        pmPowerDampedCenteredDivisorPrefix ε n + (pmPowerDampedDivisorDensity ε).re * n := by
    filter_upwards [hU.eventually_ge_atTop n] with t ht
    change (∑ d ∈ Icc 1 (min (U t) n), (moebius d : ℝ) * pmPronicFloorWeight ε n d) = _
    rw [min_eq_right ht, pmCenteredPrefix_eq_weighted_floor]
    ring
  have hp : Tendsto (fun t => pmPronicVaughanPiece ε (U t) (V t) n 0) atTop
      (𝓝 (pmPowerDampedCenteredDivisorPrefix ε n + (pmPowerDampedDivisorDensity ε).re * n)) :=
    (tendsto_congr' heq).mpr tendsto_const_nhds
  have h := hp.sub ((tendsto_pmPronicVaughanMean_moving hε hU hV 0).mul_const (n : ℝ))
  change Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n 0) atTop
    (𝓝 (pmPowerDampedCenteredDivisorPrefix ε n + (pmPowerDampedDivisorDensity ε).re * n -
      ((pmPowerDampedDivisorDensity ε).re * 1) * n)) at h
  simpa only [mul_one, add_sub_cancel_right] using h

/-- At every fixed cell, divergent cutoffs recover the two-row actual Vaughan frame. -/
theorem tendsto_pmPronicVaughanCentredPiece_moving_cell {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ → ℕ} (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop)
    (n : ℕ) (i : Fin 5) :
    Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n i) atTop
      (𝓝 (pmPronicVaughanLimitFrame ε i n)) := by
  have h0 := tendsto_vaughan_first_centered_cell hε hU hV n
  have h1 : Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n 1) atTop
      (𝓝 (pmPowerDampedCenteredDivisorPrefix ε n)) :=
    tendsto_vaughan_first_centered_cell hε hV hU n
  have h3 : Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n 3) atTop (𝓝 0) := by
    have heq : ∀ᶠ t : ℕ in atTop, pmPronicVaughanPiece ε (U t) (V t) n 3 = 0 := by
      filter_upwards [hU.eventually_ge_atTop n] with t ht
      apply pmPronicVaughanPiece_large_eq_zero_of_cover
      nlinarith only [ht, Nat.zero_le (U t * V t), Nat.zero_le (V t)]
    have hp : Tendsto (fun t => pmPronicVaughanPiece ε (U t) (V t) n 3) atTop (𝓝 0) :=
      (tendsto_congr' heq).mpr tendsto_const_nhds
    have h := hp.sub ((tendsto_pmPronicVaughanMean_moving hε hU hV 3).mul_const (n : ℝ))
    change Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n 3) atTop
      (𝓝 (0 - ((pmPowerDampedDivisorDensity ε).re * 0) * n)) at h
    simpa only [mul_zero, zero_mul, sub_zero] using h
  have h4 : Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n 4) atTop
      (𝓝 (-addDiff (pmActiveSawtoothComponent ε) n)) := by
    have heq (t : ℕ) : pmPronicVaughanCentredPiece ε (U t) (V t) n 4 =
        -addDiff (pmActiveSawtoothComponent ε) n := by
      change -(pmPowerDampedDivisorDensity ε).re * n - addDiff (pmActiveSawtoothComponent ε) n -
        (-(pmPowerDampedDivisorDensity ε).re) * n = _
      ring
    simpa only [heq] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => -addDiff (pmActiveSawtoothComponent ε) n) atTop _)
  have h2 : Tendsto (fun t => pmPronicVaughanCentredPiece ε (U t) (V t) n 2) atTop
      (𝓝 (-pmPowerDampedCenteredDivisorPrefix ε n)) := by
    have heq (t : ℕ) : pmPronicVaughanCentredPiece ε (U t) (V t) n 2 =
        pmBezoutInteriorPrefix ε n -
          (pmPronicVaughanCentredPiece ε (U t) (V t) n 0 +
            (pmPronicVaughanCentredPiece ε (U t) (V t) n 1 +
              (pmPronicVaughanCentredPiece ε (U t) (V t) n 3 +
                pmPronicVaughanCentredPiece ε (U t) (V t) n 4))) := by
      have hs : (∑ j : Fin 5, pmPronicVaughanCentredPiece ε (U t) (V t) n j) =
          pmBezoutInteriorPrefix ε n := by
        simp only [pmPronicVaughanCentredPiece, sum_sub_distrib, ← sum_mul,
          sum_pmPronicVaughanPiece, sum_pmPronicVaughanMean, zero_mul, sub_zero]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
      linarith only [hs]
    have h := (tendsto_const_nhds (x := pmBezoutInteriorPrefix ε n)).sub
      (h0.add (h1.add (h3.add h4)))
    have hlimit : pmBezoutInteriorPrefix ε n -
        (pmPowerDampedCenteredDivisorPrefix ε n +
          (pmPowerDampedCenteredDivisorPrefix ε n + (0 + -addDiff (pmActiveSawtoothComponent ε) n))) =
        -pmPowerDampedCenteredDivisorPrefix ε n := by
      rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
      ring
    simpa only [← heq, hlimit] using h
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- Removing the vanishing harmonic smooth coefficient preserves each moving-cutoff cell limit. -/
theorem tendsto_pmPronicVaughanSmoothRemainder_moving_cell {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ → ℕ} (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop)
    (n : ℕ) (i : Fin 5) :
    Tendsto (fun t => pmPronicVaughanSmoothRemainder ε (U t) (V t) n i) atTop
      (𝓝 (pmPronicVaughanLimitFrame ε i n)) := by
  have hH : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 0
  have hcoeff := ((((hH.comp hU).const_mul (subHalfZetaCoeff ε)).mul (hH.comp hV)).mul_const
    (pmPronicVaughanSmoothSigns i)).mul_const ((n : ℝ) ^ (1 - ε))
  have h := (tendsto_pmPronicVaughanCentredPiece_moving_cell hε hU hV n i).sub hcoeff
  simpa only [pmPronicVaughanSmoothRemainder, Function.comp_def, mul_zero,
    zero_mul, sub_zero] using h

#print axioms tendsto_pmPronicVaughanCentredPiece_moving_cell
#print axioms tendsto_pmPronicVaughanSmoothRemainder_moving_cell
end GaloisForLFunctions.BezoutValuationIncidence
