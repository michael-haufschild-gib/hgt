import GaloisForLFunctions.RHTower.CCMGuinandWeilLiteralPolarPrimeSource
import GaloisForLFunctions.RHTower.CCMCriticalMellinGrowingCumulative
import GaloisForLFunctions.RHTower.RoutePPrimeGammaBaseCubicWeight

/-!
# CCM/Route-P cubic Green source bridge

The Route-P base Cauchy budget and the CCM critical-Mellin source initially live on apparently
different carriers.  This module identifies them before any Xi-zero expansion.  The continuous
cubic Green test

`exp(-h/2) / (4 * max(h, log 2)^(3 : ℕ))`

converts the literal CCM atom `Lambda(n) / sqrt(n)` at `h = log n` into the undifferenced
Route-P mass `Lambda(n) / (4 n log(n)^(3 : ℕ))`.  The maximum only fills the prime-free interval
`0 <= h < log 2`, making the test continuous on the compact CCM horizon without changing a
single arithmetic atom.

Consequently the whole CCM prime functional on this test is exactly the negative finite-aperture
Route-P base budget.  The natural-number mass pulls back coefficient-faithfully to every resolved
prime-depth cell, and its global sum is exactly the existing strict-subquantum P-G181 budget.
Adding the CCM pole channel gives an exact completion fracture: polar surplus minus the Route-P
budget.  Thus the remaining completed source problem is not carrier identification or prime
summability; it is cancellation/shorting of the polar--Gamma surplus before quadratic conormal
landing.  No RH conclusion or source-to-zero trace domination is asserted here.
-/

open Matrix MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Continuous logarithmic Green profile.  The clamp changes only the prime-free interval below
`log 2`. -/
def ccmRoutePBaseCubicGreenLogProfile (h : ℝ) : ℝ :=
  Real.exp (-h / 2) / (4 * (max h (Real.log 2)) ^ (3 : ℕ))

/-- The cubic Green profile transported to the compact physical CCM horizon. -/
def ccmRoutePBaseCubicGreenHorizonTest (a : ℝ) :
    C(CCMGuinandWeilHorizon, ℝ) := by
  refine ⟨fun omega => ccmRoutePBaseCubicGreenLogProfile
    (2 * a * (1 - omega.1)), ?_⟩
  unfold ccmRoutePBaseCubicGreenLogProfile
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro omega
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hmax : Real.log 2 ≤ max (2 * a * (1 - omega.1)) (Real.log 2) :=
      le_max_right _ _
    positivity

/-- At every possible arithmetic logarithm the harmless clamp disappears. -/
theorem ccmRoutePBaseCubicGreenLogProfile_log
    {n : ℕ} (hn : 2 ≤ n) :
    ccmRoutePBaseCubicGreenLogProfile (Real.log n) =
      Real.exp (-Real.log n / 2) / (4 * Real.log n ^ (3 : ℕ)) := by
  rw [ccmRoutePBaseCubicGreenLogProfile, max_eq_left]
  exact Real.strictMonoOn_log.monotoneOn
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (n : ℝ) ∈ Set.Ioi 0 by
      change 0 < (n : ℝ)
      exact_mod_cast (show 0 < n by omega))
    (by exact_mod_cast hn)

/-- The second critical half-density converts the CCM critical atom into the normalized
von-Mangoldt weight `Lambda(n)/n`. -/
theorem criticalMellinAtomWeight_mul_exp_neg_log_half
    {n : ℕ} (hn : 0 < n) :
    criticalMellinAtomWeight n * Real.exp (-Real.log n / 2) =
      finiteVonMangoldtRealWeight n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit :
      Real.exp (-Real.log n / 2) =
        Real.exp (Real.log n / 2) * Real.exp (-Real.log n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc
    criticalMellinAtomWeight n *
          (Real.exp (Real.log n / 2) * Real.exp (-Real.log n)) =
        (criticalMellinAtomWeight n * Real.exp (Real.log n / 2)) *
          Real.exp (-Real.log n) := by ring
    _ = ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n) := by
      rw [criticalMellinAtomWeight_mul_exp_log_half hn]
    _ = finiteVonMangoldtRealWeight n := by
      rw [Real.exp_neg, Real.exp_log hnR]
      rw [finiteVonMangoldtRealWeight]
      ring

/-- **Atomwise Frankenstein seam.**  One literal CCM atom evaluated on the cubic Green test is
exactly one natural-number Route-P base Cauchy mass. -/
theorem criticalMellinAtomWeight_mul_cubicGreenProfile
    {n : ℕ} (hn : 2 ≤ n) :
    criticalMellinAtomWeight n *
        ccmRoutePBaseCubicGreenLogProfile (Real.log n) =
      routePPrimeGammaBaseCubicWeight n := by
  rw [ccmRoutePBaseCubicGreenLogProfile_log hn,
    routePPrimeGammaBaseCubicWeight, routePPrimeGammaCubicWeight,
    vonMangoldtInverseLogPowerWeight]
  rw [show (0 + 3 : ℕ) = 3 by omega]
  rw [← criticalMellinAtomWeight_mul_exp_neg_log_half
    (show 0 < n by omega)]
  ring

/-- Affine horizon transport recovers the unclamped logarithmic Green profile. -/
theorem ccmRoutePBaseCubicGreenHorizonTest_log
    {a : ℝ} (ha : 0 < a) {h : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) (2 * a)) :
    ccmRoutePBaseCubicGreenHorizonTest a
        (ccmGuinandWeilLogToHorizon a h) =
      ccmRoutePBaseCubicGreenLogProfile h := by
  change ccmRoutePBaseCubicGreenLogProfile
      (2 * a * (1 - (ccmGuinandWeilLogToHorizon a h).1)) = _
  rw [ccmGuinandWeilLogToHorizon_coe_of_mem ha hh]
  congr 1
  field_simp [ha.ne']
  ring

/-- **Finite-aperture source identity.**  The literal CCM prime functional evaluated on one
continuous Green test is the negative truncated Route-P base budget. -/
theorem ccmGuinandWeilPrimeSourceFunctional_cubicGreen_eq
    {a : ℝ} (ha : 0 < a) :
    ccmGuinandWeilPrimeSourceFunctional a
        (ccmRoutePBaseCubicGreenHorizonTest a) =
      -∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        routePPrimeGammaBaseCubicWeight n := by
  rw [ccmGuinandWeilPrimeSourceFunctional_apply]
  calc
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -criticalMellinAtomWeight n *
          ccmRoutePBaseCubicGreenHorizonTest a
            (ccmGuinandWeilLogToHorizon a (Real.log n)) =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          -routePPrimeGammaBaseCubicWeight n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ccmRoutePBaseCubicGreenHorizonTest_log ha
          (ccmGuinandWeilPrimeLog_mem hn),
        neg_mul,
        criticalMellinAtomWeight_mul_cubicGreenProfile (Finset.mem_Icc.mp hn).1]
    _ = -∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        routePPrimeGammaBaseCubicWeight n := by
      rw [Finset.sum_neg_distrib]

/-- Exact completion fracture on the common Green test: CCM polar mass minus the truncated
Route-P base budget.  Any completed contraction must short this polar surplus before landing. -/
theorem ccmGuinandWeilPolarPrimeSourceFunctional_cubicGreen_eq
    {a : ℝ} (ha : 0 < a) :
    ccmGuinandWeilPolarPrimeSourceFunctional ha
        (ccmRoutePBaseCubicGreenHorizonTest a) =
      ccmGuinandWeilPoleSourceFunctional ha
          (ccmRoutePBaseCubicGreenHorizonTest a) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          routePPrimeGammaBaseCubicWeight n := by
  rw [ccmGuinandWeilPolarPrimeSourceFunctional, _root_.add_apply,
    ccmGuinandWeilPrimeSourceFunctional_cubicGreen_eq ha]
  ring

end

end RHTower
