import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionCurvature
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature

/-!
# Source-horizontal Gamma-six landing of the wall--Xi Malgrange curvature

The first-jet-normalized prime/Gamma wall misses completed Xi by a positive real quadratic
Malgrange anomaly.  This module constructs that anomaly from the fixed opposite-character
Gamma-six boundary source.  Its source clock is positive and uniquely determined on every cold
aperture `d ≥ 1`; no Xi zero, RH premise, or adjustable complex phase enters.

This closes quadratic incidence only.  It does not identify the higher Fredholm coefficients or
prove equality of the full tau germs.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Real projective curvature missing from the first-jet-normalized prime/Gamma wall. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap
    (d : ℝ) : ℝ :=
  (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re -
    normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2

/-- Positive source clock landing the unit opposite-character Gamma-six curvature on the
wall--Xi quadratic anomaly. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock
    (d : ℝ) : ℝ :=
  (normalizedPrimeArchMoment 0 / 2) *
    Real.sqrt (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap d)

/-- The source-defined wall--Xi projective curvature gap is positive on every `d ≥ 1`. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap_pos
    {d : ℝ} (hd : 1 ≤ d) :
    0 < routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap d := by
  have hwall :=
    nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_of_one_le
      hd
  have hXi := normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap]
  linarith

/-- The canonical Gamma-six landing clock is strictly positive. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock_pos
    {d : ℝ} (hd : 1 ≤ d) :
    0 < routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d := by
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock]
  exact mul_pos
    (div_pos normalizedPrimeArchMoment_zero_pos (by norm_num))
    (Real.sqrt_pos.2
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap_pos hd))

/-- Opposite-character Gamma-six correction energy vanishes at neutral character. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionEnergy_zero
    (d : ℝ) :
    sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d) 0 = 0 := by
  rw [sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
  simp

/-- Opposite-character cancellation makes the source correction first-order flat. -/
theorem hasDerivAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionEnergy_zero
    (d : ℝ) :
    HasDerivAt
      (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d)) 0 0 := by
  simpa using
    hasDerivAt_sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d) 0

private theorem sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_secondJet
    (lambda : ℝ) :
    deriv (fun t : ℝ =>
      deriv (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy lambda) t) 0 =
        2 * lambda ^ 2 := by
  have hderiv :
      (fun t : ℝ =>
        deriv (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy lambda) t) =
      fun t : ℝ => 2 * lambda * Real.sinh (lambda * t) := by
    funext t
    exact (hasDerivAt_sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy lambda t).deriv
  rw [hderiv]
  have hsinh :
      HasDerivAt (fun t : ℝ => Real.sinh (lambda * t)) lambda 0 := by
    simpa using (hasDerivAt_const_mul (𝕜 := ℝ) (x := 0) lambda).sinh
  have hscaled := hsinh.const_mul (2 * lambda)
  simpa [pow_two, mul_assoc] using hscaled.deriv

/-- Exact irregular-RH landing: source-horizontal Gamma-six paired curvature supplies the full
complex quadratic Malgrange anomaly, including absence of an imaginary remainder. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two_eq_gammaSixCorrectionEnergy_secondJet
    {d : ℝ} (hd : 1 ≤ d) :
    iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0 =
      ((deriv (fun t : ℝ =>
        deriv (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d)) t) 0 : ℝ) : ℂ) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hgap0 :
      0 ≤ routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap d :=
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap_pos hd).le
  have hsqrt := Real.sq_sqrt hgap0
  have hgap_eq :
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap d =
        routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d / 2 -
          normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 := by
    rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionGap,
      routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_eq_half_coherence hd0]
    simp
  have hclock_sq :
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d ^ 2 =
        (normalizedPrimeArchMoment 0 / 2) ^ 2 *
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d / 2 -
            normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2) := by
    rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock,
      mul_pow, hsqrt, hgap_eq]
  rw [sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_secondJet,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two hd0,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_eq_half_coherence hd0,
    hclock_sq]
  simp only [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale]
  push_cast
  ring

/-- Positive source clock is unique among Gamma-six clocks with the required second jet. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock_eq_of_pos_of_secondJet_eq
    {d lambda : ℝ} (hd : 1 ≤ d) (hlambda : 0 < lambda)
    (hmatch :
      ((deriv (fun t : ℝ =>
        deriv (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy lambda) t) 0 : ℝ) : ℂ) =
        iteratedDeriv 2
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0) :
    lambda = routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d := by
  rw [sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_secondJet,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two_eq_gammaSixCorrectionEnergy_secondJet
      hd,
    sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_secondJet] at hmatch
  have hsquares : 2 * lambda ^ 2 =
      2 * routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d ^ 2 :=
    Complex.ofReal_injective hmatch
  have hclock :=
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock_pos hd
  nlinarith

/-- Capstone: positive, first-order-flat Gamma-six source data land the exact wall--Xi quadratic
Malgrange correction on every cold aperture. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionQuadraticLanding
    {d : ℝ} (hd : 1 ≤ d) :
    0 < routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d ∧
      sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d) 0 = 0 ∧
      deriv (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d)) 0 = 0 ∧
      iteratedDeriv 2
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0 =
        ((deriv (fun t : ℝ =>
          deriv (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
            (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d)) t) 0 : ℝ) : ℂ) := by
  exact ⟨routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock_pos hd,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionEnergy_zero d,
    (hasDerivAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionEnergy_zero d).deriv,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two_eq_gammaSixCorrectionEnergy_secondJet hd⟩

/-- Entire complexification of the opposite-character Gamma-six boundary correction. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog
    (d : ℝ) (z : ℂ) : ℂ :=
  2 * (Complex.cosh
    ((routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℝ) * z) - 1)

/-- Prime/Gamma wall log after adding the source-horizontal Gamma-six correction. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog
    (d : ℝ) (z : ℂ) : ℂ :=
  Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z) +
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d z

private theorem hasDerivAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog
    (d : ℝ) (z : ℂ) :
    HasDerivAt
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d)
      (2 * (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ) *
        Complex.sinh
          ((routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ) * z)) z := by
  let k : ℂ :=
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ)
  have hlinear : HasDerivAt (fun w : ℂ => k * w) k z :=
    hasDerivAt_const_mul k
  have hcosh := (Complex.hasDerivAt_cosh (k * z)).comp z hlinear
  have hshift := hcosh.sub_const 1
  have hscaled := hshift.const_mul 2
  change HasDerivAt (fun w : ℂ => 2 * (Complex.cosh (k * w) - 1))
    (2 * k * Complex.sinh (k * z)) z
  simpa only [Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Gamma-six correction log is entire. -/
theorem analyticAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog
    (d : ℝ) (z : ℂ) :
    AnalyticAt ℂ
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) z := by
  have hdiff : Differentiable ℂ
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) :=
    fun w =>
      (hasDerivAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d w).differentiableAt
  exact hdiff.analyticAt z

/-- Complexified Gamma-six correction vanishes at neutral character. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_zero
    (d : ℝ) :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d 0 = 0 := by
  simp [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog]

/-- Complexified Gamma-six correction remains first-order flat. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_one
    (d : ℝ) :
    iteratedDeriv 1
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 = 0 := by
  rw [iteratedDeriv_one]
  simpa using
    (hasDerivAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d 0).deriv

/-- Complex Gamma-six correction has exact quadratic jet `2κ_d²`. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_two
    (d : ℝ) :
    iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 =
      2 * (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ) ^ 2 := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ', iteratedDeriv_one]
  have hderiv :
      (fun z : ℂ =>
        deriv (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) z) =
      fun z : ℂ =>
        2 * (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ) *
          Complex.sinh
            ((routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ) * z) := by
    funext z
    exact
      (hasDerivAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d z).deriv
  change deriv (fun z : ℂ =>
    deriv (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) z) 0 = _
  rw [hderiv]
  let k : ℂ :=
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ)
  have hlinear : HasDerivAt (fun z : ℂ => k * z) k 0 :=
    hasDerivAt_const_mul k
  have hsinh := (Complex.hasDerivAt_sinh (k * 0)).comp 0 hlinear
  have hscaled := hsinh.const_mul (2 * k)
  simpa [k, Function.comp_def, pow_two, mul_assoc] using hscaled.deriv

/-- Entire Gamma-six source correction equals the inferred wall--Xi Malgrange correction at
quadratic order. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_two_eq_malgrangeCorrection
    {d : ℝ} (hd : 1 ≤ d) :
    iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 =
      iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0 := by
  rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_two,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two_eq_gammaSixCorrectionEnergy_secondJet
      hd,
    sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_secondJet]
  push_cast
  ring

private theorem analyticAt_primeGammaWallXiGammaSixScaledTauLog (d : ℝ) :
    AnalyticAt ℂ
      (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
  apply ((differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale).analyticAt 0).clog
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
  exact Complex.one_mem_slitPlane

/-- Corrected wall log is analytic at the central seam. -/
theorem analyticAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog
    (d : ℝ) :
    AnalyticAt ℂ
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d) 0 := by
  exact (analyticAt_primeGammaWallXiGammaSixScaledTauLog d).add
    (analyticAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d 0)

/-- Corrected wall log and canonical Xi log agree at the central value. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_zero
    (d : ℝ) :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d 0 =
      canonicalXiSeamLog 0 := by
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_zero,
    canonicalXiSeamLog_zero]
  norm_num

/-- Corrected wall and Xi logarithmic tau germs have equal first jets. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_one
    {d : ℝ} (hd : 1 ≤ d) :
    iteratedDeriv 1
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d) 0 =
      iteratedDeriv 1 canonicalXiSeamLog 0 := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hwall : ContDiffAt ℂ 1
      (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 :=
    (analyticAt_primeGammaWallXiGammaSixScaledTauLog d).contDiffAt
  have hcorrection : ContDiffAt ℂ 1
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 :=
    (analyticAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d 0).contDiffAt
  have hXi : ContDiffAt ℂ 1 canonicalXiSeamLog 0 :=
    analyticAt_canonicalXiSeamLog.contDiffAt
  have hmatch :=
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_one hd0
  change iteratedDeriv 1
    (canonicalXiSeamLog - fun z => Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 = 0 at hmatch
  rw [iteratedDeriv_sub hXi hwall] at hmatch
  change iteratedDeriv 1
    ((fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) +
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 = _
  rw [iteratedDeriv_add hwall hcorrection,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_one]
  linear_combination -hmatch

/-- Corrected wall and Xi logarithmic tau germs have equal second jets. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_two
    {d : ℝ} (hd : 1 ≤ d) :
    iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d) 0 =
      iteratedDeriv 2 canonicalXiSeamLog 0 := by
  have hwall : ContDiffAt ℂ 2
      (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 :=
    (analyticAt_primeGammaWallXiGammaSixScaledTauLog d).contDiffAt
  have hcorrection : ContDiffAt ℂ 2
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 :=
    (analyticAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d 0).contDiffAt
  have hXi : ContDiffAt ℂ 2 canonicalXiSeamLog 0 :=
    analyticAt_canonicalXiSeamLog.contDiffAt
  have hmatch :=
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_two_eq_malgrangeCorrection
      hd).symm
  change iteratedDeriv 2
    (canonicalXiSeamLog - fun z => Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 = _ at hmatch
  rw [iteratedDeriv_sub hXi hwall] at hmatch
  change iteratedDeriv 2
    ((fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) +
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 = _
  rw [iteratedDeriv_add hwall hcorrection]
  linear_combination -hmatch

/-- Source-horizontal analytic correction makes wall and Xi logarithmic tau germs agree through
order two. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_twoJetContact
    {d : ℝ} (hd : 1 ≤ d) :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d 0 =
        canonicalXiSeamLog 0 ∧
      iteratedDeriv 1
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d) 0 =
        iteratedDeriv 1 canonicalXiSeamLog 0 ∧
      iteratedDeriv 2
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d) 0 =
        iteratedDeriv 2 canonicalXiSeamLog 0 := by
  exact ⟨routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_zero d,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_one hd,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_two hd⟩

end

end RHTower
