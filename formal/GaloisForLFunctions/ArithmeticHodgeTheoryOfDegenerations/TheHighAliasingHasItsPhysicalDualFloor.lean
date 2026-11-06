import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRetainsItsMixedMass
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAlternatingWindowCountsTheConductorTwoPoints
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSynthesizedProfileIsRecoveredBelowTheGrid
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheHighFourierMassHasADualLowerBound
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmoothTerminalTestsRecoverWeightedMass
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Sharp aliasing floors from physical limits

Mixed physical mass, below-grid Fourier recovery, and the high-frequency
square completion identify the aliasing pairing of a moving unit-mass
source. Smooth terminal recovery vectors give the sharp weighted dual floor.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate ENNReal
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticDegenerationTheory

/-- The high-frequency pairing with a fixed recovery profile detects the exact
aliasing weight of every strongly convergent unit-mass physical source. -/
theorem tendsto_criticalCurve_highFourierPair_horizon_along_filter
    {l : Filter ℕ} (hl : l ≤ atTop)
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F h : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hh : ContDiff ℝ 2 h)
    (hs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) * c N ^ 8 *
      highFourierPair (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N)
        (normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N)
        (N * Real.exp (-A))) l
      (𝓝 (7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * halfWeight h y) * Real.exp (-(8 * y)))) := by
  let m := ∫ u, tiltedUnitSpline u
  let U := fun N => normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N
  let V := fun N => normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N
  let D := fun N => (∫ u, U N u * V N u) - m * ∫ u, U N u * halfWeight h u
  let E := fun N => highFourierPair (U N) (V N) (N * Real.exp (-A)) - D N
  have hU (N : ℕ) : ContDiff ℝ 2 (U N) :=
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline (x N) (c N) N)
  have hV (N : ℕ) : ContDiff ℝ 2 (V N) :=
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline (horizonWeights h N) (c N) N)
  have hUc (N : ℕ) (hN : 1 ≤ N) : HasCompactSupport (U N) :=
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (x N)
      (zero_lt_one.trans_le (hc1 N)) hN).mul_left
  have hVc (N : ℕ) (hN : 1 ≤ N) : HasCompactSupport (V N) :=
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (horizonWeights h N)
      (zero_lt_one.trans_le (hc1 N)) hN).mul_left
  have hH := contDiff_halfWeight hh
  have hHc := hasCompactSupport_halfWeight (hasCompactSupport_of_window hs)
  have herr := tendsto_criticalCurve_belowGrid_fourier_error
    contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero hh hs hA hc1 hR hcrit 16
  have hbound : ∀ᶠ N : ℕ in atTop, (m * c N ^ 8 * E N) ^ 2 ≤
      (m ^ 2 / (2 * Real.pi)) * (c N ^ 16 * belowGridFourierError tiltedUnitSpline h (c N) N A) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := sq_highFourierPair_sub_mass_le (hU N) (hUc N hN) (hV N) (hVc N hN)
      hH hHc (N * Real.exp (-A)) m
    have hhat (t : ℝ) : paperFT (cx (halfWeight h)) t = horizonTransform h (1 / 2 + Complex.I * t) := by
      simpa only [gammaOf_half_add] using paperFT_halfWeight_gammaOf h (1 / 2 + Complex.I * t)
    simp_rw [hhat] at hp
    change E N ^ 2 ≤ (∫ u, U N u ^ 2) / (2 * Real.pi) *
      belowGridFourierError tiltedUnitSpline h (c N) N A at hp
    have he0 : 0 ≤ belowGridFourierError tiltedUnitSpline h (c N) N A :=
      integral_nonneg fun _ => sq_nonneg _
    have hp' := hp.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hmass N) (by positivity)) he0)
    have hmul := mul_le_mul_of_nonneg_left hp' (sq_nonneg (m * c N ^ 8))
    change (m * c N ^ 8) ^ 2 * E N ^ 2 ≤
      (m * c N ^ 8) ^ 2 * (1 / (2 * Real.pi) *
        belowGridFourierError tiltedUnitSpline h (c N) N A) at hmul
    calc
      (m * c N ^ 8 * E N) ^ 2 = (m * c N ^ 8) ^ 2 * E N ^ 2 := mul_pow _ _ _
      _ ≤ (m * c N ^ 8) ^ 2 * (1 / (2 * Real.pi) *
          belowGridFourierError tiltedUnitSpline h (c N) N A) := hmul
      _ = (m ^ 2 / (2 * Real.pi)) *
          (c N ^ 16 * belowGridFourierError tiltedUnitSpline h (c N) N A) := by ring
  have helim : Tendsto (fun N => m * c N ^ 8 * E N) atTop (𝓝 0) := by
    have hzero := herr.const_mul (m ^ 2 / (2 * Real.pi))
    simp only [mul_zero] at hzero
    have hl := Real.continuous_sqrt.tendsto 0 |>.comp hzero
    simp only [Real.sqrt_zero] at hl
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [hbound] with N hn
    rw [Real.norm_eq_abs]
    exact Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hn)
  have hmain := tendsto_criticalCurve_mixed_mass_defect_along_filter hl hc1 hR hcrit hmass hF hL1 hA hh hs
  have hl := (helim.mono_left hl).add hmain
  simp only [zero_add] at hl
  refine hl.congr fun N => ?_
  dsimp only [E, D, U, V, m]
  ring

/-- The high-frequency mixed pairing along the full horizon sequence. -/
theorem tendsto_criticalCurve_highFourierPair_horizon
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F h : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hh : ContDiff ℝ 2 h)
    (hs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) * c N ^ 8 *
      highFourierPair (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N)
        (normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N)
        (N * Real.exp (-A))) atTop
      (𝓝 (7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * halfWeight h y) * Real.exp (-(8 * y)))) := by
  exact tendsto_criticalCurve_highFourierPair_horizon_along_filter le_rfl
    hc1 hR hcrit hmass hF hL1 hA hh hs

/-- The high-frequency recovery energy is precisely the total block energy minus
its closed below-grid part, in physical normalization. -/
theorem highFourierMass_normalized_horizon_eq {φ h : ℝ → ℝ} {A c : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    highFourierMass (normalizedCentredAtomicTest φ (horizonWeights h N) c N)
        (N * Real.exp (-A)) =
      1 / (2 * Real.pi) * (blockEnergy φ h c N - lowPart φ h c N A) := by
  let U := normalizedCentredAtomicTest φ (horizonWeights h N) c N
  let T : ℝ := N * Real.exp (-A)
  let J : ℝ → ℝ := fun t => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * t)‖ ^ 2 *
    (‖dirichletPoly N (horizonWeights h N) t‖ ^ 2 / N)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hs
  have hJ (t : ℝ) : ‖paperFT (cx U) t‖ ^ 2 = J t := by
    rw [paperFT_normalizedCentredAtomicTest hφ.continuous hφc _ hc hN, norm_mul, mul_pow]
    dsimp only [J]
    rw [norm_sq_div_eq hN, gammaOf_half_add]
  have hJi : Integrable J := integrable_blockIntegrand hφ hs h hc hN
  have hlo : (∫ t in (highFrequencies T)ᶜ, J t) = ∫ t in Set.Icc (-T) T, J t := by
    rw [← integral_indicator (measurableSet_highFrequencies T).compl,
      ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [ae_abs_ne_threshold T] with t ht
    simp only [Set.indicator, Set.mem_compl_iff, highFrequencies, Set.mem_setOf_eq]
    have hiff : (t ∈ Set.Icc (-T) T) ↔ (¬ T ≤ |t|) := by
      change (-T ≤ t ∧ t ≤ T) ↔ ¬ T ≤ |t|
      rw [← abs_le]
      constructor
      · intro h
        exact not_le.mpr (lt_of_le_of_ne h ht)
      · intro h
        exact (lt_of_not_ge h).le
    simp only [hiff]
  have hsplit := integral_add_compl (measurableSet_highFrequencies T) hJi
  rw [hlo] at hsplit
  change 1 / (2 * Real.pi) * (∫ t in highFrequencies T, ‖paperFT (cx U) t‖ ^ 2) = _
  simp_rw [hJ]
  change 1 / (2 * Real.pi) * (∫ t in highFrequencies T, J t) =
    1 / (2 * Real.pi) * ((∫ t, J t) - ∫ t in Set.Icc (-T) T, J t)
  rw [← hsplit]
  ring

/-- The recovery energy above the grid has the sharp tilted-spline aliasing limit. -/
theorem tendsto_criticalCurve_highFourierMass_horizon {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => c N ^ 8 *
      highFourierMass (normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N)
        (N * Real.exp (-A))) atTop
      (𝓝 (7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (halfWeight h y) ^ 2 * Real.exp (-(8 * y)))) := by
  have hcinf := (criticalCurve_facts hc1 hR hcrit).1
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hR hcrit 1 0
  have hdef := criticalCurve_sq_log_mul_energyDefect
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hh hA hs hc1 hR hcrit
  have hcinv : Tendsto (fun N => (c N ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hcinf)
  have hdeflim : Tendsto (fun N => c N ^ 8 *
      (blockEnergy tiltedUnitSpline h (c N) N - lowPart tiltedUnitSpline h (c N) N A -
        2 * Real.pi * horizonAlias tiltedUnitSpline h (c N) N)) atTop (𝓝 0) := by
    have hl := hdef.mul (hcrit.mul hcinv)
    simp only [mul_zero] at hl
    refine hl.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
    have hc : c N ≠ 0 := (zero_lt_one.trans_le (hc1 N)).ne'
    field_simp [hc, hlog]
  have halias := tendsto_rpow_eight_mul_horizonAlias hh hA hs hc1 hcinf hcN
  have hw : (∫ y, Real.exp (-(7 * y)) * h y ^ 2) =
      ∫ y, (halfWeight h y) ^ 2 * Real.exp (-(8 * y)) := by
    rw [← integral_exp_mul_halfWeight_sq]
    apply integral_congr_ae
    filter_upwards with y
    ring
  have haeq := aliasLimit_eq (∫ y, Real.exp (-(7 * y)) * h y ^ 2)
  rw [haeq, hw] at halias
  have hlim := (hdeflim.const_mul (1 / (2 * Real.pi))).add halias
  simp only [mul_zero, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [highFourierMass_normalized_horizon_eq contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    (zero_lt_one.trans_le (hc1 N)) hN]
  field_simp [Real.pi_ne_zero]; ring
/-- Every smooth terminal recovery profile supplies its sharp asymptotic dual floor
for the high-frequency energy of a strongly convergent unit-mass source. -/
theorem eventually_criticalCurve_highFourierMass_gt_dual_floor_along_filter
    {l : Filter ℕ} (hl : l ≤ atTop)
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F h : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hh : ContDiff ℝ 2 h)
    (hs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {b : ℝ} (hb : b < 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
      (2 * (∫ y, (F y * halfWeight h y) * Real.exp (-(8 * y))) -
        ∫ y, (halfWeight h y) ^ 2 * Real.exp (-(8 * y)))) :
    ∀ᶠ N : ℕ in l, b < (∫ u, tiltedUnitSpline u) ^ 2 * c N ^ 8 *
      highFourierMass (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N)
        (N * Real.exp (-A)) := by
  have hpair := tendsto_criticalCurve_highFourierPair_horizon_along_filter hl hc1 hR hcrit hmass hF hL1 hA hh hs
  have hself := tendsto_criticalCurve_highFourierMass_horizon hh hA hs hc1 hR hcrit
  have hlim := (hpair.const_mul 2).sub (hself.mono_left hl)
  have hbt : b < 2 * (7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
      ∫ y, (F y * halfWeight h y) * Real.exp (-(8 * y))) -
      7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (halfWeight h y) ^ 2 * Real.exp (-(8 * y)) := by
    convert hb using 1; ring
  filter_upwards [hlim.eventually (eventually_gt_nhds hbt), (eventually_ge_atTop 1).filter_mono hl] with N hn hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc1 N)
  have hU : ContDiff ℝ 2 (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N) :=
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline (x N) (c N) N)
  have hUc : HasCompactSupport (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N) :=
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (x N) hc0 hN).mul_left
  have hV : ContDiff ℝ 2
      (normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N) := contDiff_const.mul
    (contDiff_centredAtomicTest contDiff_tiltedUnitSpline (horizonWeights h N) (c N) N)
  have hVc : HasCompactSupport
      (normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N) :=
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero
    (horizonWeights h N) hc0 hN).mul_left
  have hdual := two_mul_scalar_highFourierPair_sub_le
    (f := normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N)
    (g := normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N)
    hU hUc hV hVc (N * Real.exp (-A)) (∫ u, tiltedUnitSpline u)
  have hd := mul_le_mul_of_nonneg_left hdual (pow_nonneg hc0.le 8)
  exact hn.trans_le (by convert hd using 1 <;> ring)

/-- Smooth recovery tests give the full-sequence aliasing dual floor. -/
theorem eventually_criticalCurve_highFourierMass_gt_dual_floor
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F h : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hh : ContDiff ℝ 2 h)
    (hs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {b : ℝ} (hb : b < 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
      (2 * (∫ y, (F y * halfWeight h y) * Real.exp (-(8 * y))) -
        ∫ y, (halfWeight h y) ^ 2 * Real.exp (-(8 * y)))) :
    ∀ᶠ N : ℕ in atTop, b < (∫ u, tiltedUnitSpline u) ^ 2 * c N ^ 8 *
      highFourierMass (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N)
        (N * Real.exp (-A)) := by
  exact eventually_criticalCurve_highFourierMass_gt_dual_floor_along_filter le_rfl
    hc1 hR hcrit hmass hF hL1 hA hh hs hb


private theorem memLp_two_of_L1_limit_of_unit_mass {ι : Type*} {l : Filter ι}
    [NeBot l] [IsCountablyGenerated l] {U : ι → ℝ → ℝ}
    (hU1 : ∀ n, Integrable (U n)) (hU2 : ∀ n, MemLp (U n) 2)
    (hmass : ∀ n, (∫ y, U n y ^ 2) ≤ 1)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun n => ∫ y, ‖U n y - F y‖) l (𝓝 0)) : MemLp F 2 := by
  have hnorm (n : ι) : ‖(hU2 n).toLp (U n)‖ ≤ 1 := by
    have hs : ‖(hU2 n).toLp (U n)‖ ^ 2 ≤ 1 := by
      rw [HTGeometry.norm_toLp_sq]
      exact hmass n
    nlinarith only [hs, norm_nonneg ((hU2 n).toLp (U n))]
  have hb (n : ι) : eLpNorm (U n) 2 ≤ 1 := by
    have he : eLpNorm (U n) 2 = ENNReal.ofReal ‖(hU2 n).toLp (U n)‖ := by
      rw [Lp.norm_toLp, ENNReal.ofReal_toReal (hU2 n).eLpNorm_ne_top]
    rw [he]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hnorm n)
  have hlp : Tendsto (fun n => eLpNorm (U n - F) 1) l (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.tendsto 0 |>.comp hL1
    simp only [ENNReal.ofReal_zero] at h
    refine h.congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hU1 n).sub hF)]
    simp only [Pi.sub_apply, Function.comp_def]
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (fun n => (hU1 n).aestronglyMeasurable) hF.aestronglyMeasurable hlp
  obtain ⟨s, _, hs⟩ := hmeasure.exists_seq_tendsto_ae'
  have hbound : eLpNorm F 2 ≤ 1 := Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall fun n => hb (s n)) (fun n => (hU2 (s n)).aestronglyMeasurable) hs
  exact ⟨hF.aestronglyMeasurable, hbound.trans_lt (by simp)⟩

/-- The full weighted terminal mass is the sharp asymptotic aliasing floor. -/
theorem eventually_criticalCurve_highFourierMass_gt_weighted_floor_along_filter
    {l : Filter ℕ} [NeBot l] [IsCountablyGenerated l] (hl : l ≤ atTop)
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A : ℝ} (hA : 0 < A) {b : ℝ}
    (hb : b < 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
      ∫ y in Set.Ioo (-A) 0, F y ^ 2 * Real.exp (-(8 * y))) :
    ∀ᶠ N : ℕ in l, b < (∫ u, tiltedUnitSpline u) ^ 2 * c N ^ 8 *
      highFourierMass (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N)
        (N * Real.exp (-A)) := by
  let U := fun N => normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N
  have hUd (N : ℕ) : ContDiff ℝ 2 (U N) :=
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline (x N) (c N) N)
  have hUc (N : ℕ) : HasCompactSupport (U N) := by
    rcases eq_or_ne N 0 with rfl | hN
    · have hzero : U 0 = 0 := by
        funext y
        simp only [U, normalizedCentredAtomicTest, Nat.cast_zero, Real.sqrt_zero,
          zero_div, zero_mul, Pi.zero_apply]
      rw [hzero]
      exact HasCompactSupport.zero
    · exact (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (x N)
        (zero_lt_one.trans_le (hc1 N)) (by omega : 1 ≤ N)).mul_left
  have hF2 : MemLp F 2 := memLp_two_of_L1_limit_of_unit_mass
    (fun N => (hUd N).continuous.integrable_of_hasCompactSupport (hUc N))
    (fun N => (hUd N).continuous.memLp_of_hasCompactSupport (hUc N)) hmass hF hL1
  let C : ℝ := 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne
  have hC : 0 < C := mul_pos (mul_pos (by norm_num) integral_tiltedUnitSpline_sq_pos)
    tiltedJordanOne_pos
  have hbC : b / C < ∫ y in Set.Ioo (-A) 0, F y ^ 2 * Real.exp (-(8 * y)) :=
    (div_lt_iff₀ hC).mpr (by simpa only [C, mul_comm] using hb)
  obtain ⟨H, hHd, hHs, hfloor⟩ := exists_smooth_exponential_dual_floor hF2 hA hbC
  let h : ℝ → ℝ := fun y => Real.exp (-(y / 2)) * H y
  have hh : ContDiff ℝ 2 h :=
    (Real.contDiff_exp.comp (contDiff_id.div_const (2 : ℝ)).neg).mul
      (hHd.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  have hs (y : ℝ) (hy : y ∉ Set.Icc (-A) 0) : h y = 0 := by
    simp only [h, hHs y hy, mul_zero]
  have hhalf : halfWeight h = H := by
    funext y
    simp only [halfWeight, h, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, one_mul]
  have hfloor' : b < C * (2 * (∫ y, (F y * H y) * Real.exp (-(8 * y))) -
      ∫ y, H y ^ 2 * Real.exp (-(8 * y))) := by
    simpa only [mul_comm] using (div_lt_iff₀ hC).mp hfloor
  apply eventually_criticalCurve_highFourierMass_gt_dual_floor_along_filter hl hc1 hR hcrit hmass hF hL1
    hA.le hh hs
  simpa only [hhalf] using hfloor'

/-- The full weighted terminal mass is the full-sequence aliasing floor. -/
theorem eventually_criticalCurve_highFourierMass_gt_weighted_floor
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 < A) {b : ℝ}
    (hb : b < 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
      ∫ y in Set.Ioo (-A) 0, F y ^ 2 * Real.exp (-(8 * y))) :
    ∀ᶠ N : ℕ in atTop, b < (∫ u, tiltedUnitSpline u) ^ 2 * c N ^ 8 *
      highFourierMass (normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N)
        (N * Real.exp (-A)) := by
  exact eventually_criticalCurve_highFourierMass_gt_weighted_floor_along_filter le_rfl
    hc1 hR hcrit hmass hF hL1 hA hb

#print axioms eventually_criticalCurve_highFourierMass_gt_weighted_floor_along_filter
#print axioms eventually_criticalCurve_highFourierMass_gt_weighted_floor
#print axioms tendsto_criticalCurve_highFourierPair_horizon
#print axioms tendsto_criticalCurve_highFourierMass_horizon
#print axioms eventually_criticalCurve_highFourierMass_gt_dual_floor
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
