import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.WindowWeightsHaveWeightedMassLimits
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AsymmetricTwoRegionConductorReserve
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingIsCoercive
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryTerminalWindowHasAPolarConductorSource

/-!
# Physical pairings of terminal window vectors

Fixed windows eventually lie in the growing collar, and their seventh mass is
controlled by the full weighted coefficient mass. The exact signed polar source
and the synthesized Lipschitz pairings retain their physical normalizations.
-/


set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis

/-- Every fixed logarithmic window eventually lies beyond the linear collar cutoff. -/
theorem eventually_horizonWindow_prefix_zero {h : ℝ → ℝ} {A : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc (-A) 0 → h u = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop) :
    ∀ᶠ N : ℕ in atTop, ∀ n, n ≤ N / linearDefectCutoff (c N) →
      primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) n = 0 := by
  filter_upwards [eventually_ge_atTop 1, hcinf.eventually_gt_atTop (Real.exp A)] with N hN hcA n hn
  by_cases hmem : n ∈ Icc 1 N
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hmem).1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcut := linearDefectCutoff_bounds (hc N)
    have hcut0 : 0 < linearDefectCutoff (c N) := by omega
    have hprod : n * linearDefectCutoff (c N) ≤ N := (Nat.le_div_iff_mul_le hcut0).mp hn
    have hlarge : Real.exp A < (linearDefectCutoff (c N) : ℝ) := by
      have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
      linarith only [hcA, hcut.2.1, hc0]
    have hprodR : (n : ℝ) * Real.exp A < N :=
      (mul_lt_mul_of_pos_left hlarge hn0).trans_le (by exact_mod_cast hprod)
    have hx : (n : ℝ) / N < Real.exp (-A) := by
      rw [Real.exp_neg, ← one_div]
      exact (div_lt_div_iff₀ hN0 (Real.exp_pos A)).mpr (by simpa only [one_mul] using hprodR)
    have hlog : Real.log n - Real.log N < -A := by
      have hh := (Real.log_lt_iff_lt_exp (div_pos hn0 hN0)).mpr hx
      simpa only [Real.log_div hn0.ne' hN0.ne'] using hh
    let i : PrimeHorizonIndex N := ⟨n, hmem⟩
    change primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) i.1 = 0
    rw [primeHorizonExtension_coe]
    change h (Real.log n - Real.log N) / Real.sqrt n = 0
    rw [hsupp _ (fun hu => not_lt_of_ge hu.1 hlog), zero_div]
  · simp only [primeHorizonExtension, hmem, dite_false]

/-- A window's collar mass is bounded by its full seventh weighted coefficient mass. -/
theorem topCollarSeventhMass_horizonWindow_le (h : ℝ → ℝ) (M N : ℕ) :
    topCollarSeventhMass M N
      (primeHorizonExtension (horizonProfileVector (horizonWeights h N) N)) ≤
      ∑ n ∈ Icc 1 N, ((N : ℝ) / n) ^ 7 * horizonWeights h N n ^ 2 := by
  unfold topCollarSeventhMass
  have he : (∑ n ∈ Ioc M N, ((N : ℝ) / n) ^ 7 *
      primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) n ^ 2) =
      ∑ n ∈ Ioc M N, ((N : ℝ) / n) ^ 7 * horizonWeights h N n ^ 2 := by
    refine sum_congr rfl fun n hn => ?_
    have hmem : n ∈ Icc 1 N := mem_Icc.mpr
      ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
    let i : PrimeHorizonIndex N := ⟨n, hmem⟩
    change _ * primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) i.1 ^ 2 = _
    rw [primeHorizonExtension_coe]
    rfl
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg
    (fun n hn => mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩)
    (fun n _ _ => by positivity)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
end


set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis CompletedArithmeticForms

/-- The completed ground conductor diagonal has vanishing mixed normalization on every fixed window. -/
theorem tendsto_polar_conductor_diagonal_window_pairing
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪completedConductorEnergy tiltedUnitSpline (c N) 1 • normalizedRamanujanHorizonVector 1 N,
        horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 0) := by
  let C := tiltedConductorUpperCoefficient 1
  have hC : 0 < C := tiltedConductorUpperCoefficient_pos one_pos
  have hB0 : 0 ≤ B := (abs_nonneg (h 0)).trans (hB 0)
  have ht : Tendsto (fun N : ℕ => C * (2 * B * Real.exp A) / c N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcinf
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hN hL
  change 0 < Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  have hE0 : 0 ≤ completedConductorEnergy tiltedUnitSpline (c N) 1 :=
    completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc0 one_pos
  have hE : completedConductorEnergy tiltedUnitSpline (c N) 1 ≤ C :=
    (tiltedConductorEnergy_two_sided (m := 1) one_pos
      (by simpa only [Nat.cast_one] using hc N)).2.trans
      (div_le_self hC.le (one_le_pow₀ (hc N)))
  have hi := abs_horizon_window_conductor_inner_le hsupp hB (m := 1) one_pos hN
  rw [real_inner_comm] at hi
  rw [Real.norm_eq_abs, real_inner_smul_left, abs_mul, abs_mul,
    abs_of_pos (div_pos hsL hc0), abs_of_nonneg hE0]
  calc
    _ ≤ (Real.sqrt (Real.log N) / c N) *
        (C * ((2 * B * Real.exp A) / Real.sqrt (Real.log N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hE hi (abs_nonneg _) hC.le)
        (div_pos hsL hc0).le
    _ = _ := by field_simp [hsL.ne', hc0.ne']

/-- Subtracting the completed conductor energy preserves the exact signed polar window source. -/
theorem tendsto_polar_residual_window_pairing {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ u, u ∉ Set.Icc (-A) 0 → h u = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪conductorResidualVector (c N) 1 N, horizonProfileVector (horizonWeights h N) N⟫)
      atTop (𝓝 (generalTerminalPolarSource A h)) := by
  obtain ⟨B, _, hB, _⟩ := exists_bound_lipschitz hh hsupp
  have hd := tendsto_polar_conductor_diagonal_window_pairing hsupp hB hc
    (criticalCurve_facts hc hR hcrit).1
  have hm := tendsto_complete_terminal_pole contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos hh hA hsupp hc hR hcrit
  change Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector 1 N), horizonProfileVector (horizonWeights h N) N⟫)
      atTop (𝓝 (generalTerminalPolarSource A h)) at hm
  have ht := hm.sub hd
  rw [sub_zero] at ht
  exact ht.congr fun N => by rw [conductorResidualVector, inner_sub_left, mul_sub]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
end

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
/-- The synthesized window paired with a Lipschitz test has the expected physical limit. -/
theorem tendsto_horizonWindow_atomic_pairing {h f : ℝ → ℝ} {A : ℝ}
    (hh : Continuous h) (hA : 0 ≤ A)
    (hsupp : ∀ u, u ∉ Set.Icc (-A) 0 → h u = 0)
    {K : NNReal} (hf : LipschitzWith K f) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hwidth : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ u, normalizedCentredAtomicTest tiltedUnitSpline
      (primeHorizonExtension (horizonProfileVector (horizonWeights h N) N)) (c N) N u * f u)
      atTop (𝓝 (∫ u, ((∫ v, tiltedUnitSpline v) * halfWeight h u) * f u)) := by
  let x := fun N => primeHorizonExtension (horizonProfileVector (horizonWeights h N) N)
  have hext (N n : ℕ) (hn : n ∈ Icc 1 N) : x N n = horizonWeights h N n := by
    let i : PrimeHorizonIndex N := ⟨n, hn⟩
    change primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) i.1 = _
    rw [primeHorizonExtension_coe]
    rfl
  have hsq (N : ℕ) : (∑ n ∈ Icc 1 N, x N n ^ 2) = ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 :=
    sum_congr rfl fun n hn => by rw [hext N n hn]
  have hpair (N : ℕ) : (∑ n ∈ Icc 1 N, x N n * f (Real.log n - Real.log N)) =
      ∑ n ∈ Icc 1 N, horizonWeights h N n * f (Real.log n - Real.log N) :=
    sum_congr rfl fun n hn => by rw [hext N n hn]
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_sum_horizonWeights_sq hh hsupp hA)
  have he := (((hwidth.mul_const (K : ℝ)).mul_const (∫ u, |tiltedUnitSpline u|)).mul hnorm)
  simp only [zero_mul] at he
  let P := fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
    ∑ n ∈ Icc 1 N, horizonWeights h N n * f (Real.log n - Real.log N)
  have hdiff : Tendsto (fun N : ℕ => (∫ u, normalizedCentredAtomicTest tiltedUnitSpline
      (x N) (c N) N u * f u) - P N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ he
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hb := abs_integral_normalizedCentredAtomicTest_mul_sub_le
      contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero hf (hc N) hN (x N)
    rw [hsq N, hpair N] at hb
    exact hb
  have hp : Tendsto P atTop
      (𝓝 ((∫ u, tiltedUnitSpline u) * ∫ u, halfWeight h u * f u)) := by
    have hh := (tendsto_horizonWeights_sample_pairing hh hf.continuous hA hsupp).const_mul
      (∫ u, tiltedUnitSpline u)
    convert hh using 1
    funext N
    dsimp only [P]
    ring
  have ht := hdiff.add hp
  simp only [sub_add_cancel, zero_add] at ht
  have hlim : (∫ u, ((∫ v, tiltedUnitSpline v) * halfWeight h u) * f u) =
      (∫ v, tiltedUnitSpline v) * ∫ u, halfWeight h u * f u := by
    simp only [mul_assoc, integral_const_mul]
  rw [hlim]
  exact ht

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
