import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolePairingsHaveTheirLiteralChannels
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPoleGammaAndCenterHaveOneConstant
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowErrorChannelsDisappear
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsAboveHalfHaveNoUpwardPrimes
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsAwayFromTheHorizonHaveNoExteriorPrimes
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsReadThePolarCenter

/-!
# The literal terminal polar source above half the horizon

A terminal profile separated from both one half and the horizon receives
neither upward prime products nor exterior downward products. The exact
complete matrix therefore retains the polar center minus `log(2π)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Every term of the complete polar–terminal pairing is retained at the finite horizon. -/
theorem complete_terminal_pole_pair_eq_channels {φ h : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt (Real.log N) / c *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector 1 N),
        horizonProfileVector (horizonWeights h N) N⟫ =
      -(Real.sqrt (Real.log N) / c *
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector 1 N) -
          (Real.log N - ramanujanAdjunctionEnergy 1) • normalizedRamanujanHorizonVector 1 N,
          horizonProfileVector (horizonWeights h N) N⟫) +
      Real.sqrt (Real.log N) / c *
        ⟪completeWeilSelfError φ c N • normalizedRamanujanHorizonVector 1 N,
          horizonProfileVector (horizonWeights h N) N⟫ +
      Real.sqrt (Real.log N) / c *
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector 1 N),
          horizonProfileVector (horizonWeights h N) N⟫ +
      Real.sqrt (Real.log N) / c *
        ⟪(completeWeilSelfFinitePart φ c + ramanujanAdjunctionEnergy 1 -
            Real.eulerMascheroniConstant) • normalizedRamanujanHorizonVector 1 N,
          horizonProfileVector (horizonWeights h N) N⟫ +
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ((∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / Real.sqrt n *
          ∑ j ∈ Icc 1 N,
            (arithmeticPoleKernel n j - archimedeanCenterKernel n j) / Real.sqrt j) / N) +
      terminalPolarGammaCenterPair φ h c N -
      (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / Real.sqrt n *
        actualExteriorDownwardRow (atomDilate φ (c / N)) N 1 n) / c -
      (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / n * upwardModeRow φ c N 1 n) / c := by
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let u : ℕ → ℝ := fun n => logProfile h ((n : ℝ) / N)
  let x := horizonProfileVector (fun n => u n / Real.sqrt n) N
  have hx : horizonProfileVector (horizonWeights h N) N = x :=
    horizonProfileVector_horizonWeights_eq_terminal h hN1
  have hn := sqrt_log_mul_terminal_row_pair hL u (nearGammaDownwardRow φ c N 1)
  change Real.sqrt (Real.log N) * ⟪normalizedNearGammaDownwardVector φ c N 1, x⟫ = _ at hn
  rw [sum_terminal_nearGammaDownwardRow_one_eq (φ := φ) (F := logProfile h) hc hN1] at hn
  have he := sqrt_log_mul_terminal_row_pair hL u
    (actualExteriorDownwardRow (atomDilate φ (c / N)) N 1)
  change Real.sqrt (Real.log N) * ⟪normalizedExteriorDownwardVector φ c N 1, x⟫ = _ at he
  have hnear := sqrt_log_mul_terminal_nearCenter_pair (m := 1) one_pos hL u
  have hfar := sqrt_log_mul_terminal_separatedCross_pair (m := 1) one_pos hL u
  have hfull := sqrt_log_mul_terminal_fullCenter_pair hL (completeWeilPoleShift φ c) u
  have hup := sqrt_log_mul_terminal_upward_pair hφ hsupp hM hc hN (m := 1) one_pos u
  have hone : ramanujanLagCoefficient 1 = fun _ => (1 : ℝ) :=
    funext ramanujanLagCoefficient_one
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one, hone] at hnear hfar hup
  have hall := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex N) =>
    Real.sqrt (Real.log N) * ⟪v, x⟫)
    (completeWeilMatrix_ramanujan_eq_terminal_channels hφ hsupp hM hc hN1 (m := 1) one_pos)
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, inv_one, one_smul] at hall
  rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc N 1] at hall
  simp only [real_inner_add_left, real_inner_sub_left, real_inner_neg_left,
    mul_add, mul_sub, mul_neg] at hall
  rw [hn, he, hnear, hfar, hfull, hup] at hall
  simp only [hx]
  calc
    _ = (Real.sqrt (Real.log N) *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector 1 N),
          x⟫) / c := by ring
    _ = _ := by
      rw [hall]
      simp only [real_inner_sub_left]
      unfold terminalPolarGammaCenterPair completeWeilPoleShift
      dsimp only [u]
      field_simp [hc.ne', hM.ne'] <;> ring

/-- The complete polar source on an interior terminal window has no critical-ratio-dependent
aliasing cross term. Both prime boundary channels vanish exactly on this support. -/
theorem tendsto_complete_terminal_pole_above_half
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) (normalizedRamanujanHorizonVector 1 N),
        horizonProfileVector (horizonWeights h N) N⟫) atTop
      (𝓝 (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ((∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x) -
          Real.log (2 * Real.pi) * ∫ x in (0 : ℝ)..1, logProfile h x))) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hcN := criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  simp only [pow_one, pow_zero, mul_one] at hcN
  have he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0) := by
    have ht := criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
    simp only [pow_zero, mul_one] at ht
    apply squeeze_zero (fun N => div_nonneg
      (mul_nonneg (hc0 N).le (Real.log_nonneg (hc N))) (Nat.cast_nonneg N)) (fun N => ?_) ht
    have hl : Real.log (c N) ≤ c N :=
      (Real.log_le_sub_one_of_pos (hc0 N)).trans (sub_le_self _ zero_le_one)
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (hc0 N).le) (Nat.cast_nonneg N)).trans_eq (by ring)
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |logProfile h x - logProfile h y| ≤ ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    fun x _ y _ => abs_logProfile_sub_le hh hsupp hA hBF hLF x y
  have hcRaw := tendsto_terminal_fullPolarCenter_pair
    (fun x => abs_logProfile_le hBF x) (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A))
    hFL (hhigh 1 hη.le) (by linarith only [hδ] : 0 < δ) (fun x _ hx => hlow x hx)
  have hcenter := hcRaw.const_mul ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2)
  change Tendsto (fun N : ℕ => ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
      ((∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / Real.sqrt n *
        ∑ j ∈ Icc 1 N,
          (arithmeticPoleKernel n j - archimedeanCenterKernel n j) / Real.sqrt j) / N))
      atTop (𝓝 (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x)) at hcenter
  have hg := tendsto_terminalPolarGammaCenterPair hφ hφsupp hM hh hA hsupp hc hcinf he
  have hr := tendsto_terminal_ratioPrime_residual_pairing hsupp hBF (m := 1) one_pos hcinf
  have hs := tendsto_terminal_selfError_pairing hφ hφsupp hM hsupp hBF (m := 1) one_pos hc hR hcrit
  have hp := tendsto_terminal_poleError_pairing hφ hφsupp hM hsupp hBF (m := 1) one_pos hc hR hcrit
  have hd := tendsto_terminal_referenceDiagonal_pairing (φ := φ) hsupp hBF
    (m := 1) one_pos hc0 hcinf (ramanujanAdjunctionEnergy 1 - Real.eulerMascheroniConstant)
  simp only [← add_sub_assoc] at hd
  have hext : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / Real.sqrt n *
        actualExteriorDownwardRow (atomDilate φ (c N / N)) N 1 n) / c N) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_terminal_exteriorDownward_pairing_eq_zero
      hφ hφsupp hη hhigh hc hcN] with N hN
    rw [hN 1, zero_div]
  have hup : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / n *
        upwardModeRow φ (c N) N 1 n) / c N) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_terminal_upward_pairing_eq_zero
      hφ hφsupp hδ hlow hc0 hcN] with N hN
    rw [hN 1, zero_div]
  have ht := ((((((hr.neg.add hs).add hp).add hd).add hcenter).add hg).sub hext).sub hup
  simp only [neg_zero, zero_add, add_zero, sub_zero] at ht
  have hconst : ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
      (∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x) +
      (-((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * Real.log (2 * Real.pi) *
        ∫ x in (0 : ℝ)..1, logProfile h x) =
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ((∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x) -
          Real.log (2 * Real.pi) * ∫ x in (0 : ℝ)..1, logProfile h x) := by ring
  rw [hconst] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (complete_terminal_pole_pair_eq_channels hφ hφsupp hM (hc0 N) hN).symm

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.complete_terminal_pole_pair_eq_channels
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_complete_terminal_pole_above_half
