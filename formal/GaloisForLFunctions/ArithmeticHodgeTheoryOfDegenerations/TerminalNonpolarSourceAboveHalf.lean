import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalConductorPairingsRetainTheDivisorJet
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalDivisorJetsCancelTheNonpolarCenter
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolarSourceAboveHalf

/-!
# Nonpolar conductors have no interior terminal source

Above half the horizon, both prime boundary channels vanish. The full
nonpolar center and divisor jet carry opposite von Mangoldt charges.
Their cancellation leaves zero in the literal complete mixed limit.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell
open ArithmeticFunction (vonMangoldt)

/-- The full center and its opposite divisor-jet receiving charge. -/
def terminalFullCenterJetPair (φ h : ℝ → ℝ) (c : ℝ) (N m : ℕ) : ℝ :=
  ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
    ((∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / Real.sqrt n *
      ∑ j ∈ Icc 1 N,
        (arithmeticPoleKernel n j - archimedeanCenterKernel n j) *
          (ramanujanLagCoefficient m j / Real.sqrt j)) / N) +
  endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
    (logProfile h) 0 2 (c / N) N (fun _ => 1) (ramanujanLogDivisorJet m) / c

/-- The two nonpolar receiving charges cancel at every sublinear growing overlap. -/
theorem tendsto_terminalFullCenterJetPair_nonpolar
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m : ℕ} (hm : 2 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => terminalFullCenterJetPair φ h (c N) N m) atTop (𝓝 0) := by
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x y, |logProfile h x - logProfile h y| ≤
      ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    abs_logProfile_sub_le hh hsupp hA hBF hLF
  have hc' := (tendsto_terminal_fullNonpolarCenter_pair
    (fun x => abs_logProfile_le hBF x)
    (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A)) hFL hm).const_mul
    ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2)
  have hj := tendsto_terminal_nearDivisorJet_mean hφ hφsupp hM
    (fun x => abs_logProfile_le hBF x)
    (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A))
    (fun x _ y _ => hFL x y) (by omega : 0 < m) hc hcinf hcN
  have ht := hc'.add hj
  have hz : ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        (-vonMangoldt m * ∫ x in (0 : ℝ)..1, logProfile h x) +
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * vonMangoldt m *
        (∫ x in (0 : ℝ)..1, logProfile h x) = 0 := by ring
  rw [hz] at ht
  exact ht

/-- The complete terminal pairing retains the full-center and divisor-jet charges together. -/
theorem complete_terminal_conductor_pair_eq_channels {φ h : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N m : ℕ}
    (hN : 2 ≤ N) (hm : 0 < m) :
    Real.sqrt (Real.log N) / c *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N),
        horizonProfileVector (horizonWeights h N) N⟫ =
      -(Real.sqrt (Real.log N) / c *
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N,
          horizonProfileVector (horizonWeights h N) N⟫) +
      Real.sqrt (Real.log N) / c *
        ⟪completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N,
          horizonProfileVector (horizonWeights h N) N⟫ +
      Real.sqrt (Real.log N) / c *
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N),
          horizonProfileVector (horizonWeights h N) N⟫ +
      Real.sqrt (Real.log N) / c *
        ⟪(completeWeilSelfFinitePart φ c + ramanujanAdjunctionEnergy m -
            Real.eulerMascheroniConstant) • normalizedRamanujanHorizonVector m N,
          horizonProfileVector (horizonWeights h N) N⟫ +
      (terminalFullCenterJetPair φ h c N m + terminalConductorGammaCenterPair φ h c N m -
        (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / Real.sqrt n *
          actualExteriorDownwardRow (atomDilate φ (c / N)) N m n) / c -
        (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / n * upwardModeRow φ c N m n) / c) /
        Real.sqrt (m.totient : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have htot : Real.sqrt (m.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm)).ne'
  let u : ℕ → ℝ := fun n => logProfile h ((n : ℝ) / N)
  let x := horizonProfileVector (fun n => u n / Real.sqrt n) N
  have hx : horizonProfileVector (horizonWeights h N) N = x :=
    horizonProfileVector_horizonWeights_eq_terminal h hN1
  have hn := sqrt_log_mul_terminal_row_pair hL u (nearGammaDownwardRow φ c N m)
  change Real.sqrt (Real.log N) * ⟪normalizedNearGammaDownwardVector φ c N m, x⟫ = _ at hn
  rw [sum_terminal_nearGammaDownwardRow_eq (φ := φ) (F := logProfile h) hc hN1 m] at hn
  have he := sqrt_log_mul_terminal_row_pair hL u
    (actualExteriorDownwardRow (atomDilate φ (c / N)) N m)
  change Real.sqrt (Real.log N) * ⟪normalizedExteriorDownwardVector φ c N m, x⟫ = _ at he
  have hnear := sqrt_log_mul_terminal_nearCenter_pair (φ := φ) (c := c) hm hL u
  have hfar := sqrt_log_mul_terminal_separatedCross_pair (φ := φ) (c := c) hm hL u
  have hfull := sqrt_log_mul_terminal_fullCenter_conductor_pair hm hL (completeWeilPoleShift φ c) u
  have hup := sqrt_log_mul_terminal_upward_pair hφ hsupp hM hc hN hm u
  have hall := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex N) =>
    Real.sqrt (Real.log N) * ⟪v, x⟫)
    (completeWeilMatrix_ramanujan_eq_terminal_channels hφ hsupp hM hc hN1 hm)
  rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc N m] at hall
  simp only [inner_add_left, inner_sub_left, inner_neg_left, real_inner_smul_left,
    mul_add, mul_sub, mul_neg] at hall
  have hscale : ∀ z : ℝ, Real.sqrt (Real.log N) * ((Real.sqrt (m.totient : ℝ))⁻¹ * z) =
      (Real.sqrt (m.totient : ℝ))⁻¹ * (Real.sqrt (Real.log N) * z) := fun _ => by ring
  simp only [hscale] at hall
  rw [hn, he, hnear, hfar, hfull, hup] at hall
  simp only [hx]
  calc
    _ = (Real.sqrt (Real.log N) *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N),
          x⟫) / c := by ring
    _ = _ := by
      rw [hall]
      simp only [inner_sub_left, real_inner_smul_left]
      unfold terminalFullCenterJetPair terminalConductorGammaCenterPair completeWeilPoleShift
      dsimp only [u]
      field_simp [hc.ne', hM.ne', htot] <;> ring

/-- Every fixed nonpolar conductor has zero complete source on a window above half the horizon. -/
theorem tendsto_complete_terminal_nonpolar_above_half
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {m : ℕ} (hm : 2 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) (normalizedRamanujanHorizonVector m N),
        horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 0) := by
  have hm0 : 0 < m := by omega
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
  have hcenter := tendsto_terminalFullCenterJetPair_nonpolar hφ hφsupp hM hh hA hsupp
    hm hc0 hcinf hcN
  have hg := tendsto_terminalConductorGammaCenterPair_nonpolar hφ hφsupp hM hh hA hsupp
    hm hc hcinf hcN he
  have hr := tendsto_terminal_ratioPrime_residual_pairing hsupp hBF hm0 hcinf
  have hs := tendsto_terminal_selfError_pairing hφ hφsupp hM hsupp hBF hm0 hc hR hcrit
  have hp := tendsto_terminal_poleError_pairing hφ hφsupp hM hsupp hBF hm0 hc hR hcrit
  have hd := tendsto_terminal_referenceDiagonal_pairing (φ := φ) hsupp hBF hm0 hc0 hcinf
    (ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant)
  simp only [← add_sub_assoc] at hd
  have hext : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / Real.sqrt n *
        actualExteriorDownwardRow (atomDilate φ (c N / N)) N m n) / c N) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_terminal_exteriorDownward_pairing_eq_zero
      hφ hφsupp hη hhigh hc hcN] with N hN
    rw [hN m, zero_div]
  have hup : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) / n *
        upwardModeRow φ (c N) N m n) / c N) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_terminal_upward_pairing_eq_zero
      hφ hφsupp hδ hlow hc0 hcN] with N hN
    rw [hN m, zero_div]
  have hcore := (((hcenter.add hg).sub hext).sub hup).div_const (Real.sqrt (m.totient : ℝ))
  have ht := (((hr.neg.add hs).add hp).add hd).add hcore
  simp only [neg_zero, zero_add, sub_zero, zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (complete_terminal_conductor_pair_eq_channels hφ hφsupp hM (hc0 N) hN hm0).symm

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminalFullCenterJetPair_nonpolar
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.complete_terminal_conductor_pair_eq_channels
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_complete_terminal_nonpolar_above_half
