import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalNonpolarSourceAboveHalf
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalExteriorDownwardSourcesDisappear
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalUpwardSourcesHaveFinitePrimeMeans

/-!
# The complete terminal source is polar

Every compact logarithmic window has an exact complete mixed limit at
all positive critical ratios. The polar source retains its boundary
logarithm and a finite prime-power mean. All fixed nonpolar sources
vanish after the full-center and divisor-jet charges cancel.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Every compact terminal window retains the same polar arithmetic source at every critical ratio. -/
theorem tendsto_complete_terminal_pole
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) (normalizedRamanujanHorizonVector 1 N),
        horizonProfileVector (horizonWeights h N) N⟫) atTop
      (𝓝 (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ((∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x) -
          Real.log (2 * Real.pi) * (∫ x in (0 : ℝ)..1, logProfile h x) -
          finitePrimeTerminalMean (logProfile h) ⌈1 / Real.exp (-A - 1)⌉₊))) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0) := by
    have ht := criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
    simp only [pow_zero, mul_one] at ht
    apply squeeze_zero (fun N => div_nonneg
      (mul_nonneg (hc0 N).le (Real.log_nonneg (hc N))) (Nat.cast_nonneg N)) (fun N => ?_) ht
    have hl : Real.log (c N) ≤ c N :=
      (Real.log_le_sub_one_of_pos (hc0 N)).trans (sub_le_self _ zero_le_one)
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (hc0 N).le) (Nat.cast_nonneg N)).trans_eq (by ring)
  obtain ⟨BF, Lh, hBF, hLh⟩ := exists_bound_lipschitz hh hsupp
  let δ : ℝ := Real.exp (-A - 1)
  let K : ℕ := ⌈1 / δ⌉₊
  have hδ : 0 < δ := Real.exp_pos _
  have hlow : ∀ x, x ≤ δ → logProfile h x = 0 := fun x hx =>
    logProfile_eq_zero_of_lt hsupp (hx.trans_lt (Real.exp_lt_exp.mpr (by linarith)))
  have hF1 : logProfile h 1 = 0 :=
    logProfile_eq_zero_of_one_le hsupp (horizon_zero_at_zero hsupp hLh) le_rfl
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x y, |logProfile h x - logProfile h y| ≤
      ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    abs_logProfile_sub_le hh hsupp hA hBF hLF
  have hcRaw := tendsto_terminal_fullPolarCenter_pair
    (fun x => abs_logProfile_le hBF x) (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A))
    (fun x _ y _ => hFL x y) hF1 hδ (fun x _ hx => hlow x hx)
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
  have hext := tendsto_terminal_exteriorDownward_pairing hφ hφsupp hM
    (fun x => abs_logProfile_le hBF x) 1 hc hR hcrit
  have hc4 := criticalCurve_pow_log_div_natCast hc hR hcrit 4 0
  simp only [pow_zero, mul_one] at hc4
  have hup := tendsto_terminal_upwardModeRow_one hφ hφsupp hM hδ
    (fun x => abs_logProfile_le hBF x) hlow
    (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A)) hFL
    (show 1 / δ ≤ (K : ℝ) from Nat.le_ceil _) hc hcinf hc4
  have ht := ((((((hr.neg.add hs).add hp).add hd).add hcenter).add hg).sub hext).sub hup
  simp only [neg_zero, zero_add, add_zero, sub_zero] at ht
  have hconst :
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
          (∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x) +
        (-((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * Real.log (2 * Real.pi) *
          ∫ x in (0 : ℝ)..1, logProfile h x) -
        ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * finitePrimeTerminalMean (logProfile h) K =
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ((∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x) -
          Real.log (2 * Real.pi) * (∫ x in (0 : ℝ)..1, logProfile h x) -
          finitePrimeTerminalMean (logProfile h) K) := by ring
  rw [hconst] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (complete_terminal_pole_pair_eq_channels hφ hφsupp hM (hc0 N) hN).symm

/-- Every fixed nonpolar conductor has zero complete source on every compact terminal window. -/
theorem tendsto_complete_terminal_nonpolar
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
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
  have hext := tendsto_terminal_exteriorDownward_pairing hφ hφsupp hM
    (fun x => abs_logProfile_le hBF x) m hc hR hcrit
  let δ : ℝ := Real.exp (-A - 1)
  have hδ : 0 < δ := Real.exp_pos _
  have hlow : ∀ x, x ≤ δ → logProfile h x = 0 := fun x hx =>
    logProfile_eq_zero_of_lt hsupp (hx.trans_lt (Real.exp_lt_exp.mpr (by linarith)))
  have hc4 := criticalCurve_pow_log_div_natCast hc hR hcrit 4 0
  simp only [pow_zero, mul_one] at hc4
  have hup := tendsto_terminal_upwardModeRow_nonpolar hφ hφsupp hM hδ
    (fun x => abs_logProfile_le hBF x) hlow hm hc hcinf hc4
  have hcore := (((hcenter.add hg).sub hext).sub hup).div_const (Real.sqrt (m.totient : ℝ))
  have ht := (((hr.neg.add hs).add hp).add hd).add hcore
  simp only [neg_zero, zero_add, sub_zero, zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (complete_terminal_conductor_pair_eq_channels hφ hφsupp hM (hc0 N) hN hm0).symm

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_complete_terminal_pole
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_complete_terminal_nonpolar
