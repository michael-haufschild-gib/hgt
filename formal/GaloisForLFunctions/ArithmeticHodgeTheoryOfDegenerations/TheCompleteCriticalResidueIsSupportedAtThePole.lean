import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingGammaCenterResidueIsSupportedAtThePole
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCanonicalCriticalClockEntersFromTheNegativeSide
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals

/-!
# The complete critical residue is supported at the pole

The seven-channel complete Weil identity has a signed fixed-conductor
limit. The ratio-prime, self and pole replacement errors vanish; the
Gamma-center and upward-prime residues retain the polar genus constant.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The ratio-prime residual disappears at growing overlap after critical scaling. -/
theorem tendsto_scaled_ratioPrime_residual {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_primeResidual_bilinear_log_free
  have hlim : Tendsto (fun N : ℕ =>
      (C * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m)) / c N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcinf
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  change 0 < Real.log (N : ℝ) at hL
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hL (hc N))]
  exact (mul_le_mul_of_nonneg_left (hb m l N hm hl) (div_nonneg hL.le (hc N).le)).trans_eq
    (by field_simp [hL.ne', (hc N).ne'])

private theorem eventually_clock_le_horizon {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, c N ≤ N := by
  have hw := tendsto_overlap_width_of_fourth_log_error hc he
  filter_upwards [eventually_ge_atTop 1,
    hw.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_one hN0).mp h.le

private theorem eventually_norm_normalizedRamanujanHorizonVector_le_two {m : ℕ}
    (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ‖normalizedRamanujanHorizonVector m N‖ ≤ 2 := by
  have h : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖ ^ 2)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [real_inner_self_eq_norm_sq, if_true] using
      tendsto_normalizedRamanujanHorizonVector_gram hm hm
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 4))] with N hN
  have hn := norm_nonneg (normalizedRamanujanHorizonVector m N)
  nlinarith only [hN, hn]

/-- The self replacement has zero critical-scale pairing on fixed conductors. -/
theorem tendsto_scaled_selfError_pairing {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪completeWeilSelfError φ (c N) N • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫) atTop (𝓝 0) := by
  let B : ℝ := Real.exp (1 / 2) / 2
  let D : ℝ := 4 * B
  have hlim := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).const_mul D
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1, eventually_clock_le_horizon hc he,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_norm_normalizedRamanujanHorizonVector_le_two hm,
    eventually_norm_normalizedRamanujanHorizonVector_le_two hl]
    with N hN hcN hL hvm hvl
  change 1 ≤ Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  have hinner : |⟪normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector l N⟫| ≤ 4 := by
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul hvm hvl (norm_nonneg _) (by positivity)).trans_eq (by ring))
  rw [Real.norm_eq_abs, real_inner_smul_left, abs_mul, abs_of_pos (div_pos hL0 hc0), abs_mul]
  calc
    _ ≤ (Real.log N / c N) * ((B * (c N / N)) *
        4) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc0 hN hcN)
          hinner (abs_nonneg _) (by dsimp only [B]; positivity)) (by positivity)
    _ = D * (Real.log N / N) := by
      dsimp only [D]
      field_simp [hc0.ne']

/-- The pole-moment replacement has zero critical-scale pairing on fixed conductors. -/
theorem tendsto_scaled_poleError_pairing {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_poleError_quadratic_conductor_bound hφ hsupp hM
  let D : ℝ := 2 * Real.sqrt (C * m)
  have hlim := he.const_mul D
  simp only [mul_zero] at hlim
  have he1 := tendsto_fourth_overlap_log_error_of_sq hc he
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1, eventually_clock_le_horizon hc he1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_norm_normalizedRamanujanHorizonVector_le_two hl]
    with N hN hcN hL hvl
  change 1 ≤ Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  let u := Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ (c N) N)
    (normalizedRamanujanHorizonVector m N)
  have hu : ‖u‖ ≤ Real.sqrt (C * m) * c N ^ 5 * (Real.log N / N) := by
    have hs : (Real.sqrt (C * m) * c N ^ 5 * (Real.log N / N)) ^ 2 =
        C * m * c N ^ 10 * (Real.log N / N) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hpos : 0 ≤ Real.sqrt (C * m) * c N ^ 5 * (Real.log N / N) := by positivity
    have hsq := hb m hm (c N) (hc N) N hN hL hcN
    change ‖u‖ ^ 2 ≤ _ at hsq
    nlinarith only [hsq, hs, hpos, norm_nonneg u]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hL0 hc0)]
  calc
    _ ≤ (Real.log N / c N) *
        ((Real.sqrt (C * m) * c N ^ 5 * (Real.log N / N)) * 2) :=
      mul_le_mul_of_nonneg_left
        ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul hu hvl (norm_nonneg _) (by positivity))) (by positivity)
    _ = D * (c N ^ 4 * Real.log N ^ 2 / N) := by
      dsimp only [D]
      field_simp [hc0.ne']

/-- The complete fixed-conductor residue at growing overlap is supported at the pole. -/
theorem tendsto_scaled_completeWeil_residual {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫) atTop
      (𝓝 (if m = 1 ∧ l = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0)) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hp := tendsto_scaled_ratioPrime_residual hm hl hc0 hcinf
  have hs := tendsto_scaled_selfError_pairing hφ hsupp hM hm hl hc
    (tendsto_fourth_overlap_log_error_of_sq hc he)
  have hg := tendsto_scaled_gammaCenterResidual hφ hsupp hM hm hl hc hcinf he
  have hq := tendsto_scaled_poleError_pairing hφ hsupp hM hm hl hc he
  have hu := tendsto_upwardPrime_residual_signed_limit hφ hsupp hM hc hcinf he hm hl
  have hsum := (((hp.neg.add hs).add hg).add hq).sub hu
  simp only [neg_zero, zero_add, add_zero] at hsum
  have hconst :
      (if m = 1 ∧ l = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (1 - Real.log (4 * Real.pi)) else 0) -
      (if m = 1 ∧ l = 1 then -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (Real.eulerMascheroniConstant + 1) else 0) =
      (if m = 1 ∧ l = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0) := by
    split_ifs <;> ring
  rw [hconst] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM (hc0 N) hN hm]
  simp only [gammaCenterResidual, inner_sub_left, inner_add_left, inner_neg_left]
  ring

/-- Every positive critical ratio has the same complete signed fixed-pair residue. -/
theorem tendsto_critical_completeWeil_residual {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫) atTop
      (𝓝 (if m = 1 ∧ l = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0)) := by
  exact tendsto_scaled_completeWeil_residual hφ hsupp hM hm hl hc
    (criticalCurve_facts hc hR hcrit).1
    (criticalCurve_pow_log_div_natCast hc hR hcrit 4 2)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_scaled_ratioPrime_residual
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_scaled_selfError_pairing
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_scaled_poleError_pairing
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_critical_completeWeil_residual
