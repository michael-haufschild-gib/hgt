import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.WindowConductorCoordinatesVanishUniformly
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCanonicalCriticalClockEntersFromTheNegativeSide
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals

/-!
# Vanishing error channels in a critical conductor-window pairing

Terminal windows have bounded physical norm and inverse-square-root
logarithmic conductor coordinates. These two estimates pay the ratio
prime residual, self and pole replacements, and logarithmic diagonal
after the mixed normalization `sqrt(log N)/c`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis

private theorem tendsto_scaled_window_pairing_of_norm_sq
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {c : ℕ → ℝ} {u : ∀ N, EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu : Tendsto (fun N : ℕ => Real.log N / c N ^ 2 * ‖u N‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪u N, horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 0) := by
  have ht := (hu.mul_const (B ^ 2 * Real.exp A)).sqrt
  simp only [zero_mul, Real.sqrt_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  let x := horizonProfileVector (horizonWeights h N) N
  have hx := horizon_window_norm_sq_le hsupp hB hN
  change ‖x‖ ^ 2 ≤ B ^ 2 * Real.exp A at hx
  have hi := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (u N) x) 2
  rw [sq_abs, mul_pow] at hi
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  calc
    _ ≤ (Real.log N / c N ^ 2) * (‖u N‖ ^ 2 * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (Real.log N / c N ^ 2) * (‖u N‖ ^ 2 * (B ^ 2 * Real.exp A)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (sq_nonneg _)) (by positivity)
    _ = _ := by ring

/-- The ratio-prime residual disappears against every bounded terminal window. -/
theorem tendsto_terminal_ratioPrime_residual_pairing
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {m : ℕ} (hm : 0 < m) {c : ℕ → ℝ} (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N,
        horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 0) := by
  apply tendsto_scaled_window_pairing_of_norm_sq hsupp hB
  obtain ⟨C, hC, hb⟩ := exists_primeResidual_quad_bound
  let D : ℝ := C * ((m : ℝ) * (1 + Real.log m) ^ 2)
  have ht : Tendsto (fun N : ℕ => D / c N ^ 2) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun N : ℕ => D / c N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hcinf
    have ht := hdiv.div_atTop hcinf
    exact ht.congr fun N => by ring
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ ht
  filter_upwards [hcinf.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hc hL
  change 0 < Real.log (N : ℝ) at hL
  exact (mul_le_mul_of_nonneg_left (hb m hm N) (by positivity : 0 ≤ Real.log N / c N ^ 2)).trans_eq
    (by dsimp only [D]; field_simp [hL.ne', hc.ne'] <;> ring)

/-- The scalar self replacement has zero terminal pairing at every positive critical ratio. -/
theorem tendsto_terminal_selfError_pairing
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A B : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {m : ℕ} (hm : 0 < m) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪completeWeilSelfError φ (c N) N • normalizedRamanujanHorizonVector m N,
        horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 0) := by
  apply tendsto_scaled_window_pairing_of_norm_sq hsupp hB
  obtain ⟨C, hC, hb⟩ := exists_selfError_quad_bound hφ hφsupp hM
  have hwidth := criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  simp only [pow_one, pow_zero, mul_one] at hwidth
  have ht₀ := criticalCurve_pow_log_div_natCast hc hR hcrit 0 1
  simp only [pow_zero, one_mul, pow_one] at ht₀
  have ht := (ht₀.div_atTop tendsto_natCast_atTop_atTop).const_mul (C * m)
  simp only [mul_zero] at ht
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ ht
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    hwidth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hL hw
  change 1 ≤ Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN : c N ≤ (N : ℝ) := (div_le_one hN0).mp hw.le
  exact (mul_le_mul_of_nonneg_left (hb m hm N hN hL (c N) hc0 hcN)
    (by positivity : 0 ≤ Real.log N / c N ^ 2)).trans_eq
      (by field_simp [hc0.ne', hN0.ne'] <;> ring)

/-- The pole-moment replacement has zero terminal pairing at every positive critical ratio. -/
theorem tendsto_terminal_poleError_pairing
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A B : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {m : ℕ} (hm : 0 < m) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N),
        horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 0) := by
  apply tendsto_scaled_window_pairing_of_norm_sq hsupp hB
  obtain ⟨C, hC, hb⟩ := exists_poleError_quadratic_conductor_bound hφ hφsupp hM
  have hwidth := criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  simp only [pow_one, pow_zero, mul_one] at hwidth
  have ht := ((criticalCurve_pow_log_div_natCast hc hR hcrit 4 2).pow 2).const_mul (C * m)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at ht
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ ht
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    hwidth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hL hw
  change 1 ≤ Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN : c N ≤ (N : ℝ) := (div_le_one hN0).mp hw.le
  have hp : Real.log N ^ 3 ≤ Real.log N ^ 4 := by
    calc
      _ = Real.log N ^ 3 * 1 := by ring
      _ ≤ Real.log N ^ 3 * Real.log N := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (Real.log N / c N ^ 2) * (C * m * c N ^ 10 * (Real.log N / N) ^ 2) :=
      mul_le_mul_of_nonneg_left (hb m hm (c N) (hc N) N hN hL hcN) (by positivity)
    _ = (C * m * c N ^ 8 / (N : ℝ) ^ 2) * Real.log N ^ 3 := by
      field_simp [hc0.ne', hN0.ne'] <;> ring
    _ ≤ (C * m * c N ^ 8 / (N : ℝ) ^ 2) * Real.log N ^ 4 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C * m * (c N ^ 4 * Real.log N ^ 2 / N) ^ 2 := by ring

/-- The logarithmic reference diagonal also disappears, using the smaller conductor
coordinate of a terminal window rather than its physical norm. -/
theorem tendsto_terminal_referenceDiagonal_pairing
    {φ h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {m : ℕ} (hm : 0 < m) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcinf : Tendsto c atTop atTop) (a : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪(completeWeilSelfFinitePart φ (c N) + a) •
          normalizedRamanujanHorizonVector m N,
        horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 0) := by
  have hd : Tendsto (fun N : ℕ =>
      (completeWeilSelfFinitePart φ (c N) + a) / c N)
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun N : ℕ =>
        (completeWeilSelfFinitePart φ 1 + a) / c N)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcinf
    have ht := hdiv.sub
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcinf)
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    rw [completeWeilSelfFinitePart_eq_at_one_sub_log φ (hc N)]
    dsimp only [Function.comp_def, id]
    ring
  have ht := hd.abs.const_mul (2 * B * Real.exp A)
  simp only [abs_zero, mul_zero] at ht
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [eventually_ge_atTop m,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hmN hL
  change 0 < Real.log (N : ℝ) at hL
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  have hi := abs_horizon_window_conductor_inner_le hsupp hB hm hmN
  rw [real_inner_comm] at hi
  rw [Real.norm_eq_abs, real_inner_smul_left, abs_mul, abs_mul,
    abs_of_pos (div_pos hsL (hc N))]
  calc
    _ ≤ (Real.sqrt (Real.log N) / c N) *
        (|completeWeilSelfFinitePart φ (c N) + a| *
          ((2 * B * Real.exp A) / Real.sqrt (Real.log N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (abs_nonneg _))
        (div_pos hsL (hc N)).le
    _ = (2 * B * Real.exp A) *
        |(completeWeilSelfFinitePart φ (c N) + a) / c N| := by
      rw [abs_div, abs_of_pos (hc N)]
      field_simp [hsL.ne', (hc N).ne'] <;> ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_ratioPrime_residual_pairing
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_selfError_pairing
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_poleError_pairing
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_referenceDiagonal_pairing
