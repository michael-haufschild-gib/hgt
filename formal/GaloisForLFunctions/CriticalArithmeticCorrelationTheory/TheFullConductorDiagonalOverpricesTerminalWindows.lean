import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TerminalWindowsHaveExplicitFullConductorCoordinates
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePoleCorrectorRetainsItsSignedWindowBenefit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolarSourceIsNonzero
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCanonicalCriticalClockEntersFromTheNegativeSide
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.CoprimeFourierOrder
import GaloisForLFunctions.RHTower.NicolasTotientLandau

/-!
# The full conductor diagonal overprices terminal windows

The explicit conductor coordinates at the top of the horizon retain a
totient-weighted diagonal cost. Landau's bound and the logarithmic
conductor reserve make this cost dominate the overlap scale. The actual
complete energy of the reconstructed fixed window remains on that scale.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The diagonal conductor cost of the explicit finite reconstruction. -/
def terminalFullConductorDiagonal (f : ℕ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, completedConductorEnergy tiltedUnitSpline c m *
    terminalNormalizedConductorCoordinate f N m ^ 2

theorem terminalFullConductorDiagonal_nonneg (f : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    0 ≤ terminalFullConductorDiagonal f c N :=
  sum_nonneg fun m hm => mul_nonneg
    (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
      integral_tiltedUnitSpline_sq_pos hc (mem_Icc.mp hm).1) (sq_nonneg _)

/-- Horizon-sized conductors keep half the horizon logarithm as energy. -/
theorem eventually_terminal_conductor_energy_ge_log
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ Icc 1 N, N < 2 * m →
      Real.log N / 2 ≤ completedConductorEnergy tiltedUnitSpline (c N) m := by
  let Cφ := min 0 (completeWeilSelfFinitePart tiltedUnitSpline 1)
  have hpow := criticalCurve_pow_log_div_natCast hc hR hcrit 4 0
  simp only [pow_zero, mul_one] at hpow
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    hpow.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlog.eventually_ge_atTop (8 * Real.log 2), hlog.eventually_ge_atTop (-8 * Cφ)]
    with N hN hp hL2 hLC
  intro m hm hhalf
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hpowN : c N ^ 4 ≤ N := (div_le_one hN0).mp hp.le
  have hlogc := Real.log_le_log (pow_pos hc0 4) hpowN
  rw [Real.log_pow] at hlogc
  norm_num only [Nat.cast_ofNat] at hlogc
  have hmhalf : (N : ℝ) / 2 ≤ m := by
    have hh : (N : ℝ) < 2 * m := by exact_mod_cast hhalf
    linarith only [hh]
  have hlogm := Real.log_le_log (div_pos hN0 two_pos) hmhalf
  rw [Real.log_div hN0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlogm
  have hE := log_conductor_sub_log_overlap_le_completedEnergy contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hc0 (mem_Icc.mp hm).1
  change Real.log (m : ℝ) - Real.log (c N) + Cφ ≤ _ at hE
  change 8 * Real.log 2 ≤ Real.log (N : ℝ) at hL2
  change -8 * Cφ ≤ Real.log (N : ℝ) at hLC
  linarith only [hlogc, hlogm, hE, hL2, hLC]

/-- A deliberately weaker logarithmic version of Landau's reserve is uniform in the top half. -/
theorem eventually_terminal_totient_log_reserve :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ Icc 1 N, N < 2 * m →
      (m : ℝ) ≤ (Real.exp Real.eulerMascheroniConstant + 1) * Real.log N * m.totient := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (_root_.RHTower.eventually_div_totient_le_landau (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (max 4 (2 * M))] with N hN
  intro m hm hhalf
  have hmM : M ≤ m := by have := (le_max_right 4 (2 * M)).trans hN; omega
  have hm2 : 2 ≤ m := by have := (le_max_left 4 (2 * M)).trans hN; omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hφ : (0 : ℝ) < m.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hll : Real.log (Real.log (m : ℝ)) ≤ Real.log (N : ℝ) := by
    have h₁ := Real.log_le_sub_one_of_pos hlogm
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hm).2
    have h₂ := Real.log_le_log hm0 hmN
    linarith only [h₁, h₂]
  have hC : 0 ≤ Real.exp Real.eulerMascheroniConstant + 1 := by positivity
  have hdiv := (hM m hmM).trans (mul_le_mul_of_nonneg_left hll hC)
  exact (div_le_iff₀ hφ).mp hdiv

/-- Every terminal datum has an explicit full-conductor diagonal cost at least a logarithmic
multiple of its physical squared mass, uniformly over the datum. -/
theorem eventually_terminalFullConductorDiagonal_ge_log_mass
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, ∀ f : ℕ → ℝ, (∀ n, 2 * n ≤ N → f n = 0) →
      Real.log N / (2 * (Real.exp Real.eulerMascheroniConstant + 1)) *
        (∑ n ∈ Icc 1 N, f n ^ 2 / n) ≤ terminalFullConductorDiagonal f (c N) N := by
  filter_upwards [eventually_terminal_conductor_energy_ge_log hc hR hcrit,
    eventually_terminal_totient_log_reserve] with N hE hφ
  intro f hlow
  unfold terminalFullConductorDiagonal
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hEnn := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos hc0 (mem_Icc.mp hm).1
  by_cases hf : f m = 0
  · simp only [hf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, mul_zero]
    exact mul_nonneg hEnn (sq_nonneg _)
  have hhalf : N < 2 * m := by
    by_contra hh
    exact hf (hlow m (le_of_not_gt hh))
  let C := Real.exp Real.eulerMascheroniConstant + 1
  let E := completedConductorEnergy tiltedUnitSpline (c N) m
  have hC : 0 < C := by dsimp only [C]; positivity
  have hφ0 : (0 : ℝ) ≤ m.totient := Nat.cast_nonneg _
  have hEL : Real.log N ≤ 2 * E := by have := hE m hm hhalf; dsimp only [E]; linarith only [this]
  have hcoeff : (m : ℝ) ≤ 2 * C * E * m.totient := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEL hC.le) hφ0
    exact (hφ m hm hhalf).trans (hh.trans_eq (by dsimp only [C]; ring))
  rw [terminalNormalizedConductorCoordinate_sq_above_half f hm hhalf]
  change Real.log N / (2 * C) * (f m ^ 2 / m) ≤ E * (Real.log N * m.totient * f m ^ 2 / (m : ℝ) ^ 2)
  calc
    _ = (Real.log N * f m ^ 2 * m) / (2 * C * (m : ℝ) ^ 2) := by
      field_simp [hC.ne', hm0.ne']
      <;> ring
    _ ≤ (Real.log N * f m ^ 2 * (2 * C * E * m.totient)) /
        (2 * C * (m : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff
        (mul_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))) (by positivity)
    _ = _ := by field_simp [hC.ne', hm0.ne'] <;> ring

/-- The diagonal cost of a fixed logarithmic terminal window. -/
def terminalWindowFullConductorDiagonal (h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  terminalFullConductorDiagonal (fun n => logProfile h ((n : ℝ) / N)) c N

private theorem terminal_window_mass_eq (h : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, logProfile h ((n : ℝ) / N) ^ 2 / n) =
      ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 := by
  have hh := congrArg (fun x : EuclideanSpace ℝ (PrimeHorizonIndex N) => ‖x‖ ^ 2)
    (horizonProfileVector_horizonWeights_eq_terminal h hN)
  rw [horizonProfileVector_norm_sq, horizonProfileVector_norm_sq] at hh
  rw [hh]
  exact sum_congr rfl fun n _ => by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The overlap scale is negligible compared with the explicit full-conductor diagonal cost. -/
theorem terminalWindowFullConductorDiagonal_positive_and_reciprocal_vanishes
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hne : ∃ y, h y ≠ 0) (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    (∀ᶠ N : ℕ in atTop, 0 < terminalWindowFullConductorDiagonal h (c N) N) ∧
      Tendsto (fun N : ℕ => c N / terminalWindowFullConductorDiagonal h (c N) N)
        atTop (𝓝 0) := by
  let C := Real.exp Real.eulerMascheroniConstant + 1
  let M := ∫ y, h y ^ 2
  have hC : 0 < C := by dsimp only [C]; positivity
  have hM : 0 < M := by
    obtain ⟨y, hy⟩ := hne
    have hcompact : HasCompactSupport (fun y => h y ^ 2) := by
      apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-A) 0))
      intro t ht
      rw [hsupp t ht, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact (hh.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcompact (fun t => sq_nonneg (h t)) (pow_ne_zero 2 hy)
  have hmass := tendsto_sum_horizonWeights_sq hh.continuous hsupp hA
  have hdiag : ∀ᶠ N : ℕ in atTop,
      0 < Real.log (N : ℝ) ∧ Real.log N * M / (4 * C) ≤
        terminalWindowFullConductorDiagonal h (c N) N := by
    filter_upwards [eventually_terminalFullConductorDiagonal_ge_log_mass hc hR hcrit,
      eventually_ge_atTop 2, hmass.eventually (lt_mem_nhds (half_lt_self hM))]
      with N hb hN hmassN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hl : ∀ n : ℕ, 2 * n ≤ N → logProfile h ((n : ℝ) / N) = 0 := by
      intro n hn
      apply hlow
      apply (div_le_iff₀ hN0).mpr
      have hh : (2 : ℝ) * n ≤ N := by exact_mod_cast hn
      linarith only [hh]
    have hh := hb (fun n => logProfile h ((n : ℝ) / N)) hl
    rw [terminal_window_mass_eq h (by omega : 1 ≤ N)] at hh
    refine ⟨hL, ?_⟩
    calc
      _ = Real.log N / (2 * C) * (M / 2) := by ring
      _ ≤ Real.log N / (2 * C) * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 :=
        mul_le_mul_of_nonneg_left hmassN.le (by positivity)
      _ ≤ _ := hh
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < terminalWindowFullConductorDiagonal h (c N) N := by
    filter_upwards [hdiag] with N hN
    exact (div_pos (mul_pos hN.1 hM) (mul_pos (by norm_num) hC)).trans_le hN.2
  refine ⟨hpos, ?_⟩
  have hclog : Tendsto (fun N : ℕ => c N / Real.log N) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => div_nonneg (zero_le_one.trans (hc N)) (Real.log_natCast_nonneg N))
      (fun N => ?_) (criticalCurve_sq_div_log hc hR hcrit)
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    nlinarith only [hc N]
  have hlim := hclog.const_mul (4 * C / M)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
    (zero_le_one.trans (hc N)) (terminalFullConductorDiagonal_nonneg _
      (zero_lt_one.trans_le (hc N)) N)) _ hlim
  filter_upwards [hdiag] with N hN
  have hden : 0 < Real.log N * M / (4 * C) :=
    div_pos (mul_pos hN.1 hM) (mul_pos (by norm_num) hC)
  calc
    _ ≤ c N / (Real.log N * M / (4 * C)) :=
      div_le_div_of_nonneg_left (zero_le_one.trans (hc N)) hden hN.2
    _ = _ := by field_simp [hN.1.ne', hM.ne', hC.ne'] <;> ring

/-- The literal complete energy loses every positive fixed comparison with the full conductor
diagonal, for any nonzero fixed interior terminal window and every critical ratio. -/
theorem tendsto_complete_terminal_energy_div_full_conductor_diagonal
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hne : ∃ y, h y ≠ 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (horizonProfileVector (horizonWeights h N) N),
        horizonProfileVector (horizonWeights h N) N⟫ /
          terminalWindowFullConductorDiagonal h (c N) N) atTop (𝓝 0) := by
  have hsmall := (terminalWindowFullConductorDiagonal_positive_and_reciprocal_vanishes
    hh hA hsupp hne (fun x hx => hlow x (hx.trans hδ.le)) hc hR hcrit).2
  have henergy := tendsto_complete_window_add_pole_corrector hh hA hsupp
    hδ hη hlow hhigh hc hR hcrit 0
  simp only [zero_mul, zero_smul, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at henergy
  have ht := henergy.mul hsmall
  simp only [mul_zero] at ht
  apply ht.congr
  intro N
  have hc0 : c N ≠ 0 := (zero_lt_one.trans_le (hc N)).ne'
  simp only [div_eq_mul_inv]
  rw [show (c N)⁻¹ *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (horizonProfileVector (horizonWeights h N) N),
        horizonProfileVector (horizonWeights h N) N⟫ *
      (c N * (terminalWindowFullConductorDiagonal h (c N) N)⁻¹) =
      ((c N)⁻¹ * c N) *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (horizonProfileVector (horizonWeights h N) N),
          horizonProfileVector (horizonWeights h N) N⟫ *
          (terminalWindowFullConductorDiagonal h (c N) N)⁻¹ by ring,
    inv_mul_cancel₀ hc0, one_mul]

/-- The full conductor packet violates every fixed positive diagonal fraction, with an explicit
terminal reconstruction as its counterfamily. -/
theorem eventually_exists_full_packet_below_diagonal_fraction
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hne : ∃ y, h y ≠ 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, ∃ b : ℕ → ℝ,
      let D := ∑ m ∈ Icc 1 N, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2
      let y := ∑ m ∈ Icc 1 N, b m • normalizedRamanujanHorizonVector m N
      b = terminalNormalizedConductorCoordinate (fun n => logProfile h ((n : ℝ) / N)) N ∧
        0 < D ∧ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, y⟫ < κ * D := by
  have hpos := (terminalWindowFullConductorDiagonal_positive_and_reciprocal_vanishes
    hh hA hsupp hne (fun x hx => hlow x (hx.trans hδ.le)) hc hR hcrit).1
  have hlim := tendsto_complete_terminal_energy_div_full_conductor_diagonal hh hA hsupp hne
    hδ hη hlow hhigh hc hR hcrit
  filter_upwards [hpos, hlim.eventually (gt_mem_nhds hκ), eventually_ge_atTop 2]
    with N hD hbound hN
  let f : ℕ → ℝ := fun n => logProfile h ((n : ℝ) / N)
  have hf : ∀ n, 2 * n ≤ N → f n = 0 := by
    intro n hn
    apply hlow
    apply le_trans _ hδ.le
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    apply (div_le_iff₀ hN0).mpr
    have hh : (2 : ℝ) * n ≤ N := by exact_mod_cast hn
    linarith only [hh]
  refine ⟨terminalNormalizedConductorCoordinate f N, rfl, hD, ?_⟩
  have hy := sum_terminalNormalizedConductorCoordinate_smul hN hf
  change (∑ m ∈ Icc 1 N, terminalNormalizedConductorCoordinate f N m •
    normalizedRamanujanHorizonVector m N) =
      horizonProfileVector (fun n => logProfile h ((n : ℝ) / N) / Real.sqrt n) N at hy
  rw [← horizonProfileVector_horizonWeights_eq_terminal h (by omega : 1 ≤ N)] at hy
  rw [hy]
  exact (div_lt_iff₀ hD).mp hbound

/-- At every positive critical ratio, even nonnegative conductor coefficients admit no fixed
positive diagonal energy comparison. One compact terminal spline supplies the counterfamily. -/
theorem full_horizon_has_no_fixed_conductor_diagonal_floor
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, ∃ b : ℕ → ℝ,
      let D := ∑ m ∈ Icc 1 N, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2
      let y := ∑ m ∈ Icc 1 N, b m • normalizedRamanujanHorizonVector m N
      (∀ m, 0 ≤ b m) ∧ 0 < D ∧
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, y⟫ < κ * D := by
  have hne : ∃ y, terminalPolarWitness y ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x, terminalPolarWitnessLinear x ≠ 0 := by
      by_contra hn
      push Not at hn
      have hh := integral_terminalPolarWitnessLinear_pos
      simp only [hn, intervalIntegral.integral_zero, lt_self_iff_false] at hh
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num)
      (terminalPolarWitnessLinear_support hx).1
    refine ⟨Real.log x, ?_⟩
    simpa only [terminalPolarWitness, Real.exp_log hx0] using hx
  have hev := eventually_exists_full_packet_below_diagonal_fraction contDiff_terminalPolarWitness
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) terminalPolarWitness_window_support hne
    (by norm_num : (1 / 2 : ℝ) < 253 / 256) (by norm_num : (511 / 512 : ℝ) < 1)
    (fun x hx => by rw [logProfile_terminalPolarWitness]; exact terminalPolarWitnessLinear_eq_zero_below x hx)
    (fun x hx => by rw [logProfile_terminalPolarWitness]; exact terminalPolarWitnessLinear_eq_zero_above x hx)
    hc hR hcrit hκ
  filter_upwards [hev] with N hN
  obtain ⟨b, hb, hD, hbound⟩ := hN
  refine ⟨b, ?_, hD, hbound⟩
  intro m
  rw [hb]
  apply terminalNormalizedConductorCoordinate_nonneg
  intro n
  rw [logProfile_terminalPolarWitness]
  exact terminalPolarWitnessLinear_nonneg _

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_terminal_conductor_energy_ge_log
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_terminal_totient_log_reserve
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_terminalFullConductorDiagonal_ge_log_mass
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.terminalWindowFullConductorDiagonal_positive_and_reciprocal_vanishes
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_complete_terminal_energy_div_full_conductor_diagonal
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.full_horizon_has_no_fixed_conductor_diagonal_floor
