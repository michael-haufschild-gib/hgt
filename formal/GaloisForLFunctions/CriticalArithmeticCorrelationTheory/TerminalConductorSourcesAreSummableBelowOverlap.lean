import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalPoleHasAnIntrinsicCollarCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSignedCriticalResidualIsCompactBelowOverlap

/-!
# Summable inverse-energy terminal sources below overlap

An interior terminal receiver has zero lower-half prefix. The dual
seventh collar estimate and the actual seventh-power conductor floor
therefore give a summable fifth-power envelope for its mixed residual
energy, at every positive critical ratio.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A terminal receiver above half the horizon has an exactly vanishing lower prefix. -/
theorem terminal_window_half_prefix_eq_zero {h : ℝ → ℝ}
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → logProfile h x = 0)
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 (N / 2),
      primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) n ^ 2) = 0 := by
  apply sum_eq_zero
  intro n hn
  have hnN : n ∈ Icc 1 N := mem_Icc.mpr
    ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.div_le_self N 2)⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hhalf : 2 * n ≤ N := by have := (mem_Icc.mp hn).2; omega
  have hhalfR : (2 : ℝ) * n ≤ N := by exact_mod_cast hhalf
  have hx : (n : ℝ) / N ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hN0).mpr
    linarith only [hhalfR]
  rw [horizonProfileVector_horizonWeights_eq_terminal h hN, primeHorizonExtension, dif_pos hnN]
  change (logProfile h ((n : ℝ) / N) / Real.sqrt n) ^ 2 = 0
  rw [hlow _ hx, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Critical clocks eventually satisfy every collar hypothesis simultaneously. -/
theorem eventually_critical_half_collar_admissible {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧ 1 ≤ Real.log N ∧
      4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N ∧
      4 * (linearNearRowRadius (c N) + 1) ^ 2 ≤ N ∧ c N ^ 4 ≤ N ∧
      2 * linearPrimeStrip (c N) ≤ N / 2 := by
  have hlarge := (criticalCurve_pow_log_div_natCast hc hR hcrit 2 0).const_mul
    (4 * (Real.exp 1 + 3) ^ 2)
  have hstrip := (criticalCurve_pow_log_div_natCast hc hR hcrit 1 0).const_mul
    (4 * (Real.exp 1 + 1))
  simp only [pow_zero, pow_one, mul_one, mul_zero] at hlarge hstrip
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_below_overlap_pair_admissible hc hR hcrit,
    hlarge.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hstrip.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN hL ha hlargeN hstripN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨_, _, hrad, hc4⟩ := ha 1 1 (by simpa only [Nat.cast_one] using hc N)
    (by simpa only [Nat.cast_one] using hc N)
  have hlarge' : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N := by
    apply (div_le_one hN0).mp
    simpa only [mul_div_assoc] using hlargeN.le
  have hstrip' : 4 * (Real.exp 1 + 1) * c N ≤ N := by
    apply (div_le_one hN0).mp
    simpa only [mul_div_assoc] using hstripN.le
  have hstripR : (4 : ℝ) * linearPrimeStrip (c N) ≤ N :=
    (mul_le_mul_of_nonneg_left (linearPrimeStrip_le (hc N)) (by norm_num)).trans
      (by simpa only [mul_assoc] using hstrip')
  have hstripNat : 4 * linearPrimeStrip (c N) ≤ N := by exact_mod_cast hstripR
  exact ⟨hN, hL, hlarge', hrad, hc4, by omega⟩

/-- The inverse-energy mixed residuals below overlap have one summable fifth-power envelope. -/
theorem exists_terminal_residual_inverse_energy_envelope
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      0 < m → (m : ℝ) ≤ c N →
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline (c N) m •
              normalizedRamanujanHorizonVector m N,
          horizonProfileVector (horizonWeights h N) N⟫ ^ 2 /
          (c N * completedConductorEnergy tiltedUnitSpline (c N) m) ≤ C / (m : ℝ) ^ 5 := by
  obtain ⟨K, hK, hbound⟩ := exists_completeWeil_dualSeventh_conductor_residual_log_free
    contDiff_tiltedUnitSpline tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos
  let T : ℝ := 128 * (B ^ 2 * Real.exp A + 1)
  let κ : ℝ := tiltedSplineSpectralFloorConstant
  have hT : 0 < T := by dsimp only [T]; positivity
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  refine ⟨2 * K * T * (R + 3) / κ, by positivity, ?_⟩
  have hsmall₁ := criticalCurve_pow_log_div_natCast hc hR hcrit 9 1
  have hsmall₂ := (criticalCurve_pow_log_div_natCast hc hR hcrit 8 1).pow 2
  simp only [pow_one] at hsmall₁ hsmall₂
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsmall₂
  filter_upwards [eventually_critical_half_collar_admissible hc hR hcrit,
    hcrit.eventually (gt_mem_nhds (lt_add_one R)),
    hsmall₁.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmall₂.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N ha hratio hsmall₁N hsmall₂N
  obtain ⟨hN, hL1, hlarge, hrad, hc4, hstrip⟩ := ha
  intro m hm hmc
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  let r := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N
  let x := horizonProfileVector (horizonWeights h N) N
  let E := completedConductorEnergy tiltedUnitSpline (c N) m
  have hE := seventh_mul_completedConductorEnergy_ge_below_overlap hc0 hm hmc
  change κ * (m : ℝ) ^ 7 ≤ c N ^ 7 * E at hE
  have hE0 : 0 < c N ^ 7 * E := (mul_pos hκ (pow_pos hm0 7)).trans_le hE
  have htop : topCollarSeventhMass (N / 2) N (primeHorizonExtension x) ≤ T := by
    have ht := (topCollarSeventhMass_half_le_norm_sq N x).trans
      (mul_le_mul_of_nonneg_left (horizon_window_norm_sq_le hsupp hB hN) (by norm_num))
    exact ht.trans (by dsimp only [T]; linarith)
  have hcs := inner_sq_le_prefix_add_topCollarSeventh (Nat.div_le_self N 2) r x
  rw [terminal_window_half_prefix_eq_zero hlow hN, mul_zero, zero_add] at hcs
  have hd := hbound hm (hc N) hL1 hlarge hrad hc4 hstrip
  change topCollarDualSeventhMass (N / 2) N r ≤ _ at hd
  have hpair : ⟪r, x⟫ ^ 2 ≤ 2 * (K * (m : ℝ) ^ 2 *
      (c N ^ 2 / Real.log N + c N ^ 3 * Real.log N / N +
        c N ^ 10 * (Real.log N / N) ^ 2)) * T := by
    exact hcs.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hd (by norm_num)) htop
      (topCollarSeventhMass_nonneg _ _ _) (by positivity))
  have hscaled : c N ^ 6 * ⟪r, x⟫ ^ 2 ≤
      2 * K * T * (m : ℝ) ^ 2 * (R + 3) := by
    calc
      _ ≤ c N ^ 6 * (2 * (K * (m : ℝ) ^ 2 *
          (c N ^ 2 / Real.log N + c N ^ 3 * Real.log N / N +
            c N ^ 10 * (Real.log N / N) ^ 2)) * T) :=
        mul_le_mul_of_nonneg_left hpair (pow_nonneg hc0.le 6)
      _ = 2 * K * T * (m : ℝ) ^ 2 * (c N ^ 8 / Real.log N +
          c N ^ 9 * Real.log N / N + (c N ^ 8 * Real.log N / N) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by linarith only [hratio, hsmall₁N, hsmall₂N]) (by positivity)
  change ⟪r, x⟫ ^ 2 / (c N * E) ≤ _
  calc
    _ = (c N ^ 6 * ⟪r, x⟫ ^ 2) / (c N ^ 7 * E) := by
      have heq : c N ^ 7 * E = c N ^ 6 * (c N * E) := by ring
      rw [heq, mul_div_mul_left _ _ (pow_ne_zero 6 hc0.ne')]
    _ ≤ (2 * K * T * (m : ℝ) ^ 2 * (R + 3)) / (κ * (m : ℝ) ^ 7) :=
      (div_le_div_of_nonneg_right hscaled hE0.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hE)
    _ = _ := by field_simp [hκ.ne', hm0.ne']

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_terminal_residual_inverse_energy_envelope
