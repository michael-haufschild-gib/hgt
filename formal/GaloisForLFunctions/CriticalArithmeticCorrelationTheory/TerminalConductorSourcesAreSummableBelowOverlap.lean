import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalPoleHasAnIntrinsicCollarCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSignedCriticalResidualIsCompactBelowOverlap
import GaloisForLFunctions.CompletedArithmeticForms.ConductorEnergiesHaveAUniformLogarithmicUpperBound

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
  CompletedArithmeticForms

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
    _ = _ := by field_simp [hκ.ne', hm0.ne'] <;> ring

/-- Restoring the conductor-energy diagonal preserves the summable terminal envelope. -/
theorem exists_terminal_complete_inverse_energy_envelope
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      0 < m → (m : ℝ) ≤ c N →
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector m N),
          horizonProfileVector (horizonWeights h N) N⟫ ^ 2 /
          (c N * completedConductorEnergy tiltedUnitSpline (c N) m) ≤ C / (m : ℝ) ^ 5 := by
  obtain ⟨C, hC, hres⟩ := exists_terminal_residual_inverse_energy_envelope hsupp hB hlow hc hR hcrit
  let β := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 5
  let α := 2 * B * Real.exp A
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hB0 : 0 ≤ B := (abs_nonneg (h 0)).trans (hB 0)
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  refine ⟨2 * C + 2 * β * α ^ 2 * (R + 1), by positivity, ?_⟩
  filter_upwards [hres, eventually_critical_half_collar_admissible hc hR hcrit,
    hcrit.eventually (gt_mem_nhds (lt_add_one R))] with N hresN ha hratio
  obtain ⟨hN, hL1, _, _, hc4, _⟩ := ha
  intro m hm hmc
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let v := normalizedRamanujanHorizonVector m N
  let x := horizonProfileVector (horizonWeights h N) N
  let E := completedConductorEnergy tiltedUnitSpline (c N) m
  let p := ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) v, x⟫
  let d := E * ⟪v, x⟫
  have hfloor := seventh_mul_completedConductorEnergy_ge_below_overlap hc0 hm hmc
  have hE0 : 0 < E := by
    have hh := (mul_pos tiltedSplineSpectralFloorConstant_pos (pow_pos hm0 7)).trans_le hfloor
    change 0 < c N ^ 7 * E at hh
    rcases mul_pos_iff.mp hh with hp | hn
    · exact hp.2
    · exact False.elim ((pow_pos hc0 7).not_gt hn.1)
  have hEm : E ≤ β * m := by
    have he := completedConductorEnergy_le_logarithmic_uniform contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (hc N) hm
    have hl : Real.log (m : ℝ) ≤ m :=
      (Real.log_le_sub_one_of_pos hm0).trans (sub_le_self _ zero_le_one)
    have hb := mul_le_mul_of_nonneg_left hm1
      (by positivity : 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| + 3)
    dsimp only [E, β]
    nlinarith only [he, hl, hb]
  have hEc : E / c N ≤ β :=
    (div_le_iff₀ hc0).mpr (hEm.trans (mul_le_mul_of_nonneg_left hmc hβ.le))
  have hmcN : m ≤ N := by
    have hcN : c N ≤ N := by
      have hh := (pow_le_pow_right₀ (hc N) (by norm_num : 1 ≤ 4)).trans hc4
      simpa only [pow_one] using hh
    exact_mod_cast hmc.trans hcN
  have hcoord := abs_horizon_window_conductor_inner_le hsupp hB hm hmcN
  rw [real_inner_comm] at hcoord
  have hcoordsq : ⟪v, x⟫ ^ 2 ≤ α ^ 2 / Real.log N := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hcoord 2
    simpa only [sq_abs, div_pow, Real.sq_sqrt hL0.le] using hh
  have hm5 : (m : ℝ) ^ 5 ≤ c N ^ 8 :=
    (pow_le_pow_left₀ hm0.le hmc 5).trans
      (pow_le_pow_right₀ (hc N) (by norm_num : 5 ≤ 8))
  have hsmall : 1 / Real.log N ≤ (R + 1) / (m : ℝ) ^ 5 := by
    apply (div_le_div_iff₀ hL0 (pow_pos hm0 5)).mpr
    have hh := (div_le_iff₀ hL0).mp hratio.le
    simpa only [one_mul] using hm5.trans hh
  have href : d ^ 2 / (c N * E) ≤ β * α ^ 2 * (R + 1) / (m : ℝ) ^ 5 := by
    calc
      _ = (E / c N) * ⟪v, x⟫ ^ 2 := by dsimp only [d]; field_simp [hc0.ne', hE0.ne']
      _ ≤ β * (α ^ 2 / Real.log N) :=
        mul_le_mul hEc hcoordsq (sq_nonneg _) hβ.le
      _ = (β * α ^ 2) * (1 / Real.log N) := by ring
      _ ≤ (β * α ^ 2) * ((R + 1) / (m : ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  have hr := hresN m hm hmc
  simp only [inner_sub_left, real_inner_smul_left] at hr
  change (p - d) ^ 2 / (c N * E) ≤ C / (m : ℝ) ^ 5 at hr
  have hsquare : p ^ 2 ≤ 2 * (p - d) ^ 2 + 2 * d ^ 2 := by
    nlinarith only [sq_nonneg (p - 2 * d)]
  have hh := div_le_div_of_nonneg_right hsquare (mul_pos hc0 hE0).le
  change p ^ 2 / (c N * E) ≤ _
  calc
    _ ≤ 2 * ((p - d) ^ 2 / (c N * E)) + 2 * (d ^ 2 / (c N * E)) := hh.trans_eq (by ring)
    _ ≤ 2 * (C / (m : ℝ) ^ 5) + 2 * (β * α ^ 2 * (R + 1) / (m : ℝ) ^ 5) :=
      add_le_add (mul_le_mul_of_nonneg_left hr (by norm_num))
        (mul_le_mul_of_nonneg_left href (by norm_num))
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_terminal_residual_inverse_energy_envelope
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_terminal_complete_inverse_energy_envelope
