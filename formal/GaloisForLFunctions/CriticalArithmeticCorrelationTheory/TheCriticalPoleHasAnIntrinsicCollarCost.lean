import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolarSourceIsNonzero
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals
import GaloisForLFunctions.CompletedArithmeticForms.ConductorOverlapDecay

/-!
# The critical pole has an intrinsic quadratic collar cost

A fixed terminal window detects a nonzero signed pole source. Weighted
Cauchy–Schwarz turns that response into a lower bound for the literal
dual-seventh residual mass. After the conductor-energy normalization,
the bound grows quadratically in the critical ratio.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CompletedArithmeticForms

/-- The complete pole residual, with its literal completed conductor energy. -/
def terminalPoleResidual (c : ℝ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector 1 N) -
    completedConductorEnergy tiltedUnitSpline c 1 • normalizedRamanujanHorizonVector 1 N

private theorem window_extension_eq_terminal (h : ℝ → ℝ) {N n : ℕ}
    (hN : 1 ≤ N) (hn : n ∈ Icc 1 N) :
    primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) n =
      logProfile h ((n : ℝ) / N) / Real.sqrt n := by
  rw [horizonProfileVector_horizonWeights_eq_terminal h hN, primeHorizonExtension, dif_pos hn]
  rfl

/-- The fixed terminal witness has exactly zero mass on the lower half of the horizon. -/
theorem terminalPolarWitness_half_prefix_eq_zero {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 (N / 2),
      primeHorizonExtension (horizonProfileVector (horizonWeights terminalPolarWitness N) N) n ^ 2) = 0 := by
  apply sum_eq_zero
  intro n hn
  have hnN : n ∈ Icc 1 N :=
    mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.div_le_self N 2)⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hhalf : 2 * n ≤ N := by have := (mem_Icc.mp hn).2; omega
  have hhalfR : (2 : ℝ) * n ≤ N := by exact_mod_cast hhalf
  have hx : (n : ℝ) / N ≤ (253 / 256 : ℝ) := by
    apply (div_le_iff₀ hN0).mpr
    nlinarith only [hhalfR, hN0]
  rw [window_extension_eq_terminal terminalPolarWitness hN hnN,
    logProfile_terminalPolarWitness, terminalPolarWitnessLinear_eq_zero_below _ hx,
    zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- On the upper half, the seventh collar weight is bounded by `2⁷`. -/
theorem topCollarSeventhMass_half_le_norm_sq (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarSeventhMass (N / 2) N (primeHorizonExtension x) ≤ 128 * ‖x‖ ^ 2 := by
  have hsub : Ioc (N / 2) N ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hn
    exact mem_Icc.mpr ⟨by omega, hhi⟩
  unfold topCollarSeventhMass
  calc
    _ ≤ ∑ n ∈ Ioc (N / 2) N, (128 : ℝ) * primeHorizonExtension x n ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (hsub hn)).1
      have hhalf : N ≤ 2 * n := by have := (mem_Ioc.mp hn).1; omega
      have hratio : (N : ℝ) / n ≤ (2 : ℝ) := by
        apply (div_le_iff₀ hn0).mpr
        exact_mod_cast hhalf
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ) / n) hratio 7
      norm_num at hp
      exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = 128 * ∑ n ∈ Ioc (N / 2) N, primeHorizonExtension x n ^ 2 := (mul_sum _ _ _).symm
    _ ≤ 128 * ∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _)
        (by norm_num)
    _ = _ := by rw [sum_primeHorizonExtension_sq]

private theorem tendsto_terminal_pole_energy_coordinate
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
    (tiltedConductorEnergy_two_sided one_pos (hc N)).2.trans
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
    _ = _ := by field_simp [hsL.ne', hc0.ne'] <;> ring

/-- The completed energy subtraction does not alter the nonzero terminal source. -/
theorem tendsto_terminalPoleResidual_witness
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪terminalPoleResidual (c N) N,
        horizonProfileVector (horizonWeights terminalPolarWitness N) N⟫)
      atTop (𝓝 terminalPolarWitnessSource) := by
  obtain ⟨B, _, hB, _⟩ := exists_bound_lipschitz contDiff_terminalPolarWitness
    terminalPolarWitness_window_support
  have hd := tendsto_terminal_pole_energy_coordinate terminalPolarWitness_window_support hB hc
    (criticalCurve_facts hc hR hcrit).1
  have ht := (tendsto_complete_terminalPolarWitness hc hR hcrit).sub hd
  simp only [sub_zero] at ht
  exact ht.congr fun N => by rw [terminalPoleResidual, real_inner_sub_left, mul_sub]

/-- The actual dual collar loss has a quadratic lower bound in the critical ratio,
with one positive constant independent of that ratio and of its critical clock. -/
theorem exists_intrinsic_critical_pole_collar_cost :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) →
      ∀ {R : ℝ}, 0 < R →
        Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R) →
        ∀ᶠ N : ℕ in atTop,
          κ * R ^ 2 ≤ c N ^ 7 / Real.log N *
            (topCollarDualSeventhMass (N / 2) N (terminalPoleResidual (c N) N) /
              completedConductorEnergy tiltedUnitSpline (c N) 1) := by
  obtain ⟨B, _, hB, _⟩ := exists_bound_lipschitz contDiff_terminalPolarWitness
    terminalPolarWitness_window_support
  let S := terminalPolarWitnessSource
  let C := tiltedConductorUpperCoefficient 1
  let T := 128 * (B ^ 2 * Real.exp (Real.log 2) + 1)
  have hS : 0 < S := terminalPolarWitnessSource_pos
  have hC : 0 < C := tiltedConductorUpperCoefficient_pos one_pos
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨S ^ 2 / (32 * C * T), by positivity, ?_⟩
  intro c hc R hR hcrit
  have hsource := tendsto_terminalPoleResidual_witness hc hR hcrit
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    hsource.eventually (lt_mem_nhds (half_lt_self hS)),
    hcrit.eventually (lt_mem_nhds (half_lt_self hR))] with N hN hL hmix hratio
  change 0 < Real.log (N : ℝ) at hL
  let x := horizonProfileVector (horizonWeights terminalPolarWitness N) N
  let r := terminalPoleResidual (c N) N
  let D := topCollarDualSeventhMass (N / 2) N r
  have hD0 : 0 ≤ D := topCollarDualSeventhMass_nonneg _ _ _
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hx := horizon_window_norm_sq_le terminalPolarWitness_window_support hB hN
  have htop : topCollarSeventhMass (N / 2) N (primeHorizonExtension x) ≤ T := by
    have hb := (topCollarSeventhMass_half_le_norm_sq N x).trans
      (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 128))
    exact hb.trans (by dsimp only [T]; linarith)
  have hcs := inner_sq_le_prefix_add_topCollarSeventh (Nat.div_le_self N 2) r x
  rw [terminalPolarWitness_half_prefix_eq_zero hN, mul_zero, zero_add] at hcs
  have hpair : ⟪r, x⟫ ^ 2 ≤ 2 * D * T :=
    hcs.trans (mul_le_mul_of_nonneg_left htop (by positivity))
  have hsq := pow_le_pow_left₀ (half_pos hS).le hmix.le 2
  rw [mul_pow, div_pow, Real.sq_sqrt hL.le] at hsq
  change (S / 2) ^ 2 ≤ Real.log N / c N ^ 2 * ⟪r, x⟫ ^ 2 at hsq
  have hscaled := hsq.trans
    (mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ Real.log N / c N ^ 2))
  have hmul := mul_le_mul_of_nonneg_right hscaled (sq_nonneg (c N))
  have hcancel : (Real.log N / c N ^ 2 * (2 * D * T)) * c N ^ 2 =
      2 * D * T * Real.log N := by field_simp [hc0.ne'] <;> ring
  rw [hcancel] at hmul
  have hD : S ^ 2 * c N ^ 2 / (8 * T * Real.log N) ≤ D := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * T * Real.log N)).mpr
    nlinarith only [hmul]
  have hE := tiltedConductorEnergy_two_sided (m := 1) one_pos (hc N)
  have hE0 : 0 < completedConductorEnergy tiltedUnitSpline (c N) 1 :=
    (div_pos tiltedConductorFloorCoefficient_pos (pow_pos hc0 7)).trans_le hE.1
  have hquot : (S ^ 2 * c N ^ 2 / (8 * T * Real.log N)) / (C / c N ^ 7) ≤
      D / completedConductorEnergy tiltedUnitSpline (c N) 1 :=
    (div_le_div_of_nonneg_left (by positivity) hE0 hE.2).trans
      (div_le_div_of_nonneg_right hD hE0.le)
  have hfinal := mul_le_mul_of_nonneg_left hquot
    (by positivity : 0 ≤ c N ^ 7 / Real.log N)
  have halg : c N ^ 7 / Real.log N *
      ((S ^ 2 * c N ^ 2 / (8 * T * Real.log N)) / (C / c N ^ 7)) =
      (S ^ 2 / (8 * C * T)) * (c N ^ 8 / Real.log N) ^ 2 := by
    field_simp [hc0.ne', hL.ne', hC.ne', hT.ne'] <;> ring
  rw [halg] at hfinal
  have hratioSq := pow_le_pow_left₀ (half_pos hR).le hratio.le 2
  calc
    _ = (S ^ 2 / (8 * C * T)) * (R / 2) ^ 2 := by
      field_simp [hC.ne', hT.ne'] <;> ring
    _ ≤ (S ^ 2 / (8 * C * T)) * (c N ^ 8 / Real.log N) ^ 2 :=
      mul_le_mul_of_nonneg_left hratioSq (by positivity)
    _ ≤ _ := hfinal

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_terminalPoleResidual_witness
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_intrinsic_critical_pole_collar_cost
