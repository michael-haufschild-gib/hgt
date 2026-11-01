import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheZeroFreeLogarithmicProfile
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheGammaReserveSurvivesGrowingOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapConductorFloor

/-!
# The logarithmic profile's quantitative Gamma reserve

The explicit spectral floor on `[c,101c]` retains a fraction
`24 c·zeroFreeLogBandFloor c / (π‖φ‖₂²)` of the logarithmic coefficient mass.
The physical Gram bound costs only a constant times `c` when `c ≤ N`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology Finset Zeta23
open scoped ContDiff

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticPositivityTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Coefficient of the logarithmic Gamma reserve. -/
def zeroFreeLogGammaReserve (c : ℝ) : ℝ :=
  24 * c * zeroFreeLogBandFloor c / (Real.pi * ∫ u, zeroFreeLogProfile u ^ 2)

theorem zeroFreeLogGammaReserve_pos {c : ℝ} (hc : 0 < c) :
    0 < zeroFreeLogGammaReserve c := by
  have hm := integral_zeroFreeLogProfile_sq_pos
  have hf := zeroFreeLogBandFloor_pos c
  unfold zeroFreeLogGammaReserve
  positivity

/-- Uniform in every horizon above the overlap and every signed coefficient vector. -/
theorem eventually_zeroFreeLogProfile_archForm_reserve :
    ∀ᶠ c : ℝ in atTop, ∀ N : ℕ, c ≤ (N : ℝ) → ∀ x : ℕ → ℝ,
      (zeroFreeLogGammaReserve c * Real.log N - growingReserveCost * c) *
        ((c / N) * ∫ u, zeroFreeLogProfile u ^ 2) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
          RHTower.archForm (atomicTest N x (atomDilate zeroFreeLogProfile (c / N))) := by
  filter_upwards [eventually_zeroFreeLogProfile_band_floor, eventually_ge_atTop (1 : ℝ)]
    with c hfloor hc
  intro N hcN x
  have hc0 := zero_lt_one.trans_le hc
  have hNR : (0 : ℝ) < N := hc0.trans_le hcN
  have hN : 1 ≤ N := by exact_mod_cast (hc.trans hcN)
  have hw : 0 < c / N := div_pos hc0 hNR
  have hφ := contDiff_zeroFreeLogProfile.of_le (natCast_le_infty 2)
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ zeroFreeLogProfile_eq_zero hw
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hgamma := archForm_ge_log_band_sub_mass hf hfc hNR
  have hband := noRealZero_highBand_mass hφ zeroFreeLogProfile_eq_zero hc0
    (zeroFreeLogBandFloor_pos c) hfloor hN x
  have hmass := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hgsupp x
  rw [integral_atomDilate_sq hw] at hmass
  have hoff : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg (by norm_num))
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hM := integral_zeroFreeLogProfile_sq_pos
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hbandTerm := mul_le_mul_of_nonneg_left hband
    (div_nonneg hlogN Real.two_pi_pos.le)
  have hcoef : Real.log N / (2 * Real.pi) *
      ((48 * (c / N) ^ 2 * zeroFreeLogBandFloor c * N) * (∑ n ∈ Icc 1 N, x n ^ 2)) =
      zeroFreeLogGammaReserve c * Real.log N *
        ((c / N) * ∫ u, zeroFreeLogProfile u ^ 2) * (∑ n ∈ Icc 1 N, x n ^ 2) := by
    unfold zeroFreeLogGammaReserve
    field_simp [Real.pi_ne_zero, hNR.ne', hM.ne']
    <;> ring
  rw [hcoef] at hbandTerm
  have hB : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
    nlinarith only [hc]
  have hG : 0 ≤ c / N * ∫ u, zeroFreeLogProfile u ^ 2 := by positivity
  have hcost := mul_le_mul_of_nonneg_left
    (hmass.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hG) hS)) hoff
  have hcostEq : (factorialSpanGammaOffset + Real.log 2) *
      ((c / N * ∫ u, zeroFreeLogProfile u ^ 2) * ((1 + 2 * Real.exp 1) * c) *
        (∑ n ∈ Icc 1 N, x n ^ 2)) =
      growingReserveCost * c * ((c / N) * ∫ u, zeroFreeLogProfile u ^ 2) *
        (∑ n ∈ Icc 1 N, x n ^ 2) := by
    unfold growingReserveCost
    ring
  rw [hcostEq] at hcost
  nlinarith only [hgamma, hbandTerm, hcost]

/-- A frequency interval of length `c` supplies a floor for every conductor. -/
def zeroFreeLogConductorFloor (c : ℝ) : ℝ :=
  2 * c * zeroFreeLogBandFloor (2 * Real.pi * c) / ∫ u, zeroFreeLogProfile u ^ 2

theorem zeroFreeLogConductorFloor_pos {c : ℝ} (hc : 0 < c) :
    0 < zeroFreeLogConductorFloor c := by
  exact div_pos (mul_pos (mul_pos zero_lt_two hc) (zeroFreeLogBandFloor_pos _))
    integral_zeroFreeLogProfile_sq_pos

/-- The same logarithmic Fourier floor controls every completed conductor energy. -/
theorem eventually_zeroFreeLogProfile_conductor_floor :
    ∀ᶠ c : ℝ in atTop, ∀ m : ℕ, 0 < m →
      zeroFreeLogConductorFloor c ≤ completedConductorEnergy zeroFreeLogProfile c m := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp eventually_zeroFreeLogProfile_band_floor
  have hp := Real.two_pi_pos
  filter_upwards [eventually_ge_atTop (A / (2 * Real.pi)), eventually_gt_atTop (0 : ℝ)]
    with c hcA hc
  have hcA' : A ≤ 2 * Real.pi * c := by
    have h := (div_le_iff₀ hp).mp hcA
    simpa only [mul_comm c] using h
  have hb : ∀ t ∈ Set.Icc c (2 * c),
      zeroFreeLogBandFloor (2 * Real.pi * c) ≤ shellSpectrum zeroFreeLogProfile t := by
    intro t ht
    apply hA _ hcA'
    constructor
    · exact mul_le_mul_of_nonneg_left ht.1 hp.le
    · have h := mul_le_mul_of_nonneg_left ht.2 hp.le
      nlinarith only [h, mul_pos hp hc]
  have hφ := contDiff_zeroFreeLogProfile.of_le (natCast_le_infty 2)
  have hcont := continuous_shellSpectrum contDiff_zeroFreeLogProfile.continuous
    hasCompactSupport_zeroFreeLogProfile
  have hband : c * zeroFreeLogBandFloor (2 * Real.pi * c) ≤
      ∫ t in c..2 * c, shellSpectrum zeroFreeLogProfile t := by
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (show c ≤ 2 * c by linarith only [hc])
      (continuous_const.intervalIntegrable c (2 * c))
      (hcont.intervalIntegrable c (2 * c)) hb
    simpa only [intervalIntegral.integral_const, smul_eq_mul,
      show 2 * c - c = c by ring] using h
  have htail : (∫ t in c..2 * c, shellSpectrum zeroFreeLogProfile t) ≤
      ∫ t in Set.Ioi c, shellSpectrum zeroFreeLogProfile t := by
    rw [intervalIntegral.integral_of_le (by linarith only [hc])]
    exact setIntegral_mono_set
      (integrableOn_shellSpectrum_Ioi hφ hasCompactSupport_zeroFreeLogProfile c)
      (Filter.Eventually.of_forall fun t => shellSpectrum_nonneg t)
      Set.Ioc_subset_Ioi_self.eventuallyLE
  intro m hm
  have hM := integral_zeroFreeLogProfile_sq_pos
  calc
    zeroFreeLogConductorFloor c =
        (2 / ∫ u, zeroFreeLogProfile u ^ 2) *
          (c * zeroFreeLogBandFloor (2 * Real.pi * c)) := by
      unfold zeroFreeLogConductorFloor
      ring
    _ ≤ (2 / ∫ u, zeroFreeLogProfile u ^ 2) *
        ∫ t in Set.Ioi c, shellSpectrum zeroFreeLogProfile t :=
      mul_le_mul_of_nonneg_left (hband.trans htail) (by positivity)
    _ ≤ _ := completedConductorEnergy_ge_shellTail hφ zeroFreeLogProfile_eq_zero hM hc hm

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_zeroFreeLogProfile_archForm_reserve
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_zeroFreeLogProfile_conductor_floor
