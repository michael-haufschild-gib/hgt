import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalLowPacketHasAUniformResidualBudget
import GaloisForLFunctions.CompletedArithmeticForms.ConductorOverlapDecay

/-!
# Fixed conductors disappear from the complete critical operator

The completed shell energy decays as the seventh inverse overlap power.
The inverse-energy residual budget therefore makes each fixed normalized
conductor column tend to zero in norm at every positive critical ratio.
This cancellation retains the literal complete matrix, including its pole.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open CriticalArithmeticCorrelationTheory CompletedArithmeticForms
  ArithmeticHodgeTheoryOfDegenerations RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The quarter-power residual budget is absorbed by seventh-power shell decay. -/
theorem criticalCurve_log_quarter_div_seventh {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.log N ^ (1 / 4 : ℝ) / c N ^ 7) atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hcinf).const_div_atTop (1 : ℝ)
  simp only [Function.comp_apply] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N => by
    have := hc N
    positivity) ?_ hlim
  filter_upwards [hcrit.eventually (lt_mem_nhds (by linarith : R / 2 < R)),
    hcinf.eventually_ge_atTop (2 / R), hlog.eventually_gt_atTop 0]
    with N hratio hcR hL
  change 0 < Real.log N at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hc8 : 2 / R ≤ c N ^ 8 := hcR.trans (by
    calc c N = c N ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (hc N) (by norm_num))
  have hL8 : Real.log N ≤ (2 / R) * c N ^ 8 := by
    have h := (le_div_iff₀ hL).mp hratio.le
    have hmul : Real.log N * R ≤ 2 * c N ^ 8 := by nlinarith only [h]
    exact ((le_div_iff₀ hR).mpr hmul).trans_eq (by ring)
  have hL16 : Real.log N ≤ c N ^ 16 :=
    hL8.trans ((mul_le_mul_of_nonneg_right hc8 (pow_nonneg hc0.le 8)).trans_eq (by ring))
  have hquarter : Real.log N ^ (1 / 4 : ℝ) ≤ c N ^ 4 := by
    calc
      _ ≤ (c N ^ 16) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hL.le hL16 (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
        norm_num [Real.rpow_natCast]
  exact (div_le_div_of_nonneg_right hquarter (pow_nonneg hc0.le 7)).trans_eq
    (by field_simp [hc0.ne'])

/-- A fixed conductor's full completed residual tends to zero in the physical norm. -/
theorem tendsto_fixedConductor_critical_residual_norm {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (c N) m •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcut := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hlog
  have hlim := (criticalCurve_log_quarter_div_seventh hc hR hcrit).const_mul
    (tiltedConductorUpperCoefficient m)
  simp only [mul_zero] at hlim
  have hsq : Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (c N) m •
          normalizedRamanujanHorizonVector m N‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ hlim
    filter_upwards [eventually_critical_low_packet_residual_budget hc hR hcrit,
      hcinf.eventually_ge_atTop m, hcut.eventually_ge_atTop m]
      with N hbudget hmc hmcut
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hE : 0 < completedConductorEnergy tiltedUnitSpline (c N) m :=
      (div_pos tiltedConductorFloorCoefficient_pos (pow_pos hc0 7)).trans_le
        (tiltedConductorEnergy_two_sided hm hmc).1
    have hmem : m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ :=
      mem_Icc.mpr ⟨hm, Nat.le_floor hmcut⟩
    have hsingle := (single_le_sum
      (f := fun j =>
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector j N) -
          completedConductorEnergy tiltedUnitSpline (c N) j •
            normalizedRamanujanHorizonVector j N‖ ^ 2 /
          completedConductorEnergy tiltedUnitSpline (c N) j)
      (fun j hj => div_nonneg (sq_nonneg _)
        (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
          integral_tiltedUnitSpline_sq_pos hc0 (mem_Icc.mp hj).1)) hmem).trans hbudget
    have hres := (div_le_iff₀ hE).mp hsingle
    exact hres.trans ((mul_le_mul_of_nonneg_left (tiltedConductorEnergy_two_sided hm hmc).2
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)).trans_eq (by ring))
  have h := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- Each fixed normalized conductor is annihilated asymptotically by the complete critical form. -/
theorem tendsto_fixedConductor_critical_complete_norm {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hE := (tendsto_completedConductorEnergy_atTop contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos m).comp hcinf
  have hnorm : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖ ^ 2)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [real_inner_self_eq_norm_sq, if_true] using
      tendsto_normalizedRamanujanHorizonVector_gram hm hm
  have hlim := (tendsto_fixedConductor_critical_residual_norm hc hR hcrit hm).add
    (hE.mul_const 2)
  simp only [Function.comp_apply, zero_mul, zero_add] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hnorm.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 4))]
    with N hnormN
  have hv : ‖normalizedRamanujanHorizonVector m N‖ ≤ 2 := by
    nlinarith only [hnormN, norm_nonneg (normalizedRamanujanHorizonVector m N)]
  have hE0 := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le (hc N)) hm
  calc
    _ ≤ ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (c N) m •
          normalizedRamanujanHorizonVector m N‖ +
        ‖completedConductorEnergy tiltedUnitSpline (c N) m •
          normalizedRamanujanHorizonVector m N‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (c N) m •
            normalizedRamanujanHorizonVector m N)
        (completedConductorEnergy tiltedUnitSpline (c N) m •
          normalizedRamanujanHorizonVector m N)
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hE0]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hE0)

#print axioms criticalCurve_log_quarter_div_seventh
#print axioms tendsto_fixedConductor_critical_residual_norm
#print axioms tendsto_fixedConductor_critical_complete_norm

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
