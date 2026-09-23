import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierIntegrand

/-!
# Uniform domination of the normalized physical barrier integrand

The bound covers the entire integration interval and every sufficiently
near-critical coexistence state. All denominator lower bounds come from
the actual phase-radius construction.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeABarrierIntegrand_dominated (w φ : ℝ) :
    ∀ᶠ τ in atBot, ∀ u ∈ Icc (0 : ℝ) 1,
      |egbFixedChargeABarrierIntegrand w φ τ u| ≤ 20 * (egbFixedChargeACriticalRadius w φ + 1) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have hdhi := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hmhi := (egbFixedChargeAMeanRadius_critical_limit w φ).eventually_lt_const (show egbFixedChargeACriticalRadius w φ < egbFixedChargeACriticalRadius w φ + 1 by linarith)
  have hNhi := (egbFixedChargeAMeanPressureNumerator_critical_limit φ).eventually_lt_const (show 3 - 2 * egbFixedChargeACriticalCouplingWeight φ < 4 by linarith)
  have hLhi := (egbFixedChargeAMiddleMeanLinearCombination_limit φ).eventually_lt_const (show 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) < 5 by linarith)
  have hLlo := (egbFixedChargeAMiddleMeanLinearCombination_limit φ).eventually_const_lt (show -5 < 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) by linarith)
  have hRhi := (egbFixedChargeAMiddleMeanResidual_linear_limit φ).eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hRlo := (egbFixedChargeAMiddleMeanResidual_linear_limit φ).eventually_const_lt (by norm_num : (-1 : ℝ) < 0)
  filter_upwards [hdhi, hmhi, hNhi, hLhi, hLlo, hRhi, hRlo] with τ hdhi hmhi hNhi hLhi hLlo hRhi hRlo
  intro u hu
  let d := egbCoexistenceASymmetricRatio τ
  let m := egbFixedChargeAMeanRadius w φ τ
  let N := egbFixedChargeAMeanPressureNumerator τ φ
  let L := 2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ
  let R := (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) / d
  let t0 := egbFixedChargeAMiddleGapCoordinate τ φ
  let c := egbFixedChargeABarrierPathCoordinate τ φ u
  let D := egbFixedChargeAMeanDenominator τ φ
  have hd : 0 < d := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hm : 0 < m := egbFixedChargeAMeanRadius_pos w φ τ
  have hN : 0 < N := egbFixedChargeAMeanPressureNumerator_pos τ φ
  have hD : 4 < D := egbFixedChargeAMeanDenominator_gt_four τ φ
  have hc : -1 ≤ c ∧ c ≤ 1 := egbFixedChargeABarrierPathCoordinate_mapsTo τ φ hu
  have ht0 : -1 < t0 ∧ t0 < 1 := egbFixedChargeAMiddleGapCoordinate_bounds τ φ
  change d < 1 / 2 at hdhi
  change m < egbFixedChargeACriticalRadius w φ + 1 at hmhi
  change N < 4 at hNhi
  change L < 5 at hLhi
  change -5 < L at hLlo
  change R < 1 at hRhi
  change -1 < R at hRlo
  have hmabs : |m| ≤ egbFixedChargeACriticalRadius w φ + 1 := by rw [abs_of_pos hm]; exact hmhi.le
  have hNabs : |N| ≤ 4 := by rw [abs_of_pos hN]; exact hNhi.le
  have hdabs : |d| ≤ 1 := by rw [abs_of_pos hd]; linarith
  have hLabs : |L| ≤ 5 := abs_le.mpr ⟨hLlo.le, hLhi.le⟩
  have hRabs : |R| ≤ 1 := abs_le.mpr ⟨hRlo.le, hRhi.le⟩
  have hcabs : |c| ≤ 1 := abs_le.mpr hc
  have hcsq : c ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - c by linarith [hc.2]) (show 0 ≤ c + 1 by linarith [hc.1])]
  have hcpoly : |c ^ (2 : ℕ) - 1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg c]
  have ht : |t0 - 1| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [ht0.1, ht0.2]
  have hterm1 : |N * d * c ^ (2 : ℕ)| ≤ 4 := by
    calc
      _ = (|N| * |d|) * c ^ (2 : ℕ) := by rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c)]
      _ ≤ (4 * 1) * 1 := mul_le_mul (mul_le_mul hNabs hdabs (abs_nonneg d) (by norm_num)) hcsq (sq_nonneg c) (by norm_num)
      _ = _ := by norm_num
  have hterm2 : |L * c| ≤ 5 := by
    rw [abs_mul]
    calc
      _ ≤ 5 * 1 := mul_le_mul hLabs hcabs (abs_nonneg c) (by norm_num)
      _ = _ := by norm_num
  have hpoly : |egbFixedChargeABarrierPolynomial τ φ c| ≤ 10 := by
    change |N * d * c ^ (2 : ℕ) + L * c + R| ≤ 10
    calc
      _ ≤ |N * d * c ^ (2 : ℕ) + L * c| + |R| := abs_add_le _ _
      _ ≤ (|N * d * c ^ (2 : ℕ)| + |L * c|) + |R| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (4 + 5) + 1 := add_le_add (add_le_add hterm1 hterm2) hRabs
      _ = _ := by norm_num
  have hnum : |m * (t0 - 1) * (c ^ (2 : ℕ) - 1) * egbFixedChargeABarrierPolynomial τ φ c| ≤
      20 * (egbFixedChargeACriticalRadius w φ + 1) := by
    calc
      _ = ((|m| * |t0 - 1|) * |c ^ (2 : ℕ) - 1|) * |egbFixedChargeABarrierPolynomial τ φ c| := by simp only [abs_mul]
      _ ≤ (((egbFixedChargeACriticalRadius w φ + 1) * 2) * 1) * 10 :=
        mul_le_mul (mul_le_mul (mul_le_mul hmabs ht (abs_nonneg _) (by positivity)) hcpoly (abs_nonneg _) (by positivity))
          hpoly (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hs : 1 / 2 ≤ 1 + d * c := by
    have hscale := (egbFixedChargeABarrierPathScale_mapsTo τ φ hu).1
    change 1 - d ≤ 1 + d * c at hscale
    linarith
  have hs2 : 1 / 4 ≤ (1 + d * c) ^ (2 : ℕ) := by nlinarith [sq_nonneg (1 + d * c - 1 / 2)]
  have hbase : 8 ≤ 2 * D * (1 + d ^ (2 : ℕ)) := by
    calc
      _ = 8 * 1 := by ring
      _ ≤ (2 * D) * (1 + d ^ (2 : ℕ)) := mul_le_mul (by linarith) (by nlinarith [sq_nonneg d]) (by norm_num) (by linarith)
  have hden2 : 2 ≤ 2 * D * (1 + d ^ (2 : ℕ)) * (1 + d * c) ^ (2 : ℕ) := by
    calc
      _ = 8 * (1 / 4) := by norm_num
      _ ≤ _ := mul_le_mul hbase hs2 (by norm_num) (by nlinarith)
  have hdenpos : 0 < 2 * D * (1 + d ^ (2 : ℕ)) * (1 + d * c) ^ (2 : ℕ) := by linarith
  change |(m * (t0 - 1) * (c ^ (2 : ℕ) - 1) * egbFixedChargeABarrierPolynomial τ φ c) /
      (2 * D * (1 + d ^ (2 : ℕ)) * (1 + d * c) ^ (2 : ℕ))| ≤ _
  rw [abs_div, abs_of_pos hdenpos]
  apply (div_le_iff₀ hdenpos).2
  calc
    _ ≤ 20 * (egbFixedChargeACriticalRadius w φ + 1) := hnum
    _ ≤ _ := by
      have hp := mul_le_mul_of_nonneg_left (show 1 ≤ 2 * D * (1 + d ^ (2 : ℕ)) * (1 + d * c) ^ (2 : ℕ) by linarith)
        (show 0 ≤ 20 * (egbFixedChargeACriticalRadius w φ + 1) by positivity)
      simpa only [mul_one] using hp

end GaloisForLFunctions.HTGeometry
