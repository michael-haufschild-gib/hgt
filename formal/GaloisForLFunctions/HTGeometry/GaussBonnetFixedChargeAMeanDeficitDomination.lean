import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitForce

/-!
# Uniform control of the shorter-path quartic force

The normalized force is bounded on the full unit path for every
sufficiently near-critical state. The bound uses the actual middle-shift
limit and positive denominator estimates, without a pointwise shortcut.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanDeficitForce_dominated (φ : ℝ) :
    ∀ᶠ τ in atBot, ∀ u ∈ Icc (0 : ℝ) 1, |egbFixedChargeAMeanDeficitForce τ φ u| ≤ 11 := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have hdhi := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hNhi := (egbFixedChargeAMeanPressureNumerator_critical_limit φ).eventually_lt_const
    (show 3 - 2 * egbFixedChargeACriticalCouplingWeight φ < 4 by linarith)
  have hLhi := (egbFixedChargeAMiddleMeanLinearCombination_limit φ).eventually_lt_const
    (show 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) < 5 by linarith)
  have hLlo := (egbFixedChargeAMiddleMeanLinearCombination_limit φ).eventually_const_lt
    (show -5 < 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) by linarith)
  have hRhi := (egbFixedChargeAMiddleMeanResidual_critical_limit φ).eventually_lt_const
    (show 1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5 < 2 by linarith)
  have hRlo := (egbFixedChargeAMiddleMeanResidual_critical_limit φ).eventually_const_lt
    (show -2 < 1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5 by linarith)
  filter_upwards [hdhi, hNhi, hLhi, hLlo, hRhi, hRlo, egbFixedChargeAMiddleQuadraticShift_eventually_bounds φ]
    with τ hdhi hNhi hLhi hLlo hRhi hRlo hc
  intro u hu
  let d := egbCoexistenceASymmetricRatio τ
  let c := egbFixedChargeAMiddleQuadraticShift τ φ
  let N := egbFixedChargeAMeanPressureNumerator τ φ
  let L := 2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ
  let R := (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) / d ^ 2
  let D := egbFixedChargeAMeanDenominator τ φ
  have hd : 0 < d := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hN : 0 < N := egbFixedChargeAMeanPressureNumerator_pos τ φ
  have hD : 4 < D := egbFixedChargeAMeanDenominator_gt_four τ φ
  change d < 1 / 2 at hdhi
  change N < 4 at hNhi
  change L < 5 at hLhi
  change -5 < L at hLlo
  change R < 2 at hRhi
  change -2 < R at hRlo
  change -1 < c ∧ c < 0 at hc
  have hNabs : |N| ≤ 4 := by rw [abs_of_pos hN]; exact hNhi.le
  have hLabs : |L| ≤ 5 := abs_le.mpr ⟨hLlo.le, hLhi.le⟩
  have hRabs : |R| ≤ 2 := abs_le.mpr ⟨hRlo.le, hRhi.le⟩
  have hcabs : |c| ≤ 1 := abs_le.mpr ⟨hc.1.le, by linarith [hc.2]⟩
  have huabs : |u| ≤ 1 := by rw [abs_of_nonneg hu.1]; exact hu.2
  have hd2 : d ^ 2 ≤ 1 := by nlinarith [mul_nonneg hd.le (show 0 ≤ 1 - d by linarith)]
  have hc2 : c ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - c by linarith [hc.2]) (show 0 ≤ c + 1 by linarith [hc.1])]
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have ha0 : 0 ≤ d ^ 2 * c ^ 2 * u ^ 2 := by positivity
  have ha1 : d ^ 2 * c ^ 2 * u ^ 2 ≤ 1 := by
    calc
      _ ≤ (1 * 1) * 1 := mul_le_mul (mul_le_mul hd2 hc2 (sq_nonneg c) (by norm_num)) hu2 (sq_nonneg u) (by norm_num)
      _ = _ := by norm_num
  have haf : |d ^ 2 * c ^ 2 * u ^ 2 - 1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hterm1 : |N * d ^ 2 * c ^ 2 * u ^ 2| ≤ 4 := by
    calc
      _ = |N| * (d ^ 2 * c ^ 2 * u ^ 2) := by
        rw [show N * d ^ 2 * c ^ 2 * u ^ 2 = N * (d ^ 2 * c ^ 2 * u ^ 2) by ring,
          abs_mul, abs_of_nonneg ha0]
      _ ≤ 4 * 1 := mul_le_mul hNabs ha1 ha0 (by norm_num)
      _ = _ := by norm_num
  have hterm2 : |L * c * u| ≤ 5 := by
    simp only [abs_mul]
    calc
      _ ≤ (5 * 1) * 1 := mul_le_mul (mul_le_mul hLabs hcabs (abs_nonneg c) (by norm_num)) huabs (abs_nonneg u) (by norm_num)
      _ = _ := by norm_num
  have hpoly : |egbFixedChargeAMeanDeficitPolynomial τ φ u| ≤ 11 := by
    change |N * d ^ 2 * c ^ 2 * u ^ 2 + L * c * u + R| ≤ 11
    calc
      _ ≤ |N * d ^ 2 * c ^ 2 * u ^ 2 + L * c * u| + |R| := abs_add_le _ _
      _ ≤ (|N * d ^ 2 * c ^ 2 * u ^ 2| + |L * c * u|) + |R| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (4 + 5) + 2 := add_le_add (add_le_add hterm1 hterm2) hRabs
      _ = _ := by norm_num
  have hnum : |(d ^ 2 * c ^ 2 * u ^ 2 - 1) * egbFixedChargeAMeanDeficitPolynomial τ φ u| ≤ 11 := by
    rw [abs_mul]
    calc
      _ ≤ 1 * 11 := mul_le_mul haf hpoly (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hs : 1 / 2 ≤ 1 + d ^ 2 * c * u := by
    have hscale := (egbFixedChargeAMeanDeficitPathScale_mapsTo τ φ hu).1
    change 1 - d ≤ 1 + d ^ 2 * c * u at hscale
    linarith
  have hs2 : 1 / 4 ≤ (1 + d ^ 2 * c * u) ^ 2 := by nlinarith [sq_nonneg (1 + d ^ 2 * c * u - 1 / 2)]
  have hbase : 8 ≤ 2 * D * (1 + d ^ 2) := by
    calc
      _ = 8 * 1 := by ring
      _ ≤ (2 * D) * (1 + d ^ 2) := mul_le_mul (by linarith) (by nlinarith [sq_nonneg d]) (by norm_num) (by linarith)
  have hden2 : 2 ≤ 2 * D * (1 + d ^ 2) * (1 + d ^ 2 * c * u) ^ 2 := by
    calc
      _ = 8 * (1 / 4) := by norm_num
      _ ≤ _ := mul_le_mul hbase hs2 (by norm_num) (by nlinarith)
  have hdenpos : 0 < 2 * D * (1 + d ^ 2) * (1 + d ^ 2 * c * u) ^ 2 := by linarith
  change |((d ^ 2 * c ^ 2 * u ^ 2 - 1) * egbFixedChargeAMeanDeficitPolynomial τ φ u) /
    (2 * D * (1 + d ^ 2) * (1 + d ^ 2 * c * u) ^ 2)| ≤ 11
  rw [abs_div, abs_of_pos hdenpos]
  apply (div_le_iff₀ hdenpos).2
  nlinarith only [hnum, hden2]

end GaloisForLFunctions.HTGeometry
