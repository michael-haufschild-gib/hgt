import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ConductorWeightedResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PolynomialConductorComplementCoercivityAndSharpenedOverlap

/-!
# Linear conductor residuals at their individual energy floors

The seventh-power floor makes the low-conductor relative weight summable.
The linear single-conductor residual leaves only a quadratic cutoff cost.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem sum_inverse_thirteenth_power_le_two (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 13) ≤ 2 := by
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 2 := by
      apply sum_le_sum
      intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
      exact div_le_div_of_nonneg_left zero_le_one
        (sq_pos_of_pos (zero_lt_one.trans_le hm1))
        (pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 13))
    _ ≤ 2 := RHTower.Sieve.sum_inv_sq_le_two Q

private theorem linear_conductor_relative_weight_le {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ^ 2 ≤
      (c ^ 14 / (m : ℝ) ^ 13 + (m : ℝ)) /
        (2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 := by
  let κ : ℝ := 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)
  have hκ : 0 < κ := div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos)
    integral_tiltedUnitSpline_sq_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hfloor := tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale hc0 hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hratio : 1 ≤ (m : ℝ) / m.totient := (one_le_div htot).mpr htot_le
  change (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ^ 2 ≤
    (c ^ 14 / (m : ℝ) ^ 13 + (m : ℝ)) / κ ^ 2
  by_cases hmc : (m : ℝ) ≤ c
  · have hp : ((m : ℝ) / c) ^ 7 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hm0.le hc0.le)
        ((div_le_one hc0).mpr hmc) 7
    rw [min_eq_right hp] at hfloor
    have henergy_lower : κ * ((m : ℝ) / c) ^ 7 ≤ completedConductorEnergy tiltedUnitSpline c m :=
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hκ.le hratio)
        (by positivity)).trans hfloor
    have hbase : 0 < κ * ((m : ℝ) / c) ^ 7 := by positivity
    calc
      _ ≤ (m : ℝ) / (κ * ((m : ℝ) / c) ^ 7) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hbase)
          (pow_le_pow_left₀ hbase.le henergy_lower 2)
      _ = (c ^ 14 / (m : ℝ) ^ 13) / κ ^ 2 := by
        field_simp [hκ.ne', hm0.ne', hc0.ne']
      _ ≤ (c ^ 14 / (m : ℝ) ^ 13 + (m : ℝ)) / κ ^ 2 :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (sq_nonneg κ)
  · have hcm : c ≤ (m : ℝ) := le_of_not_ge hmc
    have henergy_lower : κ ≤ completedConductorEnergy tiltedUnitSpline c m :=
      tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm hcm
    calc
      _ ≤ (m : ℝ) / κ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hκ)
          (pow_le_pow_left₀ hκ.le henergy_lower 2)
      _ ≤ (c ^ 14 / (m : ℝ) ^ 13 + (m : ℝ)) / κ ^ 2 :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (sq_nonneg κ)

/-- Relative residual weights have total mass `O(c¹⁴+Q²)`, uniformly in the cutoff. -/
theorem sum_linear_conductor_relative_weights_le {c : ℝ} (hc : 1 ≤ c) (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ^ 2) ≤
      (2 * c ^ 14 + (Q : ℝ) ^ 2) /
        (2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 := by
  let κ : ℝ := 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)
  have hlinear : (∑ m ∈ Icc 1 Q, (m : ℝ)) ≤ (Q : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 Q, (Q : ℝ) := sum_le_sum fun m hm => by
        exact_mod_cast (mem_Icc.mp hm).2
      _ = (Q : ℝ) ^ 2 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
  have hinverse := sum_inverse_thirteenth_power_le_two Q
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, (c ^ 14 / (m : ℝ) ^ 13 + (m : ℝ)) / κ ^ 2 :=
      sum_le_sum fun m hm => linear_conductor_relative_weight_le hc (mem_Icc.mp hm).1
    _ = (c ^ 14 * (∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 13) +
        ∑ m ∈ Icc 1 Q, (m : ℝ)) / κ ^ 2 := by
      rw [← sum_div, sum_add_distrib, mul_sum]
      congr 2
      exact sum_congr rfl fun m _ => by ring
    _ ≤ (2 * c ^ 14 + (Q : ℝ) ^ 2) / κ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg κ)
      have h := mul_le_mul_of_nonneg_left hinverse (show 0 ≤ c ^ 14 by positivity)
      linarith only [h, hlinear]

/-- Individual completed energies reduce the high-conductor residual sum to a quadratic cutoff cost. -/
theorem exists_tiltedUnitSpline_linear_relative_residual_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ m ∈ Icc 1 Q,
          ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
              completedConductorEnergy tiltedUnitSpline c m ^ 2) ≤
          K * (c ^ 14 + (Q : ℝ) ^ 2) * (1 + Real.log Q) ^ 2 *
            (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
              c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by
  obtain ⟨K₀, hK₀, hres⟩ := exists_tiltedUnitSpline_linear_conductor_residual_variable_rate
  let κ : ℝ := 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)
  have hκ : 0 < κ := div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos)
    integral_tiltedUnitSpline_sq_pos
  refine ⟨2 * K₀ / κ ^ 2, by positivity, ?_⟩
  intro A hA k hk
  filter_upwards [hres A hA k hk, eventually_ge_atTop 2] with N hN hN2
  intro c hc hwidth Q hQ
  let r := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
    c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N
  have hr : 0 ≤ r := by
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have hlog := Real.log_natCast_nonneg N
    dsimp only [r]
    positivity
  have hsum := sum_linear_conductor_relative_weights_le hc Q
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        (K₀ * (m : ℝ) * (1 + Real.log Q) ^ 2 * r) /
          completedConductorEnergy tiltedUnitSpline c m ^ 2 := by
      apply sum_le_sum
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
      have hlogm : Real.log m ≤ Real.log Q := Real.log_le_log hm0 hmQ
      have hp : (1 + Real.log m) ^ 2 ≤ (1 + Real.log Q) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hlogm]) 2
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (mul_nonneg hK₀.le hm0.le)) hr
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (hN m (mem_Icc.mp hm).1 (hmQ.trans hQ) c hc hwidth).trans
        (by simpa only [mul_assoc] using hh)
    _ = (K₀ * (1 + Real.log Q) ^ 2 * r) * ∑ m ∈ Icc 1 Q,
        (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (K₀ * (1 + Real.log Q) ^ 2 * r) * ((2 * c ^ 14 + (Q : ℝ) ^ 2) / κ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 * K₀ / κ ^ 2) * (c ^ 14 + (Q : ℝ) ^ 2) * (1 + Real.log Q) ^ 2 * r := by
      have hbase : 2 * c ^ 14 + (Q : ℝ) ^ 2 ≤ 2 * (c ^ 14 + (Q : ℝ) ^ 2) := by
        nlinarith only [sq_nonneg (Q : ℝ)]
      have hh := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hbase (sq_nonneg κ))
        (show 0 ≤ K₀ * (1 + Real.log Q) ^ 2 * r by positivity)
      exact hh.trans_eq (by ring)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_linear_conductor_relative_weights_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_linear_relative_residual_sum_le
