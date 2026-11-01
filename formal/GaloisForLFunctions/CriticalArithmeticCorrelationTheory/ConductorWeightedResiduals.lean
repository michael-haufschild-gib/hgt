import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ConductorScaleControlsTheCompletedEnergy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.VariableCutoffConductorResiduals
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic

/-!
# Conductor-weighted complete residuals

Below the overlap scale the seventh-power conductor floor makes the relative
residual summable. Above it, only the fifth power of the conductor cutoff remains.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem sum_inverse_tenth_power_le_two (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 10) ≤ 2 := by
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 2 := by
      apply sum_le_sum
      intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
      exact div_le_div_of_nonneg_left zero_le_one
        (sq_pos_of_pos (zero_lt_one.trans_le hm1))
        (pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 10))
    _ ≤ 2 := RHTower.Sieve.sum_inv_sq_le_two Q

private theorem conductor_relative_weight_le {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ 4 / completedConductorEnergy tiltedUnitSpline c m ^ 2 ≤
      (c ^ 14 / (m : ℝ) ^ 10 + (m : ℝ) ^ 4) /
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
  change (m : ℝ) ^ 4 / completedConductorEnergy tiltedUnitSpline c m ^ 2 ≤
    (c ^ 14 / (m : ℝ) ^ 10 + (m : ℝ) ^ 4) / κ ^ 2
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
      _ ≤ (m : ℝ) ^ 4 / (κ * ((m : ℝ) / c) ^ 7) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hbase)
          (pow_le_pow_left₀ hbase.le henergy_lower 2)
      _ = (c ^ 14 / (m : ℝ) ^ 10) / κ ^ 2 := by
        field_simp [hκ.ne', hm0.ne', hc0.ne']
      _ ≤ (c ^ 14 / (m : ℝ) ^ 10 + (m : ℝ) ^ 4) / κ ^ 2 :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (sq_nonneg κ)
  · have hcm : c ≤ (m : ℝ) := le_of_not_ge hmc
    have henergy_lower : κ ≤ completedConductorEnergy tiltedUnitSpline c m :=
      tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm hcm
    calc
      _ ≤ (m : ℝ) ^ 4 / κ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hκ)
          (pow_le_pow_left₀ hκ.le henergy_lower 2)
      _ ≤ (c ^ 14 / (m : ℝ) ^ 10 + (m : ℝ) ^ 4) / κ ^ 2 :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (sq_nonneg κ)

/-- Relative residual weights have total mass `O(c¹⁴+Q⁵)`, uniformly in the cutoff. -/
theorem sum_conductor_relative_weights_le {c : ℝ} (hc : 1 ≤ c) (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, (m : ℝ) ^ 4 / completedConductorEnergy tiltedUnitSpline c m ^ 2) ≤
      (2 * c ^ 14 + (Q : ℝ) ^ 5) /
        (2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 := by
  let κ : ℝ := 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)
  have hfour : (∑ m ∈ Icc 1 Q, (m : ℝ) ^ 4) ≤ (Q : ℝ) ^ 5 := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 Q, (Q : ℝ) ^ 4 := sum_le_sum fun m hm =>
        pow_le_pow_left₀ (Nat.cast_nonneg m) (by exact_mod_cast (mem_Icc.mp hm).2) 4
      _ = (Q : ℝ) ^ 5 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
  have htenth := sum_inverse_tenth_power_le_two Q
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, (c ^ 14 / (m : ℝ) ^ 10 + (m : ℝ) ^ 4) / κ ^ 2 :=
      sum_le_sum fun m hm => conductor_relative_weight_le hc (mem_Icc.mp hm).1
    _ = (c ^ 14 * (∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 10) +
        ∑ m ∈ Icc 1 Q, (m : ℝ) ^ 4) / κ ^ 2 := by
      rw [← sum_div, sum_add_distrib, mul_sum]
      congr 2
      exact sum_congr rfl fun m _ => by ring
    _ ≤ (2 * c ^ 14 + (Q : ℝ) ^ 5) / κ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg κ)
      have h := mul_le_mul_of_nonneg_left htenth (show 0 ≤ c ^ 14 by positivity)
      linarith only [h, hfour]

/-- Squared complete residuals divided by their own conductor energies have a uniform
bound on logarithmic families. The constant is independent of both exponents. -/
theorem exists_tiltedUnitSpline_relative_residual_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ m ∈ Icc 1 Q,
          ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
              completedConductorEnergy tiltedUnitSpline c m ^ 2) ≤
          K * (c ^ 14 + (Q : ℝ) ^ 5) * (c ^ 5 / Real.log N +
            c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by
  obtain ⟨K₀, hK₀, hres⟩ := exists_tiltedUnitSpline_uniform_conductor_residual_variable_rate
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
  have hsum := sum_conductor_relative_weights_le hc Q
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        (K₀ * (m : ℝ) ^ 4 * r) / completedConductorEnergy tiltedUnitSpline c m ^ 2 := by
      apply sum_le_sum
      intro m hm
      have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
      exact div_le_div_of_nonneg_right
        (hN m (mem_Icc.mp hm).1 (hmQ.trans hQ) c hc hwidth) (sq_nonneg _)
    _ = (K₀ * r) * ∑ m ∈ Icc 1 Q,
        (m : ℝ) ^ 4 / completedConductorEnergy tiltedUnitSpline c m ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (K₀ * r) * ((2 * c ^ 14 + (Q : ℝ) ^ 5) / κ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hK₀.le hr)
    _ ≤ (2 * K₀ / κ ^ 2) * (c ^ 14 + (Q : ℝ) ^ 5) * r := by
      have hbase : 2 * c ^ 14 + (Q : ℝ) ^ 5 ≤ 2 * (c ^ 14 + (Q : ℝ) ^ 5) := by
        nlinarith only [pow_nonneg (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q) 5]
      have h := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hbase (sq_nonneg κ)) (mul_nonneg hK₀.le hr)
      calc
        _ ≤ (K₀ * r) * (2 * (c ^ 14 + (Q : ℝ) ^ 5) / κ ^ 2) := h
        _ = (2 * K₀ / κ ^ 2) * (c ^ 14 + (Q : ℝ) ^ 5) * r := by ring

/-- Each conductor pays its own coordinate estimate in a nonpositive eigenvector. -/
theorem matrix_posDef_of_relative_conductor_budget {N R Q : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (E : ℕ → ℝ) (hE : ∀ m ∈ Icc 1 Q, 0 < E m)
    (hRQ : R ≤ Q) (hQ : 2 ≤ Q) (hQN : Q ^ 4 ≤ N)
    (happrox : ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ‖x‖ = 1 →
      ⟪Matrix.toEuclideanLin A x, x⟫ ≤ 0 →
      ∃ a : ℕ → ℝ, (∑ n ∈ Icc 1 N,
        (primeHorizonExtension x n -
          ∑ m ∈ Icc 1 R, a m * ramanujanPoleProfile m n) ^ 2) ≤ 1 / 4)
    (hbudget : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2) ≤ 1 / 36) : A.PosDef := by
  classical
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  by_contra hi
  have hi0 : hA.eigenvalues i ≤ 0 := le_of_not_gt hi
  let x := hA.eigenvectorBasis i
  have hx : ‖x‖ = 1 := by
    have hh : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh, norm_nonneg x]
  have henergy : ⟪Matrix.toEuclideanLin A x, x⟫ ≤ 0 := by
    have hAx : Matrix.toEuclideanLin A x = hA.eigenvalues i • x := by
      ext j
      exact congrFun (hA.mulVec_eigenvectorBasis i) j
    rw [hAx, real_inner_smul_left, real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
    exact hi0
  obtain ⟨a, ha⟩ := happrox x hx henergy
  have hmass := normalizedRamanujan_coordinate_mass_ge_of_raw_approximation
    hRQ hQ hQN x hx a ha
  have hsum : (∑ m ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
      ∑ m ∈ Icc 1 Q,
        ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2 := by
    exact sum_le_sum fun m hm =>
      nonpositive_eigenvector_coordinate_sq_le_uniform_residual hA i hi0 (hE m hm)
        le_rfl (normalizedRamanujanHorizonVector m N)
  linarith only [hmass, hsum.trans hbudget]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_conductor_relative_weights_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_relative_residual_sum_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.matrix_posDef_of_relative_conductor_budget
