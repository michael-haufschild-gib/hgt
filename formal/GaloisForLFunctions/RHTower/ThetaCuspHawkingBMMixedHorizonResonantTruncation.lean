import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonRegularBranch

/-!
# Exact resonant truncation at the mixed BM horizon

At denominator parameter `c = -N`, mathlib's ordinary hypergeometric coefficient sequence
terminates because the inverse Pochhammer denominator is zero from order `N+1` onward. Below the
collision it obeys the usual Gauss recurrence. This module proves the exact top coefficient and
shows that the full Euler-form differential residual is one terminal monomial at degree `N+1`.

The theorem isolates the unique algebraic source cancelled by the logarithmic Frobenius branch.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Nat Polynomial
open scoped PowerSeries

namespace RHTower

noncomputable section

/-- Ordinary Gauss coefficient at the resonant denominator parameter `c = -N`. -/
def d4HypergeometricResonantTruncationCoefficient
    (N : ℕ) (a b : ℂ) (j : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient a b (-(N : ℂ)) j

/-- Before and including the terminal index, the negative-integral denominator Pochhammer is
nonzero. -/
theorem d4HypergeometricResonantTruncation_denominator_ne_zero
    {N j : ℕ} (hj : j ≤ N) :
    (ascPochhammer ℂ j).eval (-(N : ℂ)) ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro k hk hkn
  simp only [neg_neg] at hkn
  have hkeq : k = N := by
    exact_mod_cast hkn
  omega

/-- The resonant truncation is normalized by constant coefficient one. -/
@[simp] theorem d4HypergeometricResonantTruncationCoefficient_zero
    (N : ℕ) (a b : ℂ) :
    d4HypergeometricResonantTruncationCoefficient N a b 0 = 1 := by
  simp [d4HypergeometricResonantTruncationCoefficient,
    ordinaryHypergeometricCoefficient]

/-- Exact Gauss recurrence strictly below the negative-integral collision. -/
theorem d4HypergeometricResonantTruncationCoefficient_succ_recurrence
    (N : ℕ) (a b : ℂ) (j : ℕ) (hj : j < N) :
    ((j + 1 : ℕ) : ℂ) * (-(N : ℂ) + (j : ℂ)) *
        d4HypergeometricResonantTruncationCoefficient N a b (j + 1) =
      (a + (j : ℂ)) * (b + (j : ℂ)) *
        d4HypergeometricResonantTruncationCoefficient N a b j := by
  unfold d4HypergeometricResonantTruncationCoefficient
  apply ordinaryHypergeometricCoefficient_succ_recurrence
  · exact d4HypergeometricResonantTruncation_denominator_ne_zero
      (Nat.le_of_lt hj)
  · intro h
    have hcast : (j : ℂ) = (N : ℂ) := by
      linear_combination h
    have : j = N := by
      exact_mod_cast hcast
    omega

/-- The first coefficient beyond the collision is exactly zero under field inverse semantics. -/
@[simp] theorem d4HypergeometricResonantTruncationCoefficient_collision
    (N : ℕ) (a b : ℂ) :
    d4HypergeometricResonantTruncationCoefficient N a b (N + 1) = 0 := by
  simp [d4HypergeometricResonantTruncationCoefficient,
    ordinaryHypergeometricCoefficient,
    ascPochhammer_eval_neg_coe_nat_of_lt]

/-- Closed value of the denominator Pochhammer at its last nonzero index. -/
theorem d4HypergeometricResonantTruncation_pochhammer_self
    (N : ℕ) :
    (ascPochhammer ℂ N).eval (-(N : ℂ)) =
      (-1 : ℂ) ^ N * (N.factorial : ℂ) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self]

/-- The actual ordinary Gauss coefficient at order `N` equals the closed Frobenius top
coefficient. -/
theorem d4HypergeometricResonantTruncationCoefficient_top
    (N : ℕ) (a b : ℂ) :
    d4HypergeometricResonantTruncationCoefficient N a b N =
      d4HypergeometricResonantTruncationTopCoefficient N a b := by
  rw [d4HypergeometricResonantTruncationCoefficient,
    ordinaryHypergeometricCoefficient,
    d4HypergeometricResonantTruncationTopCoefficient,
    d4HypergeometricResonantTruncation_pochhammer_self]
  have hfac : (N.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hsign : (-1 : ℂ) ^ N ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  field_simp
  have hpow : (-1 : ℂ) ^ (N * 2) = 1 := by
    rw [mul_comm, pow_mul]
    norm_num
  rw [← pow_mul, hpow, mul_one]

/-- Every ordinary coefficient above the resonant top order is zero. -/
theorem d4HypergeometricResonantTruncationCoefficient_eq_zero_of_order_lt
    (N : ℕ) (a b : ℂ) (j : ℕ) (hNj : N < j) :
    d4HypergeometricResonantTruncationCoefficient N a b j = 0 := by
  rw [d4HypergeometricResonantTruncationCoefficient,
    ordinaryHypergeometricCoefficient]
  have hp : (ascPochhammer ℂ j).eval (-(N : ℂ)) = 0 :=
    ascPochhammer_eval_neg_coe_nat_of_lt hNj
  rw [hp, inv_zero, mul_zero]

/-- Exact terminal obstruction: the full resonant formal Gauss series is a polynomial, and its
Euler-form differential residual is one monomial at degree `N+1`. -/
theorem ordinaryHypergeometricFormalEulerResidual_resonant_eq_terminalMonomial
    (N : ℕ) (a b : ℂ) :
    ordinaryHypergeometricFormalEulerResidual a b (-(N : ℂ)) =
      PowerSeries.monomial (N + 1)
        (-((a + (N : ℂ)) * (b + (N : ℂ)) *
          d4HypergeometricResonantTruncationTopCoefficient N a b)) := by
  apply PowerSeries.ext
  intro m
  cases m with
  | zero =>
      rw [ordinaryHypergeometricFormalEulerResidual,
        map_sub, map_add, map_add,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_C_mul,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_monomial]
      simp
  | succ j =>
      rw [ordinaryHypergeometricFormalEulerResidual,
        map_sub, map_add, map_add,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_C_mul,
        coeff_hypergeometricEulerOperator,
        coeff_X_mul_succ]
      simp only [map_add, add_mul,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_C_mul,
        ordinaryHypergeometricFormalPowerSeries,
        PowerSeries.coeff_mk,
        PowerSeries.coeff_monomial]
      by_cases hjN : j < N
      · rw [if_neg (by omega)]
        have hrec :
            ((j + 1 : ℕ) : ℂ) * (-(N : ℂ) + (j : ℂ)) *
                ordinaryHypergeometricCoefficient a b (-(N : ℂ)) (j + 1) =
              (a + (j : ℂ)) * (b + (j : ℂ)) *
                ordinaryHypergeometricCoefficient a b (-(N : ℂ)) j := by
          simpa only [d4HypergeometricResonantTruncationCoefficient] using
            d4HypergeometricResonantTruncationCoefficient_succ_recurrence
              N a b j hjN
        dsimp [ordinaryHypergeometricFormalCoefficient]
        rw [Nat.cast_add, Nat.cast_one] at hrec ⊢
        linear_combination hrec
      · by_cases hjeq : j = N
        · subst j
          rw [if_pos rfl]
          have hzero :=
            d4HypergeometricResonantTruncationCoefficient_collision N a b
          have htop :=
            d4HypergeometricResonantTruncationCoefficient_top N a b
          rw [d4HypergeometricResonantTruncationCoefficient] at hzero htop
          dsimp [ordinaryHypergeometricFormalCoefficient]
          rw [hzero, htop]
          push_cast
          ring
        · rw [if_neg (by omega)]
          have hNj : N < j := by omega
          have hzero :=
            d4HypergeometricResonantTruncationCoefficient_eq_zero_of_order_lt
              N a b j hNj
          have hzero' :=
            d4HypergeometricResonantTruncationCoefficient_eq_zero_of_order_lt
              N a b (j + 1) (by omega)
          rw [d4HypergeometricResonantTruncationCoefficient] at hzero hzero'
          dsimp [ordinaryHypergeometricFormalCoefficient]
          rw [hzero, hzero']
          ring

/-- The terminal monomial coefficient is the negative regular-log forcing fixed by the Frobenius
balance. -/
theorem ordinaryHypergeometricFormalEulerResidual_resonant_eq_logForcing
    (N : ℕ) (a b : ℂ) :
    ordinaryHypergeometricFormalEulerResidual a b (-(N : ℂ)) =
      PowerSeries.monomial (N + 1)
        (-(((N + 1 : ℕ) : ℂ) *
          d4HypergeometricResonantFrobeniusLogCoefficient N a b)) := by
  rw [ordinaryHypergeometricFormalEulerResidual_resonant_eq_terminalMonomial,
    d4HypergeometricResonantFrobeniusLogCoefficient_terminalBalance]

/-- Literal complex-momentum mixed BM truncation has exactly the Frobenius logarithmic forcing as
its sole formal differential residual. -/
theorem d4BMMixedHorizonFormalEulerResidual_eq_logForcing
    (n k : ℕ) (chi : ℂ) :
    ordinaryHypergeometricFormalEulerResidual
        (d4BMMixedHorizonComplexA n k chi)
        (d4BMMixedHorizonComplexB n k chi)
        (d4BMCausalRadialC (d4BMCausalPlusMinusFrequency n k chi)) =
      PowerSeries.monomial (d4BMMixedHorizonFrobeniusOrder n k + 1)
        (-(((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℂ) *
          d4HypergeometricResonantFrobeniusLogCoefficient
            (d4BMMixedHorizonFrobeniusOrder n k)
            (d4BMMixedHorizonComplexA n k chi)
            (d4BMMixedHorizonComplexB n k chi))) := by
  rw [d4BMCausalRadialC_plusMinus_eq_negNat]
  simpa [d4BMMixedHorizonFrobeniusOrder] using
    ordinaryHypergeometricFormalEulerResidual_resonant_eq_logForcing
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonComplexA n k chi)
      (d4BMMixedHorizonComplexB n k chi)

end

end RHTower
