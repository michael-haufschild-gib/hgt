import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteParityEvaluation
import GaloisForLFunctions.RHTower.RadialLeakageWeakConvergence
import GaloisForLFunctions.RHTower.RadialLeakageWeakConvergenceTransfer
import GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum
import GaloisForLFunctions.RHTower.ConstrainedProlatePrimeShiftDoubleSum
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass

/-!
# Independent normalization audit for the constrained prolate arithmetic dilation operator

This module performs the exact mathematical audit and formal cross-verification of all
normalizing factors, mass balances, and operator trace constants appearing throughout the
constrained prolate arithmetic dilation theory:

1. **Hermite Ground State Floor Fraction**:
   `h₀(0)² / (h₀(0)² + h₄(0)²) = 8/11`.
2. **Radial Leakage Arcsine Tail Mass**:
   `∫₁^∞ ν_∞(x) dx = 4/11`, and `∫_k^∞ ν_∞(x) dx = (8 / (11 π)) arcsin(1/k)`.
3. **Symmetrized Dilation Weights**:
   `w_k = (1/k) ∫_k^∞ ν_∞(x) dx = 8 / (11 π k) arcsin(1/k)`.
4. **Arithmetic Eigenvalues**:
   `κ_k = 2 log(k) w_k = 16 log(k) / (11 π k) arcsin(1/k)`.
5. **Trace-Shadow Identification**:
   `Tr(A_∞) = ∑_{k≥2} κ_k = - \mathcal{D}_{prime}`.
6. **Dirichlet Convolution Half-Trace Balance**:
   `∑_{q≥2, j≥1} (Λ(q)/q) (arcsin(1/(qj))/j) = (1/2) Tr(A_∞) = -(1/2) \mathcal{D}_{prime}`.
-/

open RHTower GaloisForLFunctions MeasureTheory

namespace RHTower

/-- **Audit theorem 1**: The positive-sector Hermite ground state floor fraction evaluates
to exactly `8/11`. -/
theorem normalization_audit_hermite_floor_eq_eight_elevenths :
    hermiteOriginSq 0 / (hermiteOriginSq 0 + hermiteOriginSq 2) = 8 / 11 :=
  positive_sector_hermite_floor_ratio_eq

/-- **Audit theorem 2**: The limiting radial leakage density `ν_∞` has exact total mass `4/11`
on `[1, ∞)`. -/
theorem normalization_audit_total_leakage_mass_eq_four_elevenths :
    ∫ x in Set.Ioi (1 : ℝ), nuInfinityDensity x = 4 / 11 :=
  integral_Ioi_one_nuInfinityDensity

/-- **Audit theorem 3**: The symmetrized dilation weight `w_k` is exactly `1/k` times the
tail mass `∫_k^∞ ν_∞(x) dx`. -/
theorem normalization_audit_weight_eq_tail_mass (k : ℝ) (hk : 1 ≤ k) :
    (1 / k) * (∫ x in Set.Ioi k, nuInfinityDensity x) =
      (8 / (11 * Real.pi * k)) * Real.arcsin (1 / k) := by
  rw [integral_Ioi_nuInfinityDensity hk]
  ring

/-- **Audit theorem 4**: The arithmetic eigenvalue `κ_k` is algebraically identical to
`2 * log(k) * w_k`. -/
theorem normalization_audit_eigenvalue_eq_two_mul_log_mul (n : ℕ) :
    constrainedProlateArithmeticEigenvalue n =
      2 * Real.log (((n + 2 : ℕ) : ℝ)) *
        (8 / (11 * Real.pi * ((n + 2 : ℕ) : ℝ)) * Real.arcsin (1 / ((n + 2 : ℕ) : ℝ))) := by
  rw [constrainedProlateArithmeticEigenvalue, constrainedProlatePrimeSeriesTerm]
  ring

/-- **Audit theorem 5**: The operator trace `Tr(A_∞) = ∑ κ_k` equals the exact negative
of the scalar prime constant `\mathcal{D}_{prime}`. -/
theorem normalization_audit_trace_eq_neg_primeConstant :
    ∑' n : ℕ, constrainedProlateArithmeticEigenvalue n = - constrainedProlatePrimeConstant :=
  tsum_constrainedProlateArithmeticEigenvalue.trans (by ring)

/-- **Audit theorem 6**: The double-sum Dirichlet divisor reindexing balances with exactly
half of the total operator trace. -/
theorem normalization_audit_dirichlet_eq_half_trace :
    primeShiftUnsignedResponseConstant =
      (1 / 2) * (∑' n : ℕ, constrainedProlateArithmeticEigenvalue n) :=
  primeShiftUnsignedResponseConstant_eq_half_arithmeticTrace

end RHTower
