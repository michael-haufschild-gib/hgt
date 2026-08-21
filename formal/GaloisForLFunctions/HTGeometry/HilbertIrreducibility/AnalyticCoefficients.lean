/-
# Analyticity of the coefficients of a product of scaled linear factors

If `c` and the `vᵢ` are analytic at `s₀`, so is every coefficient of
`∏ᵢ (C (c s) * X - C (vᵢ s))`, by the same one-step coefficient recursion that gives integrality.
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

/-- Coefficients of a product of scaled linear factors depend analytically on the parameter. -/
theorem analyticAt_coeff_prod {ι : Type*} (T : Finset ι) {s₀ : ℂ} {c : ℂ → ℂ} {v : ι → ℂ → ℂ}
    (hc : AnalyticAt ℂ c s₀) (hv : ∀ i, AnalyticAt ℂ (v i) s₀) (k : ℕ) :
    AnalyticAt ℂ (fun s => (∏ i ∈ T, (Polynomial.C (c s) * Polynomial.X
      - Polynomial.C (v i s))).coeff k) s₀ := by
  classical
  induction T using Finset.induction_on generalizing k with
  | empty =>
      simp only [Finset.prod_empty, Polynomial.coeff_one]
      by_cases hk : k = 0
      · simp only [if_pos hk]; exact analyticAt_const
      · simp only [if_neg hk]; exact analyticAt_const
  | insert a T ha ih =>
      have hrw : ∀ s : ℂ, (∏ i ∈ insert a T, (Polynomial.C (c s) * Polynomial.X
          - Polynomial.C (v i s))).coeff k
          = c s * (Polynomial.X * ∏ i ∈ T, (Polynomial.C (c s) * Polynomial.X
              - Polynomial.C (v i s))).coeff k
            - v a s * (∏ i ∈ T, (Polynomial.C (c s) * Polynomial.X
              - Polynomial.C (v i s))).coeff k := by
        intro s
        rw [Finset.prod_insert ha, sub_mul, Polynomial.coeff_sub, mul_assoc,
          Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
      simp only [hrw]
      cases k with
      | zero =>
          have h0 : ∀ s : ℂ, (Polynomial.X * ∏ i ∈ T, (Polynomial.C (c s) * Polynomial.X
              - Polynomial.C (v i s))).coeff 0 = 0 := by
            intro s
            simp [Polynomial.mul_coeff_zero]
          simp only [h0, mul_zero, zero_sub]
          exact ((hv a).mul (ih 0)).neg
      | succ k =>
          simp only [Polynomial.coeff_X_mul]
          exact (hc.mul (ih k)).sub ((hv a).mul (ih (k + 1)))

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
