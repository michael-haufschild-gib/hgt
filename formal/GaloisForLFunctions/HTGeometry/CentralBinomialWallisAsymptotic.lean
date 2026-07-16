import Mathlib.Analysis.SpecialFunctions.Stirling
import GaloisForLFunctions.HTGeometry.ArcsineCentralBinomial

/-!
# Central-binomial asymptotics from the Wallis product

The Wallis product gives an exact finite identity for the normalized central-binomial
coefficient.  Passing to the already formalized Wallis limit proves

`sqrt(n) * centralBinom(n) / 4^n -> 1 / sqrt(pi)`.

This is the coefficient asymptotic needed by square-root Bernstein kernels.
-/

open Filter Topology
open scoped BigOperators Nat Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The central-binomial coefficient normalized by its exponential base `4^n`. -/
def normalizedCentralBinom (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / 4 ^ n

/-- Exact Wallis identity for the squared normalized central-binomial coefficient. -/
theorem wallis_mul_normalizedCentralBinom_sq (n : ℕ) :
    Real.Wallis.W n * normalizedCentralBinom n ^ 2 = 1 / (2 * n + 1 : ℝ) := by
  rw [Real.Wallis.W_eq_factorial_ratio, normalizedCentralBinom,
    Nat.centralBinom_eq_two_mul_choose,
    Nat.cast_choose ℝ (show n ≤ 2 * n by omega)]
  have hsub : 2 * n - n = n := by omega
  rw [hsub]
  have hnfac : ((n ! : ℕ) : ℝ) ≠ 0 := by positivity
  have h2nfac : (((2 * n) ! : ℕ) : ℝ) ≠ 0 := by positivity
  have h4pow : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hodd : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hnfac, h2nfac, h4pow, hodd]
  ring_nf
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  congr 1
  omega

/-- The square of the half-order normalized central-binomial coefficient tends to `1 / pi`. -/
theorem tendsto_sqrtNat_mul_normalizedCentralBinom_sq :
    Tendsto
      (fun n : ℕ => (Real.sqrt n * normalizedCentralBinom n) ^ 2)
      atTop (nhds (1 / Real.pi)) := by
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (2 * n + 1))
      atTop (nhds (1 / 2)) := Stirling.tendsto_self_div_two_mul_self_add_one
  have hwallis : Tendsto Real.Wallis.W atTop (nhds (Real.pi / 2)) :=
    Real.Wallis.tendsto_W_nhds_pi_div_two
  have hquot := hratio.div hwallis (by positivity : Real.pi / 2 ≠ 0)
  convert hquot using 1
  · funext n
    have hW : 0 < Real.Wallis.W n := Real.Wallis.W_pos n
    have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    rw [mul_pow, hsqrt]
    have hid := wallis_mul_normalizedCentralBinom_sq n
    change (n : ℝ) * normalizedCentralBinom n ^ 2 =
      ((n : ℝ) / (2 * n + 1)) / Real.Wallis.W n
    rw [eq_div_iff hW.ne']
    calc
      (n : ℝ) * normalizedCentralBinom n ^ 2 * Real.Wallis.W n =
          (n : ℝ) * (Real.Wallis.W n * normalizedCentralBinom n ^ 2) := by ring
      _ = (n : ℝ) * (1 / (2 * n + 1 : ℝ)) := by rw [hid]
      _ = (n : ℝ) / (2 * n + 1) := by ring
  · congr 1
    field_simp [Real.pi_ne_zero]

/-- **Central-binomial half-order asymptotic.** -/
theorem tendsto_sqrtNat_mul_normalizedCentralBinom :
    Tendsto
      (fun n : ℕ => Real.sqrt n * normalizedCentralBinom n)
      atTop (nhds (1 / Real.sqrt Real.pi)) := by
  have hsquare := tendsto_sqrtNat_mul_normalizedCentralBinom_sq
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  convert hsqrt using 1
  · funext n
    simp only [Function.comp_apply]
    rw [Real.sqrt_sq]
    exact mul_nonneg (Real.sqrt_nonneg _) (by
      exact div_nonneg (by positivity) (by positivity))
  · rw [Real.sqrt_div (by positivity : 0 ≤ (1 : ℝ))]
    simp only [Real.sqrt_one, one_div]

end

end GaloisForLFunctions.HTGeometry
