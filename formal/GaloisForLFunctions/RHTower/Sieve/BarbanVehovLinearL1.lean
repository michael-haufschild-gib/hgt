import GaloisForLFunctions.RHTower.Sieve.GrahamMeanSquare
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory

/-!
# Linear absolute mass of Barban--Vehov weights

Using the exact taper `log(M/q)` and the Stirling lower bound, the absolute coefficient mass is
at most `M`, not the crude `M log M`. Consequently the bilinear absolute mass is at most `M^2`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

theorem abs_barbanVehovWeight_le_log_sub_log
    {M q : ℕ} (hM : 1 ≤ M) (hq : 1 ≤ q) (hqM : q ≤ M) :
    |barbanVehovWeight M q| ≤ Real.log M - Real.log q := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hratio : (1 : ℝ) ≤ (M : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hqR]
    norm_num
    exact_mod_cast hqM
  have hlog0 : 0 ≤ Real.log ((M : ℝ) / (q : ℝ)) := Real.log_nonneg hratio
  rw [barbanVehovWeight, if_pos hqM, abs_mul, abs_of_nonneg hlog0]
  calc
    |(μ q : ℝ)| * Real.log ((M : ℝ) / (q : ℝ)) ≤
        1 * Real.log ((M : ℝ) / (q : ℝ)) :=
      mul_le_mul_of_nonneg_right (abs_moebius_le_one q) hlog0
    _ = Real.log ((M : ℝ) / (q : ℝ)) := one_mul _
    _ = Real.log M - Real.log q := Real.log_div hMR.ne' hqR.ne'

/-- Exact logarithmic taper improves Barban--Vehov `ℓ¹` mass from `M log M` to `M`. -/
theorem sum_abs_barbanVehovWeight_le_linear {M : ℕ} (hM : 1 ≤ M) :
    ∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q| ≤ (M : ℝ) := by
  have hStirling := RHTower.stirling_le_sum_log M hM
  calc
    ∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q| ≤
        ∑ q ∈ Finset.Icc 1 M, (Real.log M - Real.log q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact abs_barbanVehovWeight_le_log_sub_log hM
        (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
    _ = (M : ℝ) * Real.log M -
        ∑ q ∈ Finset.Icc 1 M, Real.log q := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      norm_num
    _ ≤ (M : ℝ) - 1 := by linarith
    _ ≤ (M : ℝ) := by linarith

private theorem sum_product_abs_barbanVehovWeight_eq_sq_linear (M : ℕ) :
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| =
      (∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q|) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [abs_mul]

/-- Bilinear absolute mass is at most `M²`, with no logarithmic loss. -/
theorem sum_product_abs_barbanVehovWeight_le_quadratic
    {M : ℕ} (hM : 1 ≤ M) :
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| ≤
      (M : ℝ) ^ 2 := by
  rw [sum_product_abs_barbanVehovWeight_eq_sq_linear]
  have hs := sum_abs_barbanVehovWeight_le_linear hM
  have hs0 : 0 ≤ ∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  simpa only [pow_two] using mul_self_le_mul_self hs0 hs

end
end RHTower.Sieve

