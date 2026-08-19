import GaloisForLFunctions.RHTower.Sieve.CoprimeHarmonicDefect

/-!
# The modulus constant of the coprime harmonic asymptotic

The coprime harmonic asymptotic carries the modulus-dependent constant
`γ_e = ∑_{f ∣ e} (μ(f)/f) log f`.  It is bounded by `log e` times the reciprocal divisor sum, and
the reciprocal divisor sum is dominated by the harmonic sum of the window.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

theorem divisors_subset_Icc {e : ℕ} (he : 0 < e) : e.divisors ⊆ Finset.Icc 1 e := by
  intro f hf
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hf,
    Nat.le_of_dvd he (Nat.dvd_of_mem_divisors hf)⟩

theorem sum_inv_divisors_le {e : ℕ} (he : 0 < e) :
    ∑ f ∈ e.divisors, 1 / (f : ℝ) ≤ ∑ j ∈ Finset.Icc 1 e, 1 / (j : ℝ) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (divisors_subset_Icc he) ?_
  intro j hj _
  obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp hj
  have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  positivity

/-- **The modulus constant is bounded by `log e` times the reciprocal divisor sum.** -/
theorem abs_sum_moebius_log_div_divisors_le {e : ℕ} (he : 0 < e) :
    |∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) / (f : ℝ) * Real.log (f : ℝ)|
      ≤ Real.log (e : ℝ) * ∑ f ∈ e.divisors, 1 / (f : ℝ) := by
  have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hloge : (0 : ℝ) ≤ Real.log (e : ℝ) := Real.log_nonneg heR
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf0
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf0
  have hfe : (f : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast Nat.le_of_dvd he (Nat.dvd_of_mem_divisors hf)
  have hlogf : (0 : ℝ) ≤ Real.log (f : ℝ) := Real.log_nonneg hf1
  have hlogle : Real.log (f : ℝ) ≤ Real.log (e : ℝ) := Real.log_le_log hfR hfe
  rw [abs_mul, abs_of_nonneg hlogf, abs_div, abs_of_pos hfR]
  have hmu : |((μ f : ℤ) : ℝ)| / (f : ℝ) ≤ 1 / (f : ℝ) :=
    div_le_div_of_nonneg_right (abs_moebius_le_one f) hfR.le
  calc |((μ f : ℤ) : ℝ)| / (f : ℝ) * Real.log (f : ℝ)
      ≤ (1 / (f : ℝ)) * Real.log (f : ℝ) := mul_le_mul_of_nonneg_right hmu hlogf
    _ ≤ (1 / (f : ℝ)) * Real.log (e : ℝ) := mul_le_mul_of_nonneg_left hlogle (by positivity)
    _ = Real.log (e : ℝ) * (1 / (f : ℝ)) := by ring

end RHTower.Sieve
