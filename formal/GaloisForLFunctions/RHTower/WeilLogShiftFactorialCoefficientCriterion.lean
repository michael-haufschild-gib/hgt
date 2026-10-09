import GaloisForLFunctions.RHTower.WeilLogShiftUniformKernelComparison
import GaloisForLFunctions.RHTower.WeilLogShiftFactorialNormalization

/-!
# Factorial regularity is intrinsic to the unweighted coefficients

At the moving shift `log n`, the paired kernel has a fixed positive lower
bound. Uniform shift comparison therefore removes the kernel without
changing factorial order. This also identifies the native recovery criterion
with factorial regularity of its unweighted recovered deviations.
-/

open Real Zeta23

noncomputable section

namespace RHTower

open WeilExcess

/-- A moving shift exposes each coefficient with a fixed positive kernel weight. -/
theorem riemannAutocorr_zero_le_pairedLogKernel_log (n : ℕ) :
    riemannAutocorr 0 ≤ pairedLogKernel (log n) n := by
  simpa only [pairedLogKernel, sub_self] using
    le_add_of_nonneg_left (riemannAutocorr_nonneg (log n + log n))

/-- Multiplication by any fixed shifted kernel preserves each factorial-order
class exactly; its exponential decay changes only the exponential rate. -/
theorem kernelPotential_factorial_order_iff_coefficient
    (v : ℕ → ℝ) (m : ℕ) (c : ℝ) :
    (∃ (A D : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      |v n * pairedLogKernel c n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) ↔
    (∃ (A D : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      |v n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) := by
  constructor
  · rintro ⟨A, D, N, hv⟩
    obtain ⟨B, C, _, hbound⟩ := exists_kernelPotential_uniform_factorial_envelope v c m A D N hv
    refine ⟨B, C / riemannAutocorr 0, N, fun n hn => ?_⟩
    calc
      |v n| ≤ (C * exp (B * n) * (n.factorial : ℝ) ^ m) / riemannAutocorr 0 := by
        apply (le_div_iff₀ (riemannAutocorr_pos 0)).mpr
        calc
          _ ≤ |v n| * pairedLogKernel (log n) n :=
            mul_le_mul_of_nonneg_left (riemannAutocorr_zero_le_pairedLogKernel_log n)
              (abs_nonneg (v n))
          _ = |v n * pairedLogKernel (log n) n| := by
            rw [abs_mul, abs_of_pos (pairedLogKernel_pos (log n) n)]
          _ ≤ _ := hbound (log n) n hn
      _ = _ := by ring
  · rintro ⟨A, D, N, hv⟩
    refine ⟨A, (2 * riemannAutocorr 0) * |D|, N, fun n hn => ?_⟩
    have hsource : |v n| ≤ |D| * exp (A * n) * (n.factorial : ℝ) ^ m := by
      refine (hv n hn).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self D) (exp_pos _).le) (by positivity)
    calc
      |v n * pairedLogKernel c n| = |v n| * pairedLogKernel c n := by
        rw [abs_mul, abs_of_pos (pairedLogKernel_pos c n)]
      _ ≤ (|D| * exp (A * n) * (n.factorial : ℝ) ^ m) * (2 * riemannAutocorr 0) :=
        mul_le_mul hsource (pairedLogKernel_le_two_mul_riemannAutocorr_zero c n)
          (pairedLogKernel_pos c n).le (by positivity)
      _ = _ := by ring

/-- Finite factorial regularity is exactly regularity of the unweighted sequence. -/
theorem weilLogShiftHasFactorialMajorant_kernelPotential_iff_coefficient
    (v : ℕ → ℝ) (c : ℝ) :
    WeilLogShiftHasFactorialMajorant (fun n => v n * pairedLogKernel c n) ↔
      WeilLogShiftHasFactorialMajorant v := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (kernelPotential_factorial_order_iff_coefficient v m c).mp hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (kernelPotential_factorial_order_iff_coefficient v m c).mpr hm⟩

/-- The native criterion depends only on recovered deviations, even for
histories with no boundedness hypothesis. -/
theorem weilLogShiftHasFactorialMajorant_recovery_coefficients_iff
    (h : ℕ → ℝ) (y : ℝ) :
    WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment y h) ↔
      WeilLogShiftHasFactorialMajorant (weilDeviation (weilLogShiftRecoveryInverse h)) :=
  weilLogShiftHasFactorialMajorant_kernelPotential_iff_coefficient
    (weilDeviation (weilLogShiftRecoveryInverse h)) y

/-- A majorant at one shift is equivalent to summability of a factorial and
exponential normalization of the unweighted coefficients themselves. -/
theorem weilLogShiftHasFactorialMajorant_iff_summable_coefficient_normalization
    (v : ℕ → ℝ) (c : ℝ) :
    WeilLogShiftHasFactorialMajorant (fun n => v n * pairedLogKernel c n) ↔
      ∃ (m : ℕ) (B : ℝ), 0 < B ∧
        Summable (fun n : ℕ => exp (-(B * n)) * v n / (n.factorial : ℝ) ^ m) :=
  (weilLogShiftHasFactorialMajorant_kernelPotential_iff_coefficient v c).trans
    (weilLogShiftHasFactorialMajorant_iff_exists_summable_normalization v)

end RHTower
