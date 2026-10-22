import GaloisForLFunctions.RHTower.Suzuki.SuzukiEndpointRegularKernelAsymptotic
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszMarkovTransform

/-!
# Endpoint-scale cancellation for actual Suzuki prime atoms

At a natural aperture `N`, the literal prime-wall coefficient has a `sqrt N` denominator while
the regular Suzuki kernel at endpoint distance `q` has `sqrt N` growth.  They cancel *before*
any prime/polar source is summed.  The surviving coefficient is the fixed Laplace density, plus
an explicit source-weighted Binet error.  Thus this is a source-faithful reduction of the moving
endpoint band, not an absolute-value estimate of the completed source.
-/

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Exact endpoint cancellation of the natural-aperture square-root scale on each literal
von-Mangoldt atom. -/
theorem endpoint_prime_regular_exact
    {N k : ℕ} {q : ℝ} (hN : 0 < N) (hq : q < Real.log (N : ℝ)) :
    (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
        screwRegularKernel (Real.log (N : ℝ) - q) =
      ArithmeticFunction.vonMangoldt k *
        (Real.exp (-q / 2) -
          Real.exp (-3 * Real.log (N : ℝ) + 5 * q / 2) /
            (1 - Real.exp (-2 * Real.log (N : ℝ) + 2 * q))) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) :=
    sqrt_eq_exp_log_div_two hNR
  have hinv : (Real.sqrt (N : ℝ))⁻¹ = Real.exp (-(Real.log (N : ℝ) / 2)) := by
    rw [hsqrt, Real.exp_neg]
  have hkernel := exp_neg_mul_screwRegularKernel
    (a := Real.log (N : ℝ) / 2) (u := q) (by linarith)
  rw [div_eq_mul_inv, hinv]
  calc
    ArithmeticFunction.vonMangoldt k * Real.exp (-(Real.log (N : ℝ) / 2)) *
        screwRegularKernel (Real.log (N : ℝ) - q) =
      ArithmeticFunction.vonMangoldt k *
        (Real.exp (-(Real.log (N : ℝ) / 2)) *
          screwRegularKernel (2 * (Real.log (N : ℝ) / 2) - q)) := by ring
    _ = _ := by
      rw [hkernel]
      congr 3 <;> ring

/-- On every fixed endpoint window, the literal prime-wall atom differs from its Laplace
main term by the explicit Binet error.  The bound retains the von-Mangoldt coefficient rather
than replacing the arithmetic source by an unsigned aggregate. -/
theorem abs_endpoint_prime_regular_sub_laplace_le
    {N k : ℕ} {q L T : ℝ} (hN : 0 < N) (hT : 0 < T)
    (hqL : q ≤ 2 * L) (hTq : T ≤ Real.log (N : ℝ) - q) :
    |(ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
        screwRegularKernel (Real.log (N : ℝ) - q) -
      ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| ≤
      ArithmeticFunction.vonMangoldt k *
        (Real.exp (-3 * Real.log (N : ℝ) + 5 * L) /
          (1 - Real.exp (-2 * T))) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) :=
    sqrt_eq_exp_log_div_two hNR
  have hinv : (Real.sqrt (N : ℝ))⁻¹ = Real.exp (-(Real.log (N : ℝ) / 2)) := by
    rw [hsqrt, Real.exp_neg]
  have hkernel := abs_exp_neg_mul_screwRegularKernel_sub_le
    (a := Real.log (N : ℝ) / 2) (u := q) (L := L) (T := T) hT hqL (by linarith)
  rw [div_eq_mul_inv, hinv]
  have hrewrite :
      ArithmeticFunction.vonMangoldt k * Real.exp (-(Real.log (N : ℝ) / 2)) *
          screwRegularKernel (Real.log (N : ℝ) - q) -
        ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2) =
      ArithmeticFunction.vonMangoldt k *
        (Real.exp (-(Real.log (N : ℝ) / 2)) *
          screwRegularKernel (2 * (Real.log (N : ℝ) / 2) - q) -
          Real.exp (-q / 2)) := by
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hexponent :
      -6 * (Real.log (N : ℝ) / 2) + 5 * L =
        -3 * Real.log (N : ℝ) + 5 * L := by ring
  rw [hexponent] at hkernel
  exact mul_le_mul_of_nonneg_left hkernel ArithmeticFunction.vonMangoldt_nonneg

end

end GaloisForLFunctions.RHTower
