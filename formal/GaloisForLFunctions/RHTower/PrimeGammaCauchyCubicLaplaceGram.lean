import GaloisForLFunctions.RHTower.PrimeGammaCauchyCubicSignedEulerianCurvature
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Exact ray-Laplace realization of the Route-P Cauchy-cubic kernel

The Route-P zero-ordinate pair kernel is not merely a positive rational expression: it is the
Gram kernel of the literal cubic ray features `t * exp (-x t)` on the positive ray.  This
identifies the exact analytic target for any source-faithful two-port lift of pruned Suzuki
histories.  No path label is discarded in this statement; supplying such labels is the remaining
categorical bridge.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- Cubic positive-ray feature whose Gram kernel is the Route-P Cauchy-cubic edge. -/
def primeGammaCauchyCubicRayFeature (x t : ℝ) : ℝ :=
  t * Real.exp (-(x * t))

/-- The Cauchy-cubic edge is exactly the positive-ray Laplace Gram of its cubic features. -/
theorem primeGammaCauchyCubicEdge_eq_rayLaplaceGram
    {x y : ℝ} (hxy : 0 < x + y) :
    primeGammaCauchyCubicEdge x y =
      ∫ t in Ioi (0 : ℝ),
        primeGammaCauchyCubicRayFeature x t * primeGammaCauchyCubicRayFeature y t := by
  have hgamma_three : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
  unfold primeGammaCauchyCubicEdge primeGammaCauchyCubicRayFeature
  symm
  calc
    (∫ t in Ioi (0 : ℝ),
        (t * Real.exp (-(x * t))) * (t * Real.exp (-(y * t)))) =
        ∫ t in Ioi (0 : ℝ), t ^ ((3 : ℝ) - 1) * Real.exp (-((x + y) * t)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          norm_num
          calc
            t * Real.exp (-(x * t)) * (t * Real.exp (-(y * t))) =
                t ^ 2 * (Real.exp (-(x * t)) * Real.exp (-(y * t))) := by ring
            _ = t ^ 2 * Real.exp (-(x * t) + -(y * t)) := by
              rw [← Real.exp_add]
            _ = t ^ 2 * Real.exp (-((x + y) * t)) := by ring_nf
    _ = (1 / (x + y)) ^ (3 : ℝ) * Real.Gamma 3 :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hxy
    _ = 2 / (x + y) ^ 3 := by
      rw [hgamma_three]
      have hthree : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
      rw [hthree, Real.rpow_natCast, div_pow]
      norm_num
      field_simp [hxy.ne']

/-- The Route-P base kernel at zero ordinate is the complexification of the same ray-Laplace
Gram. -/
theorem routePBaseCauchyCubicKernel_one_zero_eq_rayLaplaceGram
    {x y : ℝ} (hxy : 0 < x + y) :
    routePBaseCauchyCubicKernel 1 x y 0 =
      (∫ t in Ioi (0 : ℝ),
        primeGammaCauchyCubicRayFeature x t * primeGammaCauchyCubicRayFeature y t : ℝ) := by
  rw [routePBaseCauchyCubicKernel_one_zero_eq_primeGammaCauchyCubicEdge]
  exact_mod_cast (primeGammaCauchyCubicEdge_eq_rayLaplaceGram hxy)

end GaloisForLFunctions.HTGeometry
