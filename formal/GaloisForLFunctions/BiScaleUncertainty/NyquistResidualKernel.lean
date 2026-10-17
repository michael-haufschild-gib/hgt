import GaloisForLFunctions.BiScaleUncertainty.NyquistResidualPartition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Integrability and exact mass of the explicit Nyquist residual kernel -/

open MeasureTheory Set Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem integrableOn_nyquistResidualKernel_cell (N k : ℕ) :
    IntegrableOn (nyquistResidualKernel N) (nyquistResidualCell (N + k)) := by
  apply (continuous_nyquistResidualDensity (N + k)).integrableOn_Ioc.congr_fun
    (fun x hx => (nyquistResidualKernel_on_cell N k hx).symm)
    (measurableSet_nyquistResidualCell (N + k))

theorem integral_nyquistResidualKernel_cell (N k : ℕ) :
    (∫ x in nyquistResidualCell (N + k), nyquistResidualKernel N x) =
      nyquistResidualMass (N + k) := by
  rw [nyquistResidualMass, intervalIntegral.integral_of_le
    (strictMono_nyquistResidualNode.monotone (by omega : N + k ≤ N + k + 1))]
  exact setIntegral_congr_fun (measurableSet_nyquistResidualCell (N + k))
    (fun x hx => nyquistResidualKernel_on_cell N k hx)

theorem integral_norm_nyquistResidualKernel_cell (N k : ℕ) :
    (∫ x in nyquistResidualCell (N + k), ‖nyquistResidualKernel N x‖) =
      nyquistResidualMass (N + k) := by
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (nyquistResidualKernel_nonneg N _)]
  exact integral_nyquistResidualKernel_cell N k

theorem integrable_nyquistResidualKernel (N : ℕ) :
    Integrable (nyquistResidualKernel N) := by
  have hi := integrableOn_iUnion_of_summable_integral_norm
    (integrableOn_nyquistResidualKernel_cell N)
    (by simpa only [integral_norm_nyquistResidualKernel_cell] using summable_nyquistResidualMass N)
  rw [iUnion_nyquistResidualCell] at hi
  have hh := hi.integrable_indicator measurableSet_Ioi
  rwa [nyquistResidualKernel_indicator] at hh

theorem integral_nyquistResidualKernel (N : ℕ) :
    (∫ x, nyquistResidualKernel N x) = nyquistResidualTailMass N := by
  calc
    _ = ∫ x in Ioi (nyquistResidualNode N), nyquistResidualKernel N x := by
      rw [← integral_indicator measurableSet_Ioi, nyquistResidualKernel_indicator]
    _ = ∫ x in ⋃ k : ℕ, nyquistResidualCell (N + k), nyquistResidualKernel N x := by
      rw [iUnion_nyquistResidualCell]
    _ = ∑' k : ℕ, ∫ x in nyquistResidualCell (N + k), nyquistResidualKernel N x :=
      integral_iUnion (fun k => measurableSet_nyquistResidualCell (N + k))
        (fun i j hij => pairwise_disjoint_nyquistResidualCell (by omega : N + i ≠ N + j))
        (integrable_nyquistResidualKernel N).integrableOn
    _ = nyquistResidualTailMass N := by
      simp only [integral_nyquistResidualKernel_cell, nyquistResidualTailMass]

theorem integral_norm_nyquistResidualKernel (N : ℕ) :
    (∫ x, ‖nyquistResidualKernel N x‖) = nyquistResidualTailMass N := by
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (nyquistResidualKernel_nonneg N _)]
  exact integral_nyquistResidualKernel N

theorem integrable_mul_nyquistResidualKernel (N : ℕ) (H : ℝ →ᵇ ℝ) :
    Integrable (fun x => H x * nyquistResidualKernel N x) :=
  (integrable_nyquistResidualKernel N).bdd_mul H.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => H.norm_coe_le_norm x)

theorem integral_mul_nyquistResidualKernel_le (N : ℕ) (H : ℝ →ᵇ ℝ) :
    ‖∫ x, H x * nyquistResidualKernel N x‖ ≤ nyquistResidualTailMass N * ‖H‖ := by
  calc
    _ ≤ ∫ x, ‖H‖ * nyquistResidualKernel N x :=
      norm_integral_le_of_norm_le ((integrable_nyquistResidualKernel N).const_mul ‖H‖)
        (Eventually.of_forall fun x => by
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (nyquistResidualKernel_nonneg N x)]
          exact mul_le_mul_of_nonneg_right (H.norm_coe_le_norm x) (nyquistResidualKernel_nonneg N x))
    _ = _ := by rw [integral_const_mul, integral_nyquistResidualKernel, mul_comm]

end
end GaloisForLFunctions.BiScaleUncertainty
