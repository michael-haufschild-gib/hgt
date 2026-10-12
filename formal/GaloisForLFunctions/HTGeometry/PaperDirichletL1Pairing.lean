import GaloisForLFunctions.HTGeometry.PaperDirichletPeriodicPrimitive
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-! # Uniform action of the Dirichlet primitives on actual L¹ data

The globally bounded periodic primitives define convolution pairings on the
whole real line. Their common bound controls both values and differences in
the L¹ norm, independently of the Fourier cutoff and translation.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Period

def dirichletPrimitiveConvolution (N : ℕ) (u : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) : ℂ :=
  ∫ y, u y * meanZeroDirichletPrimitive N (t - y)

theorem integrable_dirichletPrimitiveConvolution (N : ℕ)
    (u : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) :
    Integrable (fun y => u y * meanZeroDirichletPrimitive N (t - y)) := by
  apply (L1.integrable_coeFn u).mul_bdd
    (((continuous_meanZeroDirichletPrimitive N).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun y => norm_meanZeroDirichletPrimitive_le N (t - y)

theorem norm_dirichletPrimitiveConvolution_le (N : ℕ)
    (u : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) :
    ‖dirichletPrimitiveConvolution N u t‖ ≤ (5 / 2) * ‖u‖ := by
  have h := norm_integral_le_of_norm_le ((L1.integrable_coeFn u).norm.mul_const (5 / 2))
    (f := fun y => u y * meanZeroDirichletPrimitive N (t - y))
    (Eventually.of_forall fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_meanZeroDirichletPrimitive_le N (t - y))
        (norm_nonneg _))
  rw [integral_mul_const, ← L1.norm_eq_integral_norm] at h
  simpa only [dirichletPrimitiveConvolution, mul_comm] using h

theorem dirichletPrimitiveConvolution_sub (N : ℕ)
    (u v : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) :
    dirichletPrimitiveConvolution N (u - v) t =
      dirichletPrimitiveConvolution N u t - dirichletPrimitiveConvolution N v t := by
  unfold dirichletPrimitiveConvolution
  rw [← integral_sub (integrable_dirichletPrimitiveConvolution N u t)
    (integrable_dirichletPrimitiveConvolution N v t)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with y hy
  rw [hy, Pi.sub_apply, sub_mul]

theorem norm_dirichletPrimitiveConvolution_sub_le (N : ℕ)
    (u v : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) :
    ‖dirichletPrimitiveConvolution N u t - dirichletPrimitiveConvolution N v t‖ ≤
      (5 / 2) * ‖u - v‖ := by
  rw [← dirichletPrimitiveConvolution_sub]
  exact norm_dirichletPrimitiveConvolution_le N (u - v) t

end GaloisForLFunctions.HTGeometry.FourierLLogL.Period
