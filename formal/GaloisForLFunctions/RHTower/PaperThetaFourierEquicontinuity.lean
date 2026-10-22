import GaloisForLFunctions.RHTower.PaperThetaDerivativeL1
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalL1Translation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! # Equicontinuity of all native symmetric source sums

Real L¹ translation continuity and the uniform Dirichlet primitive bound
give one continuity modulus for every Fourier cutoff.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

theorem dirichletPrimitiveConvolution_translate (N : ℕ)
    (u : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) :
    Period.dirichletPrimitiveConvolution N u t =
      Period.dirichletPrimitiveConvolution N (realL1Translate t u) 0 := by
  unfold Period.dirichletPrimitiveConvolution
  calc
    _ = ∫ y, u (t + y) * Period.meanZeroDirichletPrimitive N (-y) := by
      have h := integral_add_left_eq_self (μ := (volume : Measure ℝ))
        (fun y => u y * Period.meanZeroDirichletPrimitive N (t - y)) t
      simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [realL1Translate_ae t u] with y hy
      rw [hy, zero_sub]

theorem equicontinuous_dirichletPrimitiveConvolution (u : Lp ℂ 1 (volume : Measure ℝ)) :
    Equicontinuous (fun N : ℕ => Period.dirichletPrimitiveConvolution N u) := by
  intro t
  let b : ℝ → ℝ := fun s => (5 / 2) * ‖realL1Translate t u - realL1Translate s u‖
  have hb : Continuous b :=
    continuous_const.mul ((continuous_const.sub (continuous_realL1Translate u)).norm)
  have hlim : Tendsto b (𝓝 t) (𝓝 0) := by
    simpa only [b, sub_self, norm_zero, mul_zero] using hb.tendsto t
  apply Metric.equicontinuousAt_of_continuity_modulus b hlim
  exact Eventually.of_forall fun s N => by
    rw [dirichletPrimitiveConvolution_translate N u t,
      dirichletPrimitiveConvolution_translate N u s, dist_eq_norm]
    exact Period.norm_dirichletPrimitiveConvolution_sub_le N
      (realL1Translate t u) (realL1Translate s u) 0

/-- A common modulus controls the original source sums at every real coordinate. -/
theorem equicontinuous_sourcePartialSum (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    Equicontinuous (fun N : ℕ => sourcePartialSum z.val N) := by
  intro t
  have h := equicontinuous_dirichletPrimitiveConvolution (closedQuantileDerivativeL1 z) t
  rw [Metric.equicontinuousAt_iff_right] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with s hs N
  simpa only [sourcePartialSum_eq_L1_derivative_convolution z, dist_add_left] using hs N

end RHTower.PaperThetaEndpoint
