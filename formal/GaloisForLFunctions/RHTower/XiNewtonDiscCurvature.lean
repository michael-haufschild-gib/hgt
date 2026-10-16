import GaloisForLFunctions.RHTower.XiNewtonDiscSourceMargin
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Curvature of the Xi Newton disc margin

The margin is subharmonic inside its disc: its Laplacian is exactly
`4 * (r² - |z-c|²) * |xi''(z)|²`. Thus a boundary lower bound cannot be
propagated inward by a minimum principle. A source proof must also control
the interior curvature defect.
-/

open Complex Metric Set Filter Topology InnerProductSpace
open scoped ContDiff

noncomputable section

namespace RHTower.XiNewtonCriticalLine

private theorem laplacian_normSq_analytic {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    Laplacian.laplacian (fun w => normSq (f w)) z = 4 * normSq (deriv f z) := by
  have hc : ContDiffAt ℝ 2 f z := hf.contDiffAt.restrict_scalars ℝ
  have hzero : Laplacian.laplacian f z = 0 := hf.harmonicAt.2.self_of_nhds
  have hs := hc.laplacian_norm_sq
  rw [hzero, inner_zero_right, mul_zero, zero_add,
    ContinuousLinearMap.hilbertSchmidtInner_eq_sum Complex.orthonormalBasisOneI] at hs
  have hfd (v : ℂ) : fderiv ℝ f z v = deriv f z * v := by
    rw [hf.differentiableAt.fderiv_restrictScalars ℝ]
    exact fderiv_eq_deriv_mul
  simp only [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one, hfd,
    real_inner_self_eq_norm_sq, mul_one, norm_mul, norm_one, Complex.norm_I] at hs
  simp_rw [Complex.normSq_eq_norm_sq]
  linarith [hs]

private theorem contDiffAt_normSq_analytic {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : ContDiffAt ℝ 2 (fun w => normSq (f w)) z := by
  have hc : ContDiffAt ℝ 2 f z := hf.contDiffAt.restrict_scalars ℝ
  simpa only [Complex.normSq_eq_norm_sq] using hc.norm_sq ℝ

/-- The exact curvature of the quotient-free Xi Newton margin. -/
theorem laplacian_xiNewtonDiscMargin (c z : ℂ) (r : ℝ) :
    Laplacian.laplacian (xiNewtonDiscMargin c r) z =
      4 * (r ^ 2 - normSq (z - c)) * normSq (deriv (deriv xi) z) := by
  have hx : AnalyticAt ℂ xi z := xi_analyticOnNhd_univ z (mem_univ z)
  let A : ℂ → ℂ := fun w => (w - c) * deriv xi w - xi w
  have hA : AnalyticAt ℂ A z :=
    ((analyticAt_id.sub analyticAt_const).mul hx.deriv).sub hx
  have hAd : deriv A z = (z - c) * deriv (deriv xi) z := by
    have h := (((hasDerivAt_id z).sub_const c).mul
      hx.deriv.differentiableAt.hasDerivAt).sub hx.differentiableAt.hasDerivAt
    change HasDerivAt A
      (1 * deriv xi z + (z - c) * deriv (deriv xi) z - deriv xi z) z at h
    calc
      deriv A z = 1 * deriv xi z + (z - c) * deriv (deriv xi) z - deriv xi z := h.deriv
      _ = (z - c) * deriv (deriv xi) z := by ring
  have hd := contDiffAt_normSq_analytic hx.deriv
  have ha := contDiffAt_normSq_analytic hA
  change Laplacian.laplacian
    (fun w => r ^ 2 * normSq (deriv xi w) - normSq (A w)) z = _
  have hrd : ContDiffAt ℝ 2 (fun w => r ^ 2 * normSq (deriv xi w)) z :=
    contDiffAt_const.mul hd
  rw [hrd.laplacian_sub ha]
  have hscale := laplacian_smul (r ^ 2) hd
  change Laplacian.laplacian (fun w => r ^ 2 * normSq (deriv xi w)) z =
    r ^ 2 * Laplacian.laplacian (fun w => normSq (deriv xi w)) z at hscale
  rw [hscale, laplacian_normSq_analytic hx.deriv, laplacian_normSq_analytic hA,
    hAd, Complex.normSq_mul]
  ring

/-- Curvature is nonnegative everywhere on the closed source disc. -/
theorem laplacian_xiNewtonDiscMargin_nonneg (c : ℂ) (r : ℝ) :
    ∀ z ∈ closedBall c r, 0 ≤ Laplacian.laplacian (xiNewtonDiscMargin c r) z := by
  intro z hz
  rw [laplacian_xiNewtonDiscMargin]
  have hn : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr : 0 ≤ r := (norm_nonneg _).trans hn
  have hs : normSq (z - c) ≤ r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z - c)]
  exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hs)) (normSq_nonneg _)

end RHTower.XiNewtonCriticalLine
