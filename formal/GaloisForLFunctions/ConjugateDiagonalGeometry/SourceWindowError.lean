import GaloisForLFunctions.ConjugateDiagonalGeometry.CommonSourceError
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceMomentLaplacianBound
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianArchimedeanContour

/-!
# Uniform source error in moving arithmetic windows

The common regulator defeats the growth of all fixed-order source moments
uniformly for linearly moving ordinates and logarithmic translation depth.
This controls the compact current error; the omitted divisor tail is a
separate summability question.
-/

open Complex Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open ArithmeticPolarization

/-- The source regulator error after cancelling the actual cutoff derivative norm. -/
theorem sourceMomentCurrentError_le (f : CompactTest) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (j n : ℕ) (L τ : ℝ) :
    |commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
      xiCurrentPairing (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
        ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
          Real.exp (-((n : ℝ) ^ 4) +
            2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) := by
  have hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * sourceDepthKernel (sourceTwist τ f) L j w) z| ≤
        4 ^ j * sourceSquareEnvelope A n τ ((j : ℝ) * |L|) := by
    intro z hz
    have hz' : ‖z‖ ≤ (n : ℝ) + 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right,
        abs_of_pos (by positivity : 0 < (n : ℝ) + 2)] using hz
    simpa only [sourceTranslate_zero, abs_zero, zero_add] using
      abs_laplacian_cutoff_moving_moment_le f hA0 hA L j n 0 τ hz'
  refine (abs_commonSourceReading_sub_current_le _
    (contDiff_sourceDepthKernel (sourceTwist τ f) L j) n hb).trans_eq ?_
  unfold sourceSquareEnvelope sourceLocalAccuracy
  rw [Real.exp_add, pow_succ (4 : ℝ) j]
  field_simp [Real.pi_ne_zero, (sourceCutoffControl_pos n).ne']

/-- A fixed envelope for every ordinate and Hecke scale in the joint source window. -/
def sourceWindowErrorEnvelope (A : ℝ) (j n : ℕ) : ℝ :=
  ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
    Real.exp (-((n : ℝ) ^ 4) + 50 * (n : ℝ) ^ 2 + 56)

theorem sourceWindowErrorEnvelope_nonneg (A : ℝ) (j n : ℕ) :
    0 ≤ sourceWindowErrorEnvelope A j n := by
  unfold sourceWindowErrorEnvelope
  positivity

private theorem source_window_exponent_le (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ)) (hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    -((n : ℝ) ^ 4) +
      2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2)) ≤
        -((n : ℝ) ^ 4) + 50 * (n : ℝ) ^ 2 + 56 := by
  have hsq : ((n : ℝ) + 3 + |τ|) ^ 2 ≤ (2 * (n : ℝ) + 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hτ]) 2
  have hlog : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)
    linarith only [h]
  have hj : (j : ℝ) * |L| ≤ 2 * (n : ℝ) := by linarith only [hL, hlog]
  have hp := mul_le_mul_of_nonneg_right hj (by positivity : 0 ≤ (n : ℝ) + 7 / 2)
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by
    nlinarith only [sq_nonneg ((n : ℝ) - 1 / 2)]
  nlinarith only [hsq, hp, hn]

/-- A single vanishing majorant controls the entire moving source window. -/
theorem sourceMomentCurrentError_le_window (f : CompactTest) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (j n : ℕ) (L τ : ℝ) (hτ : |τ| ≤ (n : ℝ))
    (hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    |commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
      xiCurrentPairing (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
        sourceWindowErrorEnvelope A j n := by
  refine (sourceMomentCurrentError_le f hA0 hA j n L τ).trans ?_
  unfold sourceWindowErrorEnvelope
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (source_window_exponent_le j n L τ hτ hL)) (by positivity)

theorem tendsto_sourceWindowErrorEnvelope (A : ℝ) (j : ℕ) :
    Tendsto (sourceWindowErrorEnvelope A j) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := (RiemannGaussian.tendsto_exp_neg_quadratic_add_linear_atTop
    (ε := 1) zero_lt_one 0 50 56).comp ht
  have he : Tendsto (fun n : ℕ =>
      Real.exp (-((n : ℝ) ^ 4) + 50 * (n : ℝ) ^ 2 + 56)) atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards with n
    change Real.exp (-1 * ((n : ℝ) ^ 2 - 0) ^ 2 + 50 * (n : ℝ) ^ 2 + 56) =
      Real.exp (-((n : ℝ) ^ 4) + 50 * (n : ℝ) ^ 2 + 56)
    apply congrArg Real.exp
    ring
  change Tendsto (fun n : ℕ =>
    ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
      Real.exp (-((n : ℝ) ^ 4) + 50 * (n : ℝ) ^ 2 + 56)) atTop (𝓝 0)
  simpa only [mul_zero] using
    he.const_mul ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2)

/-- Uniform compact-current recovery for actual C² source tests in both moving parameters. -/
theorem commonSourceReading_uniform_cutoff_current (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |commonSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
          xiCurrentPairing (fun z => sourceCutoff n z *
            sourceDepthKernel (sourceTwist τ f) L j z)| < ε := by
  obtain ⟨A, hA1, hA⟩ := norm_tr_le_sourceGaussian f
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_sourceWindowErrorEnvelope A j) ε hε
  refine ⟨N, fun n hn L τ hτ hL => ?_⟩
  have hsmall : sourceWindowErrorEnvelope A j n < ε := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (sourceWindowErrorEnvelope_nonneg A j n)] using hN n hn
  exact (sourceMomentCurrentError_le_window f (by linarith only [hA1]) hA j n L τ hτ hL).trans_lt
    hsmall

end GaloisForLFunctions.ConjugateDiagonalGeometry
