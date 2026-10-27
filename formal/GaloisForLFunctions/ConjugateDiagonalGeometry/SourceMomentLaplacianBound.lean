import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceMovedTests
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceSquareCalculus
import GaloisForLFunctions.ConjugateDiagonalGeometry.CommonSourceMetric

/-!
# Cutoff Laplacians of moving collided moments

The zeroth moment is a holomorphic square. Higher depth moments are obtained
by exact second translation differences, so their differential cost is
controlled without repeatedly differentiating a power of the depth kernel.
-/

open Complex Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open ArithmeticPolarization

/-- Cauchy envelope for the cutoff square at an ordinate and a total translation depth. -/
def sourceSquareEnvelope (A : ℝ) (n : ℕ) (τ d : ℝ) : ℝ :=
  4 * sourceCutoffControl n * A ^ 2 *
    Real.exp (2 * (((n : ℝ) + 3 + |τ|) ^ 2 + d * ((n : ℝ) + 7 / 2)))

theorem sourceSquareEnvelope_nonneg (A : ℝ) (n : ℕ) (τ d : ℝ) :
    0 ≤ sourceSquareEnvelope A n τ d := by
  have hM := (sourceCutoffControl_pos n).le
  unfold sourceSquareEnvelope
  positivity

theorem sourceSquareEnvelope_mono (A : ℝ) (n : ℕ) (τ : ℝ) {d e : ℝ} (h : d ≤ e) :
    sourceSquareEnvelope A n τ d ≤ sourceSquareEnvelope A n τ e := by
  have hM := (sourceCutoffControl_pos n).le
  unfold sourceSquareEnvelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (n : ℝ) + 7 / 2)
  linarith only [hm]

/-- The zeroth-moment differential bound is uniform in both source motions. -/
theorem abs_laplacian_cutoff_moved_square_le (f : CompactTest) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (u τ : ℝ) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ (n : ℝ) + 2) :
    |Δ (fun w => sourceCutoff n w *
      Complex.normSq (tr (sourceTranslate u (sourceTwist τ f)).1 w)) z| ≤
        sourceSquareEnvelope A n τ |u| := by
  have hb := shiftedSourceTransform_disc_bound f hA0 hA u τ
    (by positivity : 0 ≤ (n : ℝ) + 2) hz
  have hr : (n : ℝ) + 2 + 1 + |τ| = (n : ℝ) + 3 + |τ| := by ring
  have hs : (n : ℝ) + 2 + 3 / 2 = (n : ℝ) + 7 / 2 := by ring
  simp only [hr, hs] at hb
  rw [tr_sourceTranslate_sourceTwist]
  calc
    |Δ (fun w => sourceCutoff n w * Complex.normSq (shiftedSourceTransform f u τ w)) z| ≤
        4 * sourceCutoffControl n *
          (A * Real.exp (((n : ℝ) + 3 + |τ|) ^ 2 + |u| * ((n : ℝ) + 7 / 2))) ^ 2 :=
      abs_laplacian_cutoff_normSq_le _ (differentiable_shiftedSourceTransform f u τ)
        n z hb.1 hb.2
    _ = sourceSquareEnvelope A n τ |u| := by
      unfold sourceSquareEnvelope
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      ring

/-- Cutoff differentiation preserves the exact depth-moment translation recurrence. -/
theorem laplacian_cutoff_sourceDepthKernel_succ (f : CompactTest) (L : ℝ) (j n : ℕ) (z : ℂ) :
    Δ (fun w => sourceCutoff n w * sourceDepthKernel f L (j + 1) w) z =
      Δ (fun w => sourceCutoff n w * sourceDepthKernel (sourceTranslate L f) L j w) z +
      Δ (fun w => sourceCutoff n w * sourceDepthKernel (sourceTranslate (-L) f) L j w) z -
        2 * Δ (fun w => sourceCutoff n w * sourceDepthKernel f L j w) z := by
  have hp := (sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel (sourceTranslate L f) L j)
  have hm := (sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel (sourceTranslate (-L) f) L j)
  have h0 := (sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel f L j)
  have hpm : ContDiff ℝ 2
      ((fun w => sourceCutoff n w * sourceDepthKernel (sourceTranslate L f) L j w) +
        (fun w => sourceCutoff n w * sourceDepthKernel (sourceTranslate (-L) f) L j w)) :=
    hp.add hm
  have h2 : ContDiff ℝ 2 ((2 : ℝ) • (fun w => sourceCutoff n w * sourceDepthKernel f L j w)) :=
    contDiff_const.mul h0
  have he : (fun w => sourceCutoff n w * sourceDepthKernel f L (j + 1) w) =
      ((fun w => sourceCutoff n w * sourceDepthKernel (sourceTranslate L f) L j w) +
        (fun w => sourceCutoff n w * sourceDepthKernel (sourceTranslate (-L) f) L j w)) -
        (2 : ℝ) • (fun w => sourceCutoff n w * sourceDepthKernel f L j w) := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← sourceDepthKernel_second_difference]
    ring
  rw [he, hpm.contDiffAt.laplacian_sub h2.contDiffAt,
    hp.contDiffAt.laplacian_add hm.contDiffAt,
    InnerProductSpace.laplacian_smul (2 : ℝ) h0.contDiffAt]
  rfl

/-- All finite depth moments have one differential envelope, uniform in ordinate and translation. -/
theorem abs_laplacian_cutoff_moving_moment_le (f : CompactTest) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (L : ℝ) (j n : ℕ) (u τ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ (n : ℝ) + 2) :
    |Δ (fun w => sourceCutoff n w *
      sourceDepthKernel (sourceTranslate u (sourceTwist τ f)) L j w) z| ≤
        4 ^ j * sourceSquareEnvelope A n τ (|u| + (j : ℝ) * |L|) := by
  induction j generalizing u with
  | zero =>
      simpa only [sourceDepthKernel, pow_zero, mul_one, Nat.cast_zero, zero_mul,
        add_zero, one_mul] using abs_laplacian_cutoff_moved_square_le f hA0 hA u τ n hz
  | succ j ih =>
      have hplus : |u + L| + (j : ℝ) * |L| ≤ |u| + ((j + 1 : ℕ) : ℝ) * |L| := by
        have h := abs_add_le u L
        push_cast
        nlinarith only [h]
      have hminus : |u + -L| + (j : ℝ) * |L| ≤ |u| + ((j + 1 : ℕ) : ℝ) * |L| := by
        have h := abs_add_le u (-L)
        rw [abs_neg] at h
        push_cast
        nlinarith only [h]
      have hself : |u| + (j : ℝ) * |L| ≤ |u| + ((j + 1 : ℕ) : ℝ) * |L| := by
        push_cast
        nlinarith only [abs_nonneg L]
      have hp := (ih (u + L)).trans (mul_le_mul_of_nonneg_left
        (sourceSquareEnvelope_mono A n τ hplus) (by positivity : 0 ≤ (4 : ℝ) ^ j))
      have hm := (ih (u + -L)).trans (mul_le_mul_of_nonneg_left
        (sourceSquareEnvelope_mono A n τ hminus) (by positivity : 0 ≤ (4 : ℝ) ^ j))
      have h0 := (ih u).trans (mul_le_mul_of_nonneg_left
        (sourceSquareEnvelope_mono A n τ hself) (by positivity : 0 ≤ (4 : ℝ) ^ j))
      have he := laplacian_cutoff_sourceDepthKernel_succ
        (sourceTranslate u (sourceTwist τ f)) L j n z
      rw [sourceTranslate_add, sourceTranslate_add] at he
      rw [he, pow_succ]
      have ha := abs_add_le
        (Δ (fun w => sourceCutoff n w *
          sourceDepthKernel (sourceTranslate (u + L) (sourceTwist τ f)) L j w) z)
        (Δ (fun w => sourceCutoff n w *
          sourceDepthKernel (sourceTranslate (u + -L) (sourceTwist τ f)) L j w) z)
      have hs := abs_sub
        (Δ (fun w => sourceCutoff n w *
          sourceDepthKernel (sourceTranslate (u + L) (sourceTwist τ f)) L j w) z +
          Δ (fun w => sourceCutoff n w *
            sourceDepthKernel (sourceTranslate (u + -L) (sourceTwist τ f)) L j w) z)
        (2 * Δ (fun w => sourceCutoff n w *
          sourceDepthKernel (sourceTranslate u (sourceTwist τ f)) L j w) z)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
      nlinarith only [hp, hm, h0, ha, hs]

end GaloisForLFunctions.ConjugateDiagonalGeometry
