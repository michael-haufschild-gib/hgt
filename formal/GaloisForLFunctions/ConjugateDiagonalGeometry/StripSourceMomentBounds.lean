import GaloisForLFunctions.ConjugateDiagonalGeometry.StripSourceCutoff
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceStripTransformBounds
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceMomentLaplacianBound

/-!
# Moment Laplacians on the fixed-strip exhaustion

Cauchy control on a fixed vertical strip is independent of ordinate.
The exact second-translation recurrence then bounds every depth moment
with a cost exponential only in physical support and Hecke displacement.
-/

open Complex Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open ArithmeticPolarization

/-- Fixed-strip cutoff differentiation uses only the holomorphic value and first derivative. -/
theorem abs_laplacian_stripCutoff_normSq_le (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (n : ℕ) (z : ℂ) {B : ℝ} (hb : ‖g z‖ ≤ B) (hdb : ‖deriv g z‖ ≤ B) :
    |Δ (fun w => stripSourceCutoff n w * Complex.normSq (g w)) z| ≤
      4 * stripSourceCutoffControl * B ^ 2 := by
  let φ : ℂ → ℝ := fun w => Complex.normSq (g w)
  have hp : ContDiff ℝ 2 φ := by
    have he : φ = fun w => (g w).re ^ 2 + (g w).im ^ 2 := by
      funext w
      simp only [φ, Complex.normSq_apply]
      ring
    rw [he]
    exact ((Complex.reCLM.contDiff.comp (hg.contDiff.restrict_scalars ℝ)).pow 2).add
      ((Complex.imCLM.contDiff.comp (hg.contDiff.restrict_scalars ℝ)).pow 2)
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  have hv : |φ z| ≤ B ^ 2 := by
    dsimp only [φ]
    rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    gcongr
  have hΔ : |Δ φ z| ≤ 4 * B ^ 2 := by
    dsimp only [φ]
    rw [laplacian_normSq_holomorphic g hg,
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Complex.normSq_nonneg _)),
      Complex.normSq_eq_norm_sq]
    gcongr
  have hd (v : ℂ) (hn : ‖v‖ = 1) : |fderiv ℝ φ z v| ≤ 2 * B ^ 2 := by
    have h := abs_fderiv_normSq_holomorphic_le g hg z v
    rw [hn, mul_one] at h
    calc
      |fderiv ℝ φ z v| ≤ 2 * ‖g z‖ * ‖deriv g z‖ := h
      _ ≤ 2 * B * B := by gcongr
      _ = _ := by ring
  have ha : |stripSourceCutoff n z * Δ φ z| ≤ 4 * B ^ 2 := by
    rw [abs_mul, abs_of_nonneg (stripSourceCutoff_nonneg n z)]
    exact (mul_le_mul (stripSourceCutoff_le_one n z) hΔ (abs_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  have hb' : |φ z * Δ (stripSourceCutoff n) z| ≤
      B ^ 2 * (‖stripBumpSecond 1‖ + ‖stripBumpSecond Complex.I‖) := by
    rw [abs_mul]
    exact mul_le_mul hv (abs_stripSourceCutoff_laplacian_le n z) (abs_nonneg _) (sq_nonneg B)
  have hc (v : ℂ) (hn : ‖v‖ = 1) {D : ℝ}
      (hD : |fderiv ℝ (stripSourceCutoff n) z v| ≤ D) :
      |2 * fderiv ℝ (stripSourceCutoff n) z v * fderiv ℝ φ z v| ≤ 4 * B ^ 2 * D := by
    have hD0 := (abs_nonneg _).trans hD
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      2 * |fderiv ℝ (stripSourceCutoff n) z v| * |fderiv ℝ φ z v| ≤
          (2 * D) * (2 * B ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) (hd v hn)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hc1 := hc 1 norm_one (abs_stripSourceCutoff_deriv_one_le n z)
  have hcI := hc Complex.I Complex.norm_I (abs_stripSourceCutoff_deriv_I_le n z)
  rw [source_laplacian_mul _ φ (contDiff_stripSourceCutoff n) hp]
  have ht1 := abs_add_le (stripSourceCutoff n z * Δ φ z) (φ z * Δ (stripSourceCutoff n) z)
  have ht2 := abs_add_le (stripSourceCutoff n z * Δ φ z + φ z * Δ (stripSourceCutoff n) z)
    (2 * fderiv ℝ (stripSourceCutoff n) z 1 * fderiv ℝ φ z 1)
  have ht3 := abs_add_le
    (stripSourceCutoff n z * Δ φ z + φ z * Δ (stripSourceCutoff n) z +
      2 * fderiv ℝ (stripSourceCutoff n) z 1 * fderiv ℝ φ z 1)
    (2 * fderiv ℝ (stripSourceCutoff n) z Complex.I * fderiv ℝ φ z Complex.I)
  have hnon := mul_nonneg (sq_nonneg B)
    (add_nonneg (norm_nonneg (stripBumpSecond 1)) (norm_nonneg (stripBumpSecond Complex.I)))
  unfold stripSourceCutoffControl
  nlinarith only [ha, hb', hc1, hcI, ht1, ht2, ht3, hnon]

/-- The fixed-strip differential envelope records the source norm explicitly. -/
def stripSourceSquareEnvelope (f : CompactTest) (a d : ℝ) : ℝ :=
  4 * stripSourceCutoffControl * sourceTestSize f ^ 2 * Real.exp (6 * (a + d))

lemma stripSourceSquareEnvelope_nonneg (f : CompactTest) (a d : ℝ) :
    0 ≤ stripSourceSquareEnvelope f a d := by
  have hM : 0 ≤ stripSourceCutoffControl := le_trans zero_le_one one_le_stripSourceCutoffControl
  unfold stripSourceSquareEnvelope
  positivity

lemma stripSourceSquareEnvelope_mono (f : CompactTest) (a : ℝ) {d e : ℝ} (h : d ≤ e) :
    stripSourceSquareEnvelope f a d ≤ stripSourceSquareEnvelope f a e := by
  have hM : 0 ≤ stripSourceCutoffControl := le_trans zero_le_one one_le_stripSourceCutoffControl
  unfold stripSourceSquareEnvelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  linarith only [h]

/-- Ordinate motion has no differential cost on the fixed-strip support. -/
theorem abs_laplacian_stripCutoff_moved_square_le (f : CompactTest) {a : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a)
    (u τ : ℝ) (n : ℕ) {z : ℂ} (hz : |z.re - 1 / 2| ≤ 2) :
    |Δ (fun w => stripSourceCutoff n w *
      Complex.normSq (tr (sourceTranslate u (sourceTwist τ f)).1 w)) z| ≤
        stripSourceSquareEnvelope f a |u| := by
  have hb := shiftedSourceTransform_strip_bound f ha hsupp u τ hz
  rw [tr_sourceTranslate_sourceTwist]
  calc
    |Δ (fun w => stripSourceCutoff n w * Complex.normSq (shiftedSourceTransform f u τ w)) z| ≤
        4 * stripSourceCutoffControl *
          (sourceTestSize f * Real.exp ((2 + 1) * (a + |u|))) ^ 2 :=
      abs_laplacian_stripCutoff_normSq_le _ (differentiable_shiftedSourceTransform f u τ)
        n z hb.1 hb.2
    _ = stripSourceSquareEnvelope f a |u| := by
      have he : Real.exp ((2 + 1) * (a + |u|)) ^ 2 =
          Real.exp (6 * (a + |u|)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      unfold stripSourceSquareEnvelope
      rw [mul_pow, he]
      ring

/-- Cutoff differentiation preserves the exact depth-moment translation recurrence. -/
theorem laplacian_stripCutoff_sourceDepthKernel_succ (f : CompactTest) (L : ℝ) (j n : ℕ) (z : ℂ) :
    Δ (fun w => stripSourceCutoff n w * sourceDepthKernel f L (j + 1) w) z =
      Δ (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTranslate L f) L j w) z +
      Δ (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTranslate (-L) f) L j w) z -
        2 * Δ (fun w => stripSourceCutoff n w * sourceDepthKernel f L j w) z := by
  have hp := (contDiff_stripSourceCutoff n).mul (contDiff_sourceDepthKernel (sourceTranslate L f) L j)
  have hm := (contDiff_stripSourceCutoff n).mul (contDiff_sourceDepthKernel (sourceTranslate (-L) f) L j)
  have h0 := (contDiff_stripSourceCutoff n).mul (contDiff_sourceDepthKernel f L j)
  have hpm : ContDiff ℝ 2
      ((fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTranslate L f) L j w) +
        (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTranslate (-L) f) L j w)) :=
    hp.add hm
  have h2 : ContDiff ℝ 2 ((2 : ℝ) • (fun w => stripSourceCutoff n w * sourceDepthKernel f L j w)) :=
    contDiff_const.mul h0
  have he : (fun w => stripSourceCutoff n w * sourceDepthKernel f L (j + 1) w) =
      ((fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTranslate L f) L j w) +
        (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTranslate (-L) f) L j w)) -
        (2 : ℝ) • (fun w => stripSourceCutoff n w * sourceDepthKernel f L j w) := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← sourceDepthKernel_second_difference]
    ring
  rw [he, hpm.contDiffAt.laplacian_sub h2.contDiffAt,
    hp.contDiffAt.laplacian_add hm.contDiffAt,
    InnerProductSpace.laplacian_smul (2 : ℝ) h0.contDiffAt]
  rfl

/-- All finite depth moments have one differential envelope, uniform in ordinate and translation. -/
theorem abs_laplacian_stripCutoff_moving_moment_le (f : CompactTest) {a : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a)
    (L : ℝ) (j n : ℕ) (u τ : ℝ) {z : ℂ} (hz : |z.re - 1 / 2| ≤ 2) :
    |Δ (fun w => stripSourceCutoff n w *
      sourceDepthKernel (sourceTranslate u (sourceTwist τ f)) L j w) z| ≤
        4 ^ j * stripSourceSquareEnvelope f a (|u| + (j : ℝ) * |L|) := by
  induction j generalizing u with
  | zero =>
      simpa only [sourceDepthKernel, pow_zero, mul_one, Nat.cast_zero, zero_mul,
        add_zero, one_mul] using abs_laplacian_stripCutoff_moved_square_le f ha hsupp u τ n hz
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
        (stripSourceSquareEnvelope_mono f a hplus) (by positivity : 0 ≤ (4 : ℝ) ^ j))
      have hm := (ih (u + -L)).trans (mul_le_mul_of_nonneg_left
        (stripSourceSquareEnvelope_mono f a hminus) (by positivity : 0 ≤ (4 : ℝ) ^ j))
      have h0 := (ih u).trans (mul_le_mul_of_nonneg_left
        (stripSourceSquareEnvelope_mono f a hself) (by positivity : 0 ≤ (4 : ℝ) ^ j))
      have he := laplacian_stripCutoff_sourceDepthKernel_succ
        (sourceTranslate u (sourceTwist τ f)) L j n z
      rw [sourceTranslate_add, sourceTranslate_add] at he
      rw [he, pow_succ]
      have ha := abs_add_le
        (Δ (fun w => stripSourceCutoff n w *
          sourceDepthKernel (sourceTranslate (u + L) (sourceTwist τ f)) L j w) z)
        (Δ (fun w => stripSourceCutoff n w *
          sourceDepthKernel (sourceTranslate (u + -L) (sourceTwist τ f)) L j w) z)
      have hs := abs_sub
        (Δ (fun w => stripSourceCutoff n w *
          sourceDepthKernel (sourceTranslate (u + L) (sourceTwist τ f)) L j w) z +
          Δ (fun w => stripSourceCutoff n w *
            sourceDepthKernel (sourceTranslate (u + -L) (sourceTwist τ f)) L j w) z)
        (2 * Δ (fun w => stripSourceCutoff n w *
          sourceDepthKernel (sourceTranslate u (sourceTwist τ f)) L j w) z)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
      nlinarith only [hp, hm, h0, ha, hs]


/-- A logarithmic physical and Hecke aperture has polynomial differential cost. -/
theorem abs_laplacian_stripCutoff_aperture_moment_le (f : CompactTest) {a : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a)
    (L τ : ℝ) (j n : ℕ)
    (hwindow : a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1))
    {z : ℂ} (hz : |z.re - 1 / 2| ≤ 2) :
    |Δ (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTwist τ f) L j w) z| ≤
      4 ^ (j + 1) * stripSourceCutoffControl * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12 := by
  have h := abs_laplacian_stripCutoff_moving_moment_le f ha hsupp L j n 0 τ hz
  simp only [sourceTranslate_zero, abs_zero, zero_add] at h
  have he : Real.exp (6 * (a + (j : ℝ) * |L|)) ≤ ((n : ℝ) + 1) ^ 12 := by
    calc
      Real.exp (6 * (a + (j : ℝ) * |L|)) ≤ Real.exp (12 * Real.log ((n : ℝ) + 1)) :=
        Real.exp_le_exp.mpr (by linarith only [hwindow])
      _ = _ := by
        have hex := Real.exp_nat_mul (Real.log ((n : ℝ) + 1)) 12
        norm_num only [Nat.cast_ofNat] at hex
        rw [hex, Real.exp_log (by positivity)]
  have hM : 0 ≤ stripSourceCutoffControl := le_trans zero_le_one one_le_stripSourceCutoffControl
  refine h.trans ?_
  unfold stripSourceSquareEnvelope
  calc
    (4 : ℝ) ^ j * (4 * stripSourceCutoffControl * sourceTestSize f ^ 2 *
        Real.exp (6 * (a + (j : ℝ) * |L|))) ≤
      (4 : ℝ) ^ j * (4 * stripSourceCutoffControl * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12) := by
      gcongr
    _ = _ := by rw [pow_succ]; ring


/-- The polynomial differential estimate is global because the cutoff owns the support. -/
theorem abs_laplacian_stripCutoff_aperture_moment_le_global (f : CompactTest) {a : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a)
    (L τ : ℝ) (j n : ℕ)
    (hwindow : a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) (z : ℂ) :
    |Δ (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTwist τ f) L j w) z| ≤
      4 ^ (j + 1) * stripSourceCutoffControl * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12 := by
  by_cases hz : z ∈ tsupport (stripSourceCutoff n)
  · exact abs_laplacian_stripCutoff_aperture_moment_le f ha hsupp L τ j n hwindow
      (stripSourceCutoff_support_re n hz)
  · rw [stripSourceCutoff_laplacian_eq_zero_off_support n _
      (contDiff_sourceDepthKernel (sourceTwist τ f) L j) hz, abs_zero]
    have hM : 0 ≤ stripSourceCutoffControl := le_trans zero_le_one one_le_stripSourceCutoffControl
    positivity

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.abs_laplacian_stripCutoff_aperture_moment_le

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.abs_laplacian_stripCutoff_aperture_moment_le_global
