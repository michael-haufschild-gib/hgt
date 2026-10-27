import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceSquareCalculus

/-!
# A fixed-strip source exhaustion

One fixed smooth bump is stretched only in the ordinate direction. Its
support stays in a bounded real-part strip, contains the radial cutoff on
the actual zero strip, and has derivative bounds independent of the stage.
-/

open Complex Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- Vertical contraction used by the fixed-strip exhaustion. -/
def stripSourceScale (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1))

lemma stripSourceScale_pos (n : ℕ) : 0 < stripSourceScale n := by
  unfold stripSourceScale
  positivity

lemma stripSourceScale_le_one (n : ℕ) : stripSourceScale n ≤ 1 := by
  unfold stripSourceScale
  apply (div_le_iff₀ (by positivity)).2
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith only [hn]

/-- Real-linear contraction preserving the horizontal spectral coordinate. -/
def stripSourceCompression (n : ℕ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM +
    stripSourceScale n • (Complex.I • (Complex.ofRealCLM.comp Complex.imCLM))

lemma stripSourceCompression_apply (n : ℕ) (z : ℂ) :
    stripSourceCompression n z = (z.re : ℂ) +
      ((stripSourceScale n * z.im : ℝ) : ℂ) * Complex.I := by
  simp only [stripSourceCompression, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  ring

lemma stripSourceCompression_one (n : ℕ) : stripSourceCompression n 1 = 1 := by
  simp only [stripSourceCompression_apply, Complex.one_re, Complex.one_im,
    mul_zero, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one]

lemma stripSourceCompression_I (n : ℕ) :
    stripSourceCompression n Complex.I = stripSourceScale n • Complex.I := by
  simp only [stripSourceCompression_apply, Complex.I_re, Complex.I_im,
    mul_one, Complex.ofReal_zero, zero_add, Complex.real_smul]

/-- Anisotropic source coordinate centred on the critical line. -/
def stripSourcePoint (n : ℕ) (z : ℂ) : ℂ := stripSourceCompression n z - 1 / 2

lemma stripSourcePoint_re (n : ℕ) (z : ℂ) :
    (stripSourcePoint n z).re = z.re - 1 / 2 := by
  simp [stripSourcePoint, stripSourceCompression_apply]

lemma stripSourcePoint_im (n : ℕ) (z : ℂ) :
    (stripSourcePoint n z).im = z.im / (4 * ((n : ℝ) + 1)) := by
  have hhalf : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [stripSourcePoint, Complex.sub_im, hhalf, sub_zero,
    stripSourceCompression_apply]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
    add_zero, zero_add]
  unfold stripSourceScale
  ring

lemma contDiff_stripSourcePoint (n : ℕ) : ContDiff ℝ 2 (stripSourcePoint n) :=
  (stripSourceCompression n).contDiff.sub contDiff_const

/-- A compact cutoff with fixed horizontal support and linearly growing height. -/
def stripSourceCutoff (n : ℕ) (z : ℂ) : ℝ := sourceCutoff 0 (stripSourcePoint n z)

lemma contDiff_stripSourceCutoff (n : ℕ) : ContDiff ℝ 2 (stripSourceCutoff n) :=
  (sourceCutoff 0).contDiff.comp (contDiff_stripSourcePoint n)

lemma stripSourceCutoff_nonneg (n : ℕ) (z : ℂ) : 0 ≤ stripSourceCutoff n z :=
  (sourceCutoff 0).nonneg

lemma stripSourceCutoff_le_one (n : ℕ) (z : ℂ) : stripSourceCutoff n z ≤ 1 :=
  (sourceCutoff 0).le_one

private lemma norm_le_abs_coordinates (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  calc
    ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ :=
      congrArg norm (Complex.re_add_im z).symm
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = _ := by simp

/-- Every point of the cutoff support lies in the fixed compressed disc. -/
lemma norm_stripSourcePoint_le_of_mem_tsupport (n : ℕ) {z : ℂ}
    (hz : z ∈ tsupport (stripSourceCutoff n)) : ‖stripSourcePoint n z‖ ≤ 2 := by
  have hs : tsupport (stripSourceCutoff n) ⊆ {w | ‖stripSourcePoint n w‖ ≤ 2} := by
    apply closure_minimal
    · intro w hw
      have hne : sourceCutoff 0 (stripSourcePoint n w) ≠ 0 := hw
      have h := subset_tsupport _ hne
      rw [(sourceCutoff 0).tsupport_eq, mem_closedBall, dist_zero_right] at h
      change ‖stripSourcePoint n w‖ ≤ 2
      simpa only [sourceCutoff, Nat.cast_zero, zero_add] using h
    · exact isClosed_le (contDiff_stripSourcePoint n).continuous.norm continuous_const
  exact hs hz

/-- Horizontal width is independent of the exhaustion stage. -/
lemma stripSourceCutoff_support_re (n : ℕ) {z : ℂ}
    (hz : z ∈ tsupport (stripSourceCutoff n)) : |z.re - 1 / 2| ≤ 2 := by
  have h := (Complex.abs_re_le_norm (stripSourcePoint n z)).trans
    (norm_stripSourcePoint_le_of_mem_tsupport n hz)
  simpa only [stripSourcePoint_re] using h

/-- The entire stretched support lies in one linearly growing source disc. -/
lemma stripSourceCutoff_support_norm (n : ℕ) {z : ℂ}
    (hz : z ∈ tsupport (stripSourceCutoff n)) : ‖z‖ ≤ 11 * ((n : ℝ) + 1) := by
  have hδ := stripSourceCutoff_support_re n hz
  have him := (Complex.abs_im_le_norm (stripSourcePoint n z)).trans
    (norm_stripSourcePoint_le_of_mem_tsupport n hz)
  rw [stripSourcePoint_im, abs_div, abs_of_pos (by positivity : 0 < 4 * ((n : ℝ) + 1))] at him
  have him' := (div_le_iff₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp him
  have hre := abs_add_le (z.re - 1 / 2) (1 / 2 : ℝ)
  rw [sub_add_cancel, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hre
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith only [norm_le_abs_coordinates z, hδ, him', hre, hn]

lemma hasCompactSupport_stripSourceCutoff (n : ℕ) : HasCompactSupport (stripSourceCutoff n) := by
  apply (isCompact_closedBall (0 : ℂ) (11 * ((n : ℝ) + 1))).of_isClosed_subset
    (isClosed_tsupport _)
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  exact stripSourceCutoff_support_norm n hz

/-- The new exhaustion contains the old radial support on the actual zero strip. -/
lemma stripSourceCutoff_eq_one_of_strip_im_le (n : ℕ) {z : ℂ}
    (hz : 0 ≤ z.re ∧ z.re ≤ 1) (hy : |z.im| ≤ (n : ℝ) + 2) :
    stripSourceCutoff n z = 1 := by
  have hδ : |z.re - 1 / 2| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  have him : |z.im| / (4 * ((n : ℝ) + 1)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith only [hy, hn]
  apply (sourceCutoff 0).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right]
  simp only [sourceCutoff, Nat.cast_zero, zero_add]
  have h := norm_le_abs_coordinates (stripSourcePoint n z)
  rw [stripSourcePoint_re, stripSourcePoint_im, abs_div,
    abs_of_pos (by positivity : 0 < 4 * ((n : ℝ) + 1))] at h
  linarith only [h, hδ, him]

private lemma fderiv_affine_pullback (f : ℂ → ℝ) (hf : Differentiable ℝ f)
    (A : ℂ →L[ℝ] ℂ) (b z v : ℂ) :
    fderiv ℝ (fun w => f (A w - b)) z v = fderiv ℝ f (A z - b) (A v) := by
  have h := (hf (A z - b)).hasFDerivAt.comp z (A.hasFDerivAt.sub_const b)
  simpa only [ContinuousLinearMap.comp_apply, Function.comp_def] using
    congrArg (fun D => D v) h.fderiv

private lemma dderiv_affine_pullback (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (A : ℂ →L[ℝ] ℂ) (b v z : ℂ) :
    Bottcher.dderiv (fun w => f (A w - b)) v z = Bottcher.dderiv f (A v) (A z - b) := by
  have he : (fun w => fderiv ℝ (fun y => f (A y - b)) w v) =
      fun w => fderiv ℝ f (A w - b) (A v) :=
    funext fun w => fderiv_affine_pullback f (hf.differentiable (by norm_num)) A b w v
  have hg : Differentiable ℝ (fun w => fderiv ℝ f w (A v)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  rw [Bottcher.dderiv, he]
  exact fderiv_affine_pullback _ hg A b z v

private lemma dderiv_real_smul (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (r : ℝ) (v z : ℂ) :
    Bottcher.dderiv f (r • v) z = r ^ 2 * Bottcher.dderiv f v z := by
  have he : (fun w => fderiv ℝ f w (r • v)) = r • (fun w => fderiv ℝ f w v) := by
    funext w
    exact map_smul (fderiv ℝ f w) r v
  have hg : Differentiable ℝ (fun w => fderiv ℝ f w v) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  have hd := (hg z).hasFDerivAt.const_smul r
  unfold Bottcher.dderiv
  rw [he, hd.fderiv]
  simp only [smul_apply, map_smul, smul_eq_mul]
  ring

/-- Fixed second directional derivative of the bump, with its actual supremum norm. -/
def stripBumpSecond (v : ℂ) : BoundedContinuousFunction ℂ ℝ := by
  have hb : ContDiff ℝ 2 (sourceCutoff 0 : ℂ → ℝ) := (sourceCutoff 0).contDiff
  have hd : ContDiff ℝ 1 (fun z => fderiv ℝ (sourceCutoff 0) z v) :=
    (hb.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact ofCompactSupport (Bottcher.dderiv (sourceCutoff 0) v)
    ((hd.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (((sourceCutoff 0).hasCompactSupport.fderiv_apply ℝ v).fderiv_apply ℝ v)

lemma abs_stripBumpSecond_le (v z : ℂ) :
    |Bottcher.dderiv (sourceCutoff 0) v z| ≤ ‖stripBumpSecond v‖ := by
  have h := (stripBumpSecond v).norm_coe_le_norm z
  change ‖Bottcher.dderiv (sourceCutoff 0) v z‖ ≤ _ at h
  simpa only [Real.norm_eq_abs] using h

/-- A single fixed constant pays every cutoff product Laplacian. -/
def stripSourceCutoffControl : ℝ :=
  1 + ‖sourceCutoffDerivative 0 1‖ + ‖sourceCutoffDerivative 0 Complex.I‖ +
    ‖stripBumpSecond 1‖ + ‖stripBumpSecond Complex.I‖

lemma one_le_stripSourceCutoffControl : 1 ≤ stripSourceCutoffControl := by
  unfold stripSourceCutoffControl
  linarith only [norm_nonneg (sourceCutoffDerivative 0 1),
    norm_nonneg (sourceCutoffDerivative 0 Complex.I),
    norm_nonneg (stripBumpSecond 1), norm_nonneg (stripBumpSecond Complex.I)]

lemma abs_stripSourceCutoff_deriv_one_le (n : ℕ) (z : ℂ) :
    |fderiv ℝ (stripSourceCutoff n) z 1| ≤ ‖sourceCutoffDerivative 0 1‖ := by
  have hb : ContDiff ℝ 2 (sourceCutoff 0 : ℂ → ℝ) := (sourceCutoff 0).contDiff
  have h := fderiv_affine_pullback (sourceCutoff 0)
    (hb.differentiable (by norm_num))
    (stripSourceCompression n) (1 / 2) z 1
  rw [stripSourceCompression_one] at h
  rw [show fderiv ℝ (stripSourceCutoff n) z 1 =
      fderiv ℝ (sourceCutoff 0) (stripSourcePoint n z) 1 from h]
  exact abs_sourceCutoffDerivative_le 0 1 _

lemma abs_stripSourceCutoff_deriv_I_le (n : ℕ) (z : ℂ) :
    |fderiv ℝ (stripSourceCutoff n) z Complex.I| ≤ ‖sourceCutoffDerivative 0 Complex.I‖ := by
  have hb : ContDiff ℝ 2 (sourceCutoff 0 : ℂ → ℝ) := (sourceCutoff 0).contDiff
  have h := fderiv_affine_pullback (sourceCutoff 0)
    (hb.differentiable (by norm_num))
    (stripSourceCompression n) (1 / 2) z Complex.I
  rw [stripSourceCompression_I, map_smul, smul_eq_mul] at h
  rw [show fderiv ℝ (stripSourceCutoff n) z Complex.I =
      stripSourceScale n * fderiv ℝ (sourceCutoff 0) (stripSourcePoint n z) Complex.I from h,
    abs_mul, abs_of_pos (stripSourceScale_pos n)]
  exact (mul_le_mul_of_nonneg_left (abs_sourceCutoffDerivative_le 0 Complex.I _)
    (stripSourceScale_pos n).le).trans
      (mul_le_of_le_one_left (norm_nonneg _) (stripSourceScale_le_one n))

/-- The vertical second derivative decreases quadratically under stretching. -/
lemma stripSourceCutoff_laplacian (n : ℕ) (z : ℂ) :
    Δ (stripSourceCutoff n) z =
      Bottcher.dderiv (sourceCutoff 0) 1 (stripSourcePoint n z) +
        stripSourceScale n ^ 2 * Bottcher.dderiv (sourceCutoff 0) Complex.I (stripSourcePoint n z) := by
  have hb : ContDiff ℝ 2 (sourceCutoff 0 : ℂ → ℝ) := (sourceCutoff 0).contDiff
  have h1 := dderiv_affine_pullback (sourceCutoff 0) hb (stripSourceCompression n) (1 / 2) 1 z
  have hI := dderiv_affine_pullback (sourceCutoff 0) hb (stripSourceCompression n) (1 / 2) Complex.I z
  rw [stripSourceCompression_one] at h1
  rw [stripSourceCompression_I, dderiv_real_smul _ hb] at hI
  rw [Bottcher.laplacian_eq_dderiv _ (contDiff_stripSourceCutoff n)]
  exact congrArg₂ (· + ·) h1 hI

/-- The cutoff Laplacians have a bound independent of height. -/
lemma abs_stripSourceCutoff_laplacian_le (n : ℕ) (z : ℂ) :
    |Δ (stripSourceCutoff n) z| ≤ ‖stripBumpSecond 1‖ + ‖stripBumpSecond Complex.I‖ := by
  have hr2 : stripSourceScale n ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (stripSourceScale_pos n).le
      (stripSourceScale_le_one n) 2
  rw [stripSourceCutoff_laplacian]
  refine (abs_add_le _ _).trans (add_le_add (abs_stripBumpSecond_le 1 _) ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (abs_stripBumpSecond_le Complex.I _) (sq_nonneg _)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hr2)


/-- Multiplication and Laplacian preserve the fixed-strip cutoff support. -/
lemma stripSourceCutoff_laplacian_eq_zero_off_support (n : ℕ) (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) {z : ℂ} (hz : z ∉ tsupport (stripSourceCutoff n)) :
    Δ (fun w => stripSourceCutoff n w * φ w) z = 0 := by
  have hs : tsupport (Δ (fun w => stripSourceCutoff n w * φ w)) ⊆
      tsupport (stripSourceCutoff n) :=
    (tsupport_test_laplacian_subset ((contDiff_stripSourceCutoff n).mul hp)).trans
      tsupport_mul_subset_left
  by_contra hne
  exact hz (hs (subset_tsupport _ hne))

/-- The cutoff product Laplacian vanishes outside the prescribed source disc. -/
lemma stripSourceCutoff_laplacian_eq_zero_outside (n : ℕ) (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (z : ℂ)
    (hz : z ∉ closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|) :
    Δ (fun w => stripSourceCutoff n w * φ w) z = 0 := by
  apply stripSourceCutoff_laplacian_eq_zero_off_support n φ hp
  intro hs
  apply hz
  rw [mem_closedBall, dist_zero_right, abs_of_pos (by positivity : 0 < 11 * ((n : ℝ) + 1))]
  exact stripSourceCutoff_support_norm n hs

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.hasCompactSupport_stripSourceCutoff
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.stripSourceCutoff_eq_one_of_strip_im_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.abs_stripSourceCutoff_laplacian_le
