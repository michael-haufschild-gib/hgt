import GaloisForLFunctions.HTGeometry.BochnerL2HilbertTensor
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyCauchyTotality
import GaloisForLFunctions.HTGeometry.ContinuousFrameGramBound

/-!
# Signed covariance bounds retaining positive-negative frequency correlations

The density feature `conj(f) ⊗ f` realizes the squared complex Gram kernel in
a genuine Hilbert space. Subtracting two integrated density features therefore
retains the negative cross term in its squared norm. No rank cutoff is used.
-/

open Complex MeasureTheory
open scoped InnerProduct TensorProduct BoundedContinuousFunction
noncomputable section
namespace GaloisForLFunctions.HTGeometry

abbrev L2DensitySpace := Lp RealLineL2 2 (volume : Measure ℝ)

private theorem norm_star_l2 (f : RealLineL2) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [Lp.coeFn_star f] with x hx
  rw [hx, Pi.star_apply, norm_star]

private theorem continuous_star_l2 : Continuous (star : RealLineL2 → RealLineL2) := by
  apply Isometry.continuous
  apply Isometry.of_dist_eq
  intro f g
  rw [dist_eq_norm, dist_eq_norm]
  change ‖RHTower.lpStarₛₗ f - RHTower.lpStarₛₗ g‖ = _
  rw [← map_sub]
  exact norm_star_l2 (f-g)

private theorem norm_bochner_product (f g : RealLineL2) :
    ‖bochnerL2Product f g‖ = ‖f‖ * ‖g‖ := by
  calc
    _ = ‖f ⊗ₜ[ℂ] g‖ := bochnerL2TensorIsometry.norm_map (f ⊗ₜ[ℂ] g)
    _ = _ := TensorProduct.norm_tmul _ _

/-- A rank-one density represented in a complete Hilbert space. -/
def l2DensityFeature (f : RealLineL2) : L2DensitySpace :=
  bochnerL2Product (star f) f

theorem l2DensityFeature_inner (f g : RealLineL2) :
    inner ℂ (l2DensityFeature f) (l2DensityFeature g) =
      ((‖inner ℂ f g‖ ^ 2 : ℝ) : ℂ) := by
  rw [l2DensityFeature, l2DensityFeature, bochnerL2Product_inner,
    inner_star_star_realLineL2, mul_comm, Complex.mul_conj, ← Complex.sq_norm]

theorem norm_l2DensityFeature (f : RealLineL2) :
    ‖l2DensityFeature f‖ = ‖f‖ ^ 2 := by
  rw [l2DensityFeature, norm_bochner_product, norm_star_l2, pow_two]

theorem continuous_l2DensityFeature : Continuous l2DensityFeature := by
  let B : RealLineL2 →L[ℂ] RealLineL2 →L[ℂ] L2DensitySpace :=
    bochnerL2ProductBilinear.mkContinuous₂ 1 (fun f g => by
      change ‖bochnerL2Product f g‖ ≤ _
      rw [norm_bochner_product, one_mul])
  exact (B.continuous.comp continuous_star_l2).clm_apply continuous_id

/-- The density field of a bounded continuous whole-line L² field. -/
def l2DensityFrame (v : ℝ →ᵇ RealLineL2) : ℝ →ᵇ L2DensitySpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => l2DensityFeature (v x))
    (continuous_l2DensityFeature.comp v.continuous) (‖v‖ ^ 2) (fun x => by
      rw [norm_l2DensityFeature]
      exact pow_le_pow_left₀ (norm_nonneg _) (v.norm_coe_le_norm x) 2)

theorem integrable_l2DensityFrame (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ RealLineL2) : Integrable (fun x => l2DensityFeature (v x)) μ :=
  (integrable_const ‖l2DensityFrame v‖).mono'
    (l2DensityFrame v).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (l2DensityFrame v).norm_coe_le_norm)

/-- Integrated density; it retains all off-diagonal frequency correlations. -/
def l2FrameCovariance (μ : Measure ℝ) (v : ℝ →ᵇ RealLineL2) : L2DensitySpace :=
  ∫ x, l2DensityFeature (v x) ∂μ

theorem l2DensityFeature_inner_covariance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ RealLineL2) (f : RealLineL2) :
    inner ℂ (l2DensityFeature f) (l2FrameCovariance μ v) =
      ((∫ x, ‖inner ℂ f (v x)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [l2FrameCovariance, ← integral_inner (integrable_l2DensityFrame μ v)]
  simp_rw [l2DensityFeature_inner]
  exact integral_complex_ofReal

/-- The interaction of two frequency measures, with no absolute-value splitting. -/
def l2FrameCrossGram (μ ν : Measure ℝ) (v : ℝ →ᵇ RealLineL2) : ℝ :=
  ∫ x, ∫ y, ‖inner ℂ (v x) (v y)‖ ^ 2 ∂μ ∂ν

theorem l2FrameCovariance_inner_re (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : ℝ →ᵇ RealLineL2) :
    (inner ℂ (l2FrameCovariance μ v) (l2FrameCovariance ν v)).re =
      l2FrameCrossGram μ ν v := by
  change (inner ℂ (l2FrameCovariance μ v) (∫ x, l2DensityFeature (v x) ∂ν)).re = _
  rw [← integral_inner (integrable_l2DensityFrame ν v)]
  change RCLike.re (∫ x, inner ℂ (l2FrameCovariance μ v)
    (l2DensityFeature (v x)) ∂ν) = _
  rw [← integral_re ((integrable_l2DensityFrame ν v).const_inner
    (𝕜 := ℂ) (l2FrameCovariance μ v))]
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_re_symm (𝕜 := ℂ)]
  change (inner ℂ (l2DensityFeature (v x)) (l2FrameCovariance μ v)).re = _
  rw [l2DensityFeature_inner_covariance, Complex.ofReal_re]

theorem l2FrameCrossGram_nonneg (μ ν : Measure ℝ) (v : ℝ →ᵇ RealLineL2) :
    0 ≤ l2FrameCrossGram μ ν v :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

theorem norm_l2FrameCovariance_sq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ RealLineL2) :
    ‖l2FrameCovariance μ v‖ ^ 2 = _root_.HTGeometry.continuousFrameGramEnergy μ v := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  change (inner ℂ (l2FrameCovariance μ v) (l2FrameCovariance μ v)).re = _
  rw [l2FrameCovariance_inner_re]
  rfl

/-- Positive-frequency subtraction carries the exact negative cross-correlation term. -/
theorem norm_l2FrameCovariance_sub_sq (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : ℝ →ᵇ RealLineL2) (θ : ℝ) :
    ‖l2FrameCovariance μ v - (θ : ℂ) • l2FrameCovariance ν v‖ ^ 2 =
      _root_.HTGeometry.continuousFrameGramEnergy μ v -
        2 * θ * l2FrameCrossGram μ ν v +
        θ ^ 2 * _root_.HTGeometry.continuousFrameGramEnergy ν v := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖l2FrameCovariance μ v‖ ^ 2 -
    2 * (inner ℂ (l2FrameCovariance μ v) ((θ : ℂ) • l2FrameCovariance ν v)).re +
    ‖(θ : ℂ) • l2FrameCovariance ν v‖ ^ 2 = _
  rw [inner_smul_right, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs,
    norm_l2FrameCovariance_sq, norm_l2FrameCovariance_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    l2FrameCovariance_inner_re]
  ring

/-- A source-uniform bound with the two signs still interacting inside one Hilbert norm. -/
theorem abs_l2Frame_difference_le (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : ℝ →ᵇ RealLineL2)
    (θ : ℝ) (f : RealLineL2) :
    |(∫ x, ‖inner ℂ (v x) f‖ ^ 2 ∂μ) - θ * (∫ x, ‖inner ℂ (v x) f‖ ^ 2 ∂ν)| ≤
      ‖l2FrameCovariance μ v - (θ : ℂ) • l2FrameCovariance ν v‖ * ‖f‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (l2DensityFeature f)
    (l2FrameCovariance μ v - (θ : ℂ) • l2FrameCovariance ν v)
  rw [inner_sub_right, inner_smul_right, l2DensityFeature_inner_covariance,
    l2DensityFeature_inner_covariance, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, norm_l2DensityFeature] at h
  simpa only [norm_inner_symm, mul_comm] using h

end GaloisForLFunctions.HTGeometry
