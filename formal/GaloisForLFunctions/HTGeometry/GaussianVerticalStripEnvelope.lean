import GaloisForLFunctions.HTGeometry.GaussianHasseTailEnvelope
import GaloisForLFunctions.HTGeometry.GaussianPolynomialPhaseDefect

/-!
# Simultaneous vertical-strip control of complete polynomial Gaussians

A finite Hasse envelope, coordinate energy, and the exact Gaussian phase give
one square-integrable majorant for every vertical displacement in a strip.
The displacement may vary at every real point. The majorant has the same
coefficient-uniform budget as the fixed-displacement L² estimate.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions
open HTGeometry

/-- A pointwise envelope retaining the Hasse tail, Gaussian phase, and scalar growth. -/
def gaussianVerticalStripEnvelope (P : Polynomial ℝ) (R : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (π * (R : ℝ) ^ 2) *
    (gaussianHasseTailEnvelope P R x +
      (2 * π * (R : ℝ)) * ‖mulXCLM (polyGaussSchwartz P) x‖) +
    (Real.exp (π * (R : ℝ) ^ 2) - 1) * ‖polyGaussSchwartz P x‖

/-- The envelope is nonnegative, including zero-width strips. -/
theorem gaussianVerticalStripEnvelope_nonneg (P : Polynomial ℝ) (R : ℝ≥0) (x : ℝ) :
    0 ≤ gaussianVerticalStripEnvelope P R x := by
  have hc : 0 ≤ Real.exp (π * (R : ℝ) ^ 2) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  unfold gaussianVerticalStripEnvelope
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le
    (add_nonneg (gaussianHasseTailEnvelope_nonneg P R x) (by positivity)))
    (mul_nonneg hc (norm_nonneg _))

/-- Exact pointwise splitting of the full complex Gaussian into amplitude and phase. -/
theorem polynomialGaussian_vertical_eq (P : Polynomial ℝ) (x δ : ℝ) :
    P.eval₂ (algebraMap ℝ ℂ) ((x : ℂ) + (δ : ℂ) * Complex.I) *
        Complex.exp (-(π : ℂ) * ((x : ℂ) + (δ : ℂ) * Complex.I) ^ 2) =
      (Real.exp (π * δ ^ 2) : ℂ) * modulationSymbol (-δ) x *
        complexTranslatedPolyGauss P ((δ : ℂ) * Complex.I) x := by
  have hexp :
      (Real.exp (π * δ ^ 2) : ℂ) * modulationSymbol (-δ) x * (gaussReal x : ℂ) =
        Complex.exp (-(π : ℂ) * ((x : ℂ) + (δ : ℂ) * Complex.I) ^ 2) := by
    rw [modulationSymbol, gaussReal, Complex.ofReal_exp, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [complexTranslatedPolyGauss_apply, ← hexp]
  ring

/-- A single envelope dominates the complete error at every point of the vertical strip. -/
theorem norm_polynomialGaussian_vertical_sub_le_envelope (P : Polynomial ℝ)
    (R : ℝ≥0) (x : ℝ) (δ : Set.Icc (-(R : ℝ)) R) :
    ‖P.eval₂ (algebraMap ℝ ℂ) ((x : ℂ) + (δ : ℝ) * Complex.I) *
        Complex.exp (-(π : ℂ) * ((x : ℂ) + (δ : ℝ) * Complex.I) ^ 2) -
      polyGaussSchwartz P x‖ ≤ gaussianVerticalStripEnvelope P R x := by
  let f : ℂ := polyGaussSchwartz P x
  let T : ℂ := complexTranslatedPolyGauss P (((δ : ℝ) : ℂ) * Complex.I) x
  let m : ℂ := modulationSymbol (-(δ : ℝ)) x
  let c : ℝ := Real.exp (π * (δ : ℝ) ^ 2)
  let C : ℝ := Real.exp (π * (R : ℝ) ^ 2)
  have hδ : |(δ : ℝ)| ≤ (R : ℝ) := abs_le.mpr δ.property
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hc1 : 0 ≤ c - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hcC : c ≤ C := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (δ : ℝ)) hδ 2
  have hT : ‖T - f‖ ≤ gaussianHasseTailEnvelope P R x := by
    apply norm_complexTranslatedPolyGauss_sub_le_envelope P R
      ⟨((δ : ℝ) : ℂ) * Complex.I, ?_⟩ x
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one] using hδ
  have hm : ‖m‖ = 1 := norm_modulationSymbol _ _
  have hM : ‖(m - 1) * f‖ ≤ (2 * π * (R : ℝ)) *
      ‖mulXCLM (polyGaussSchwartz P) x‖ := by
    rw [norm_mul, mulXCLM_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := norm_modulationSymbol_sub_one_le (-(δ : ℝ)) x
    rw [abs_neg] at hb
    calc
      _ ≤ (2 * π * |(δ : ℝ)| * |x|) * ‖f‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ (2 * π * (R : ℝ) * |x|) * ‖f‖ := by gcongr
      _ = _ := by dsimp [f]; ring
  rw [polynomialGaussian_vertical_eq]
  change ‖(c : ℂ) * m * T - f‖ ≤ _
  have hid : (c : ℂ) * m * T - f =
      (c : ℂ) * m * (T - f) + (c : ℂ) * ((m - 1) * f) + ((c : ℂ) - 1) * f := by ring
  have hcnorm : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hcnorm' : ‖(c : ℂ) - 1‖ = c - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc1]
  calc
    _ ≤ ‖(c : ℂ) * m * (T - f)‖ + ‖(c : ℂ) * ((m - 1) * f)‖ +
        ‖((c : ℂ) - 1) * f‖ := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = c * ‖T - f‖ + c * ‖(m - 1) * f‖ + (c - 1) * ‖f‖ := by
      simp only [norm_mul, hcnorm, hcnorm', hm, mul_one]
    _ ≤ c * gaussianHasseTailEnvelope P R x +
        c * ((2 * π * (R : ℝ)) * ‖mulXCLM (polyGaussSchwartz P) x‖) +
        (c - 1) * ‖f‖ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hT hc)
        (mul_le_mul_of_nonneg_left hM hc)) le_rfl
    _ ≤ C * gaussianHasseTailEnvelope P R x +
        C * ((2 * π * (R : ℝ)) * ‖mulXCLM (polyGaussSchwartz P) x‖) +
        (C - 1) * ‖f‖ := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hcC (gaussianHasseTailEnvelope_nonneg P R x))
        (mul_le_mul_of_nonneg_right hcC (by positivity)))
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hcC 1) (norm_nonneg _))
    _ = _ := by dsimp [gaussianVerticalStripEnvelope, C, f]; ring

/-- The complete strip envelope is square integrable. -/
theorem memLp_gaussianVerticalStripEnvelope (P : Polynomial ℝ) (R : ℝ≥0) :
    MemLp (gaussianVerticalStripEnvelope P R) 2 (volume : Measure ℝ) := by
  exact ((memLp_gaussianHasseTailEnvelope P R).add
    (((mulXCLM (polyGaussSchwartz P)).memLp 2 volume).norm.const_mul _)).const_mul _ |>.add
    (((polyGaussSchwartz P).memLp 2 volume).norm.const_mul _)

/-- A coefficient-uniform L² budget for the simultaneous vertical-strip envelope. -/
theorem lpNorm_gaussianVerticalStripEnvelope_le (P : Polynomial ℝ) (R : ℝ≥0) :
    lpNorm (gaussianVerticalStripEnvelope P R) 2 (volume : Measure ℝ) ≤
      verticalPolynomialGaussianDefect P.natDegree R *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let C : ℝ := Real.exp (π * (R : ℝ) ^ 2)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hC1 : 0 ≤ C - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  let F : ℝ → ℝ := fun x => ‖polyGaussSchwartz P x‖
  let X : ℝ → ℝ := fun x => ‖mulXCLM (polyGaussSchwartz P) x‖
  have hX : MemLp X 2 (volume : Measure ℝ) :=
    ((mulXCLM (polyGaussSchwartz P)).memLp 2 volume).norm
  have hB := memLp_gaussianHasseTailEnvelope P R
  have hs (b : ℝ≥0) (u : ℝ → ℝ) :
      lpNorm (fun x => (b : ℝ) * u x) 2 (volume : Measure ℝ) =
        (b : ℝ) * lpNorm u 2 (volume : Measure ℝ) := by
    have hh := lpNorm_const_smul (p := (2 : ENNReal)) (b : ℝ) u (volume : Measure ℝ)
    change lpNorm (fun x => (b : ℝ) * u x) 2 (volume : Measure ℝ) =
      ‖(b : ℝ)‖ * lpNorm u 2 (volume : Measure ℝ) at hh
    rw [Real.norm_eq_abs, abs_of_nonneg b.coe_nonneg] at hh
    exact hh
  have hinner := lpNorm_add_le hB (g := fun x => (2 * π * (R : ℝ)) * X x) (by simp)
  have houter := lpNorm_add_le
    ((hB.add (hX.const_mul (2 * π * (R : ℝ)))).const_mul C)
    (g := fun x => (C - 1) * F x) (by simp)
  simp only [Pi.add_def] at hinner houter
  have hsC := hs ⟨C, hC⟩ (fun x => gaussianHasseTailEnvelope P R x + 2 * π * (R : ℝ) * X x)
  have hsC1 := hs ⟨C - 1, hC1⟩ F
  have hsX := hs ⟨2 * π * (R : ℝ), by positivity⟩ X
  change lpNorm (fun x => C * (gaussianHasseTailEnvelope P R x + 2 * π * (R : ℝ) * X x))
    2 (volume : Measure ℝ) = C * lpNorm
      (fun x => gaussianHasseTailEnvelope P R x + 2 * π * (R : ℝ) * X x)
      2 (volume : Measure ℝ) at hsC
  change lpNorm (fun x => (C - 1) * F x) 2 (volume : Measure ℝ) =
    (C - 1) * lpNorm F 2 (volume : Measure ℝ) at hsC1
  change lpNorm (fun x => (2 * π * (R : ℝ)) * X x) 2 (volume : Measure ℝ) =
    (2 * π * (R : ℝ)) * lpNorm X 2 (volume : Measure ℝ) at hsX
  rw [hsC, hsC1] at houter
  rw [hsX] at hinner
  have hFn : lpNorm F 2 (volume : Measure ℝ) =
      ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
    dsimp only [F]
    rw [lpNorm_norm (polyGaussSchwartz P).continuous.aestronglyMeasurable,
      lpNorm_schwartz_eq]
  have hXn : lpNorm X 2 (volume : Measure ℝ) =
      ‖(mulXCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ := by
    dsimp only [X]
    rw [lpNorm_norm (mulXCLM (polyGaussSchwartz P)).continuous.aestronglyMeasurable,
      lpNorm_schwartz_eq]
  rw [hFn] at houter
  rw [hXn] at hinner
  have htail := lpNorm_gaussianHasseTailEnvelope_le P R
  have hcoord := mul_le_mul_of_nonneg_left (gaussianPolynomialCoordinateNorm_le P) R.coe_nonneg
  have hcombined := add_le_add
    (mul_le_mul_of_nonneg_left hinner hC)
    (le_refl ((C - 1) * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖))
  have h := houter.trans hcombined
  change lpNorm (gaussianVerticalStripEnvelope P R) 2 (volume : Measure ℝ) ≤ _ at h
  have hlast := mul_le_mul_of_nonneg_left htail hC
  have hcoord' := mul_le_mul_of_nonneg_left hcoord hC
  unfold verticalPolynomialGaussianDefect
  simp only [abs_of_nonneg R.coe_nonneg]
  change _ ≤ (C * (Real.exp ((R : ℝ) * Real.sqrt (4 * π * P.natDegree)) - 1 +
    (R : ℝ) * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1))) + (C - 1)) * _
  nlinarith only [h, hlast, hcoord']

end GaloisForLFunctions
