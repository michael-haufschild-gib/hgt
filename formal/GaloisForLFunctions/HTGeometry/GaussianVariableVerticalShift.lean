import GaloisForLFunctions.HTGeometry.GaussianVerticalStripEnvelope
import GaloisForLFunctions.HTGeometry.GaussianPolynomialParabolicDefect

/-!
# Relative Gaussian control along varying vertical displacements

The simultaneous strip envelope controls a complete polynomial Gaussian along
every continuous graph in the strip. Its degree-normalized relative error has
a common vanishing modulus, independent of the graph and all coefficients.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory Filter Topology
noncomputable section

namespace GaloisForLFunctions

/-- The entire polynomial Gaussian evaluated along a continuous graph in a vertical strip. -/
def variableVerticalPolynomialGaussian (P : Polynomial ℝ) (R : ℝ≥0)
    (δ : C(ℝ, Set.Icc (-(R : ℝ)) R)) (x : ℝ) : ℂ :=
  P.eval₂ (algebraMap ℝ ℂ) ((x : ℂ) + ((δ x : ℝ) : ℂ) * Complex.I) *
    Complex.exp (-(π : ℂ) * ((x : ℂ) + ((δ x : ℝ) : ℂ) * Complex.I) ^ 2)

/-- Square integrability of the varying-displacement error follows from the strip envelope. -/
theorem memLp_variableVerticalPolynomialGaussian_sub (P : Polynomial ℝ) (R : ℝ≥0)
    (δ : C(ℝ, Set.Icc (-(R : ℝ)) R)) :
    MemLp (fun x => variableVerticalPolynomialGaussian P R δ x - polyGaussSchwartz P x)
      2 (volume : Measure ℝ) := by
  apply (memLp_gaussianVerticalStripEnvelope P R).mono'
  · have hd : Continuous (fun x => (δ x : ℝ)) :=
      continuous_subtype_val.comp δ.continuous
    apply Continuous.aestronglyMeasurable
    unfold variableVerticalPolynomialGaussian
    fun_prop
  · exact Filter.Eventually.of_forall fun x =>
      norm_polynomialGaussian_vertical_sub_le_envelope P R x (δ x)

/-- The complete Gaussian along every such graph is square integrable. -/
theorem memLp_variableVerticalPolynomialGaussian (P : Polynomial ℝ) (R : ℝ≥0)
    (δ : C(ℝ, Set.Icc (-(R : ℝ)) R)) :
    MemLp (variableVerticalPolynomialGaussian P R δ) 2 (volume : Measure ℝ) := by
  have h := (memLp_variableVerticalPolynomialGaussian_sub P R δ).add
    ((polyGaussSchwartz P).memLp 2 (volume : Measure ℝ))
  simpa only [Pi.add_def, sub_add_cancel] using h

/-- Variable displacement has a coefficient-uniform error with no derivative bound on the graph. -/
theorem lpNorm_variableVerticalPolynomialGaussian_sub_le (P : Polynomial ℝ) (R : ℝ≥0)
    (δ : C(ℝ, Set.Icc (-(R : ℝ)) R)) :
    lpNorm (fun x => variableVerticalPolynomialGaussian P R δ x - polyGaussSchwartz P x)
      2 (volume : Measure ℝ) ≤
      verticalPolynomialGaussianDefect P.natDegree R *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  exact (lpNorm_mono_real (memLp_gaussianVerticalStripEnvelope P R)
    (fun x => norm_polynomialGaussian_vertical_sub_le_envelope P R x (δ x))).trans
    (lpNorm_gaussianVerticalStripEnvelope_le P R)

/-- An independent continuous-energy floor for the entire Gaussian along a varying graph. -/
theorem lpNorm_variableVerticalPolynomialGaussian_lower_margin (P : Polynomial ℝ) (R : ℝ≥0)
    (δ : C(ℝ, Set.Icc (-(R : ℝ)) R)) :
    (1 - verticalPolynomialGaussianDefect P.natDegree R) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
      lpNorm (variableVerticalPolynomialGaussian P R δ) 2 (volume : Measure ℝ) := by
  have ht := lpNorm_le_lpNorm_add_lpNorm_sub
    (f := (polyGaussSchwartz P : ℝ → ℂ))
    (memLp_variableVerticalPolynomialGaussian P R δ) (by simp)
  have he := lpNorm_variableVerticalPolynomialGaussian_sub_le P R δ
  rw [lpNorm_schwartz_eq] at ht
  change _ ≤ _ + lpNorm (fun x => variableVerticalPolynomialGaussian P R δ x -
    polyGaussSchwartz P x) 2 (volume : Measure ℝ) at ht
  nlinarith only [ht, he]

/-- The strip radius normalized by the square root of degree plus one. -/
def polynomialGaussianStripRadius (P : Polynomial ℝ) (ε : ℝ≥0) : ℝ≥0 :=
  ⟨(ε : ℝ) / Real.sqrt ((P.natDegree : ℝ) + 1), by positivity⟩

/-- One degree-independent budget controls every varying graph in the normalized strip. -/
theorem lpNorm_variableVerticalPolynomialGaussian_parabolic_sub_le
    (P : Polynomial ℝ) (ε : ℝ≥0)
    (δ : C(ℝ, Set.Icc (-(polynomialGaussianStripRadius P ε : ℝ))
      (polynomialGaussianStripRadius P ε : ℝ))) :
    lpNorm (fun x => variableVerticalPolynomialGaussian P (polynomialGaussianStripRadius P ε) δ x -
      polyGaussSchwartz P x) 2 (volume : Measure ℝ) ≤
      parabolicGaussianDefect ε * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  refine (lpNorm_variableVerticalPolynomialGaussian_sub_le P _ δ).trans ?_
  exact mul_le_mul_of_nonneg_right (verticalPolynomialGaussianDefect_parabolic_le P.natDegree ε)
    (norm_nonneg _)

/-- One rescaled cutoff gives a half-norm floor for every polynomial and every strip graph. -/
theorem eventually_forall_variableVerticalPolynomialGaussian_parabolic_lower :
    ∀ᶠ τ : ℝ in atBot, ∀ (P : Polynomial ℝ)
      (δ : C(ℝ, Set.Icc
        (-(polynomialGaussianStripRadius P ⟨Real.exp τ, (Real.exp_pos _).le⟩ : ℝ))
        (polynomialGaussianStripRadius P ⟨Real.exp τ, (Real.exp_pos _).le⟩ : ℝ))),
      (1 / 2 : ℝ) * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤
        lpNorm (variableVerticalPolynomialGaussian P
          (polynomialGaussianStripRadius P ⟨Real.exp τ, (Real.exp_pos _).le⟩) δ)
          2 (volume : Measure ℝ) := by
  have he := (parabolicGaussianDefect_tendsto_zero.comp Real.tendsto_exp_atBot).eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / 2))
  filter_upwards [he] with τ hτ P δ
  let ε : ℝ≥0 := ⟨Real.exp τ, (Real.exp_pos _).le⟩
  have hfloor := lpNorm_variableVerticalPolynomialGaussian_lower_margin P
    (polynomialGaussianStripRadius P ε) δ
  have hbudget := verticalPolynomialGaussianDefect_parabolic_le P.natDegree (Real.exp τ)
  have hsmall := mul_le_mul_of_nonneg_right (hbudget.trans hτ.le)
    (norm_nonneg ((polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)))
  change verticalPolynomialGaussianDefect P.natDegree (polynomialGaussianStripRadius P ε) *
    ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ≤ _ at hsmall
  nlinarith only [hfloor, hsmall]

end GaloisForLFunctions
