import GaloisForLFunctions.RHTower.VectorL2FourierIntegralBridge

/-!
# Vector-valued Plancherel for the classical Fourier integral

Mathlib's Plancherel theorem is an isometry of `L²` *classes*; what a block estimate needs is the
pointwise identity for a Hilbert-valued function that is both integrable and square integrable,

`∫ ‖𝓕 f(ξ)‖² dξ = ∫ ‖f(x)‖² dx`,

together with the change of normalization to the angular convention `z ↦ ∫ e^{-izx}f(x)dx` used by
the card.  Since that transform is mathlib's at frequency `z/2π`, the scaling of the frequency
variable contributes exactly the factor `2π`:

`∫ ‖f̂(z)‖² dz = 2π ∫ ‖f(x)‖² dx`.

This is the card's `(12)`, and it is the only place the convention constant appears.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory FourierTransform

open _root_.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The squared `L²` norm as an integral of squared norms, for a Hilbert-valued class. -/
theorem lp_norm_sq_eq_integral_vector (f : Lp H 2 (volume : Measure ℝ)) :
    ‖f‖ ^ (2 : ℕ) = ∫ x : ℝ, ‖(f : ℝ → H) x‖ ^ (2 : ℕ) := by
  have h1 : (inner ℂ f f : ℂ) = ∫ x : ℝ, (inner ℂ ((f : ℝ → H) x) ((f : ℝ → H) x) : ℂ) :=
    L2.inner_def f f
  have h2 : ∀ z : H, (inner ℂ z z : ℂ) = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro z
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h3 : (inner ℂ f f : ℂ) = ((‖f‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h3] at h1
  simp only [h2] at h1
  rw [integral_complex_ofReal] at h1
  exact Complex.ofReal_inj.mp h1

/-- For an integrable square-integrable Hilbert-valued function, the `L²` Fourier transform of its
class is the classical Fourier integral. -/
theorem coeFn_fourier_toLp_vector {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((𝓕 (hf2.toLp f) : Lp H 2 (volume : Measure ℝ)) : ℝ → H) =ᵐ[volume] 𝓕 f := by
  have hcoe : ((hf2.toLp f : Lp H 2 (volume : Measure ℝ)) : ℝ → H) =ᵐ[volume] f := hf2.coeFn_toLp
  have hint : Integrable ((hf2.toLp f : Lp H 2 (volume : Measure ℝ)) : ℝ → H) :=
    hf1.congr hcoe.symm
  have hbridge := _root_.RHTower.l2_vector_fourier_coeFn_eq_l1_fourier_of_integrable
    (hf2.toLp f) hint
  refine hbridge.trans (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.Lp.fourierTransform_apply]
  refine Real.fourier_congr_ae ?_ ξ
  exact ((memLp_one_iff_integrable.mpr hint).coeFn_toLp).trans hcoe

/-- **Plancherel for the classical Hilbert-valued Fourier integral.** -/
theorem integral_norm_sq_fourier_eq_vector {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    (∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ (2 : ℕ)) = ∫ x : ℝ, ‖f x‖ ^ (2 : ℕ) := by
  have hlhs : (∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ (2 : ℕ))
      = ‖(𝓕 (hf2.toLp f) : Lp H 2 (volume : Measure ℝ))‖ ^ (2 : ℕ) := by
    rw [lp_norm_sq_eq_integral_vector]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fourier_toLp_vector hf1 hf2] with ξ hξ
    rw [hξ]
  have hrhs : (∫ x : ℝ, ‖f x‖ ^ (2 : ℕ)) = ‖(hf2.toLp f : Lp H 2 (volume : Measure ℝ))‖ ^ (2 : ℕ) := by
    rw [lp_norm_sq_eq_integral_vector]
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  rw [hlhs, hrhs, Lp.norm_fourier_eq]

/-- The spectral density of an integrable square-integrable Hilbert-valued function is
integrable. -/
theorem integrable_norm_sq_fourier_vector {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    Integrable (fun ξ : ℝ => ‖𝓕 f ξ‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
  have hmem := Lp.memLp (𝓕 (hf2.toLp f) : Lp H 2 (volume : Measure ℝ))
  have hsq : Integrable (fun ξ : ℝ =>
      ‖((𝓕 (hf2.toLp f) : Lp H 2 (volume : Measure ℝ)) : ℝ → H) ξ‖ ^ (2 : ℕ))
      (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hsq.congr ?_
  filter_upwards [coeFn_fourier_toLp_vector hf1 hf2] with ξ hξ
  rw [hξ]

/-! ## The angular-frequency convention -/

/-- The angular-frequency Fourier transform `z ↦ ∫ e^{-izx}f(x)dx` of the card. -/
def vectorAngularTransform (f : ℝ → H) (z : ℝ) : H :=
  ∫ x : ℝ, Complex.exp (-(Complex.I) * (z : ℂ) * (x : ℂ)) • f x

theorem integral_comp_div_two_pi (G : ℝ → ℝ) :
    (∫ z : ℝ, G (z / (2 * Real.pi))) = (2 * Real.pi) * ∫ w : ℝ, G w := by
  have hscale := Measure.integral_comp_mul_left G (1 / (2 * Real.pi))
  rw [show (fun z : ℝ => G (1 / (2 * Real.pi) * z)) = fun z => G (z / (2 * Real.pi)) by
    funext z
    congr 1
    ring] at hscale
  rw [show (1 / (2 * Real.pi) : ℝ)⁻¹ = 2 * Real.pi by
    field_simp] at hscale
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hscale
  simpa [smul_eq_mul] using hscale

omit [CompleteSpace H] in
/-- **The angular transform is mathlib's transform at frequency `z/2π`.** -/
theorem vectorAngularTransform_eq_fourier (f : ℝ → H) (z : ℝ) :
    vectorAngularTransform f z = 𝓕 f (z / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, vectorAngularTransform]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have he : -(Complex.I) * (z : ℂ) * (x : ℂ)
      = ((-2 * Real.pi * x * (z / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  show Complex.exp (-(Complex.I) * (z : ℂ) * (x : ℂ)) • f x
      = Complex.exp (((-2 * Real.pi * x * (z / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) • f x
  rw [he]

/-- **`(12)`: the angular Parseval identity.**  The transform of a physical profile has `L²` energy
`2π` times the physical energy — the only place the convention constant enters. -/
theorem integral_norm_sq_vectorAngularTransform_eq {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    (∫ z : ℝ, ‖vectorAngularTransform f z‖ ^ (2 : ℕ)) = (2 * Real.pi) * ∫ x : ℝ, ‖f x‖ ^ (2 : ℕ) := by
  have h1 : (fun z : ℝ => ‖vectorAngularTransform f z‖ ^ (2 : ℕ))
      = fun z : ℝ => ‖𝓕 f (z / (2 * Real.pi))‖ ^ (2 : ℕ) := by
    funext z
    rw [vectorAngularTransform_eq_fourier]
  have h2 := integral_comp_div_two_pi (fun w : ℝ => ‖𝓕 f w‖ ^ (2 : ℕ))
  rw [h1, h2, integral_norm_sq_fourier_eq_vector hf1 hf2]

/-- The angular spectral density of an integrable square-integrable profile is integrable. -/
theorem integrable_norm_sq_vectorAngularTransform {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    Integrable (fun z : ℝ => ‖vectorAngularTransform f z‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
  have hbase : Integrable (fun w : ℝ => ‖𝓕 f w‖ ^ (2 : ℕ)) (volume : Measure ℝ) :=
    integrable_norm_sq_fourier_vector hf1 hf2
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hscaled := hbase.comp_div hpi
  refine hscaled.congr ?_
  filter_upwards with z
  rw [vectorAngularTransform_eq_fourier]

end GaloisForLFunctions.RHTower

end
