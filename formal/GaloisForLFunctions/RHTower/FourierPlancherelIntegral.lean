import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

/-!
# Plancherel for the classical Fourier integral

Mathlib's Plancherel theorem is an isometry statement about `L²` *classes*.  What analysis needs is the
pointwise version: for a function that is both integrable and square integrable, the classical Fourier
integral has the same energy as the function,

```text
∫ ‖𝓕 f (xi)‖² d xi = ∫ ‖f x‖² dx,
```

and its squared modulus is integrable.  The bridge from the class-level transform to the classical
integral is the corpus's `l2_fourier_coeFn_eq_l1_fourier_of_integrable`; the rest is bookkeeping between
`Lp` norms and integrals of squared norms.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory FourierTransform

open _root_.RHTower

/-- The squared `L²` norm as an integral of squared norms. -/
theorem lp_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ (2 : ℕ) = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ) := by
  have h1 : (inner ℂ f f : ℂ) = ∫ x : ℝ, (inner ℂ ((f : ℝ → ℂ) x) ((f : ℝ → ℂ) x) : ℂ) :=
    L2.inner_def f f
  have h2 : ∀ z : ℂ, (inner ℂ z z : ℂ) = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
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

/-- For an integrable square-integrable function, mathlib's `L²` Fourier transform of its class is the
classical Fourier integral. -/
theorem coeFn_fourier_toLp {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hcoe : ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hint : Integrable ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    hf1.congr hcoe.symm
  have hbridge := _root_.RHTower.l2_fourier_coeFn_eq_l1_fourier_of_integrable (hf2.toLp f) hint
  refine hbridge.trans (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.Lp.fourierTransform_apply]
  refine Real.fourier_congr_ae ?_ ξ
  exact ((memLp_one_iff_integrable.mpr hint).coeFn_toLp).trans hcoe

/-- **The Fourier integral of an integrable function is continuous.**  Mathlib's `L¹` Fourier
transform is a bounded continuous function, and it represents the classical integral. -/
theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) := by
  have hmem : MemLp f 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hf
  have hcont : Continuous fun ξ : ℝ => (Real.Lp.fourierTransform (hmem.toLp f)) ξ :=
    (Real.Lp.fourierTransform (hmem.toLp f)).continuous
  refine hcont.congr fun ξ => ?_
  rw [Real.Lp.fourierTransform_apply]
  exact Real.fourier_congr_ae hmem.coeFn_toLp ξ

/-- **Plancherel for the classical Fourier integral.** -/
theorem integral_norm_sq_fourier_eq {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    (∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ (2 : ℕ)) = ∫ x : ℝ, ‖f x‖ ^ (2 : ℕ) := by
  have hlhs : (∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ (2 : ℕ))
      = ‖(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))‖ ^ (2 : ℕ) := by
    rw [lp_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fourier_toLp hf1 hf2] with ξ hξ
    rw [hξ]
  have hrhs : (∫ x : ℝ, ‖f x‖ ^ (2 : ℕ)) = ‖(hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ))‖ ^ (2 : ℕ) := by
    rw [lp_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  rw [hlhs, hrhs, Lp.norm_fourier_eq]

/-- The spectral density of an integrable square-integrable function is integrable. -/
theorem integrable_norm_sq_fourier {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    Integrable (fun ξ : ℝ => ‖𝓕 f ξ‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
  have hmem := Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))
  have hsq : Integrable (fun ξ : ℝ =>
      ‖((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ (2 : ℕ))
      (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hsq.congr ?_
  filter_upwards [coeFn_fourier_toLp hf1 hf2] with ξ hξ
  rw [hξ]

end GaloisForLFunctions.RHTower

end
