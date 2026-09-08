import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Lattice sums of band-limited Schwartz functions

Poisson summation on the lattice `x + sℤ` reads the Fourier transform of `f` at the multiples of
`1/s`.  If `𝓕 f` vanishes at every frequency of modulus at least `1/s` (the function is band-limited
below the Nyquist frequency of the lattice), every nonzero mode drops out and the lattice sum equals
the continuum integral exactly:

`Σ_{n ∈ ℤ} f (x + n s) = s⁻¹ ∫ f`, for every shift `x`.

This is the mechanism by which a configuration placed on an arithmetic progression of spacing `s`,
with weights of Fourier width below `1/s` minus the bandwidth of the test function, is
indistinguishable from its own continuum average by every test function of exponential type below
the Nyquist frequency.
-/

open Complex Real MeasureTheory
open scoped FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Fourier transform of a positive dilation: `𝓕 (f (c ·)) (w) = c⁻¹ 𝓕 f (w / c)`. -/
theorem fourier_comp_mul_pos {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) (w : ℝ) :
    (𝓕 fun v : ℝ => f (c * v)) w = (c : ℂ)⁻¹ * (𝓕 f) (w / c) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have harg : ∀ v : ℝ, v * w = (c * v) * (w / c) := by
    intro v; field_simp
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have hrewrite : ∀ v : ℝ,
      Real.fourierChar (-(v * w)) • f (c * v) =
        (fun u : ℝ => Real.fourierChar (-(u * (w / c))) • f u) (c * v) := by
    intro v
    simp only
    rw [harg v]
  simp only [hrewrite]
  rw [MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => Real.fourierChar (-(u * (w / c))) • f u) c,
    abs_of_pos (inv_pos.mpr hc), Complex.real_smul, Complex.ofReal_inv]

/-- Scalar dilation of the line as a continuous linear equivalence. -/
def realScaleEquiv {c : ℝ} (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toFun v := c * v
  invFun v := c⁻¹ * v
  map_add' x y := by ring
  map_smul' m x := by
    simp only [smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by field_simp
  right_inv v := by field_simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem realScaleEquiv_apply {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    realScaleEquiv hc v = c * v := rfl

/-- The dilated Schwartz function `v ↦ f (c v)`. -/
def schwartzScale (f : SchwartzMap ℝ ℂ) {c : ℝ} (hc : c ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realScaleEquiv hc) f

@[simp] theorem schwartzScale_apply (f : SchwartzMap ℝ ℂ) {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    schwartzScale f hc v = f (c * v) := rfl

/-- The Fourier transform at the origin is the integral. -/
theorem fourier_zero_eq_integral (f : ℝ → ℂ) : (𝓕 f) 0 = ∫ v, f v := by
  rw [Real.fourier_real_eq]
  simp

/-- **Nyquist lattice sum.** If `𝓕 f` vanishes at every frequency of modulus `≥ 1/s`, the lattice
sum of `f` over `x + sℤ` equals `s⁻¹ ∫ f`, independently of the shift `x`. -/
theorem tsum_lattice_eq_integral_of_fourier_vanishes (f : SchwartzMap ℝ ℂ) {s : ℝ} (hs : 0 < s)
    (hband : ∀ ξ : ℝ, 1 / s ≤ |ξ| → (𝓕 (f : ℝ → ℂ)) ξ = 0) (x : ℝ) :
    ∑' n : ℤ, f (x + n * s) = (s : ℂ)⁻¹ * ∫ v, f v := by
  have hsne : s ≠ 0 := ne_of_gt hs
  obtain ⟨g, hg⟩ : ∃ g : SchwartzMap ℝ ℂ, g = schwartzScale f hsne := ⟨_, rfl⟩
  -- the lattice sum of `f` is the unit-lattice sum of the dilation at the shift `x / s`
  have hshift : ∀ n : ℤ, f (x + n * s) = g (x / s + n) := by
    intro n
    rw [hg, schwartzScale_apply]
    congr 1
    field_simp
  -- the Fourier transform of the dilation
  have hgF : ∀ w : ℝ, (𝓕 (g : ℝ → ℂ)) w = (s : ℂ)⁻¹ * (𝓕 (f : ℝ → ℂ)) (w / s) := by
    intro w
    have : (g : ℝ → ℂ) = fun v : ℝ => (f : ℝ → ℂ) (s * v) := by
      funext v; rw [hg, schwartzScale_apply]
    rw [this]
    exact fourier_comp_mul_pos hs (f : ℝ → ℂ) w
  calc ∑' n : ℤ, f (x + n * s) = ∑' n : ℤ, g (x / s + n) := by
        exact tsum_congr fun n => hshift n
    _ = ∑' k : ℤ, (𝓕 (g : ℝ → ℂ)) k * fourier k ((x / s : ℝ) : UnitAddCircle) :=
        SchwartzMap.tsum_eq_tsum_fourier g (x / s)
    _ = (fun k : ℤ => (𝓕 (g : ℝ → ℂ)) k * fourier k ((x / s : ℝ) : UnitAddCircle)) 0 := by
        refine tsum_eq_single 0 ?_
        intro k hk
        show (𝓕 (g : ℝ → ℂ)) k * fourier k ((x / s : ℝ) : UnitAddCircle) = 0
        rw [hgF]
        have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
          have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
          exact_mod_cast this
        have hξ : 1 / s ≤ |(k : ℝ) / s| := by
          rw [abs_div, abs_of_pos hs]
          exact div_le_div_of_nonneg_right hk1 hs.le
        rw [hband _ hξ]
        ring
    _ = (s : ℂ)⁻¹ * ∫ v, f v := by
        simp only [Int.cast_zero, fourier_zero, mul_one]
        rw [hgF, zero_div, fourier_zero_eq_integral]

end GaloisForLFunctions.HTGeometry

end
