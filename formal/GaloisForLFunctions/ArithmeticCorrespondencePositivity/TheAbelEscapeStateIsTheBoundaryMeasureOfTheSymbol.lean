import GaloisForLFunctions.RHTower.CausalLaplacePlancherel

/-!
# The Abel escape state is the boundary measure of the symbol

The escape states of the damped Möbius receiver are limits of normalized translation Grams of one
log profile `g` (`TheCofactorGramIsATranslationGram`), whose Laplace transform is the symbol `G`
(`TheLaplaceFormOfTheCofactorProfile`). With a sharp horizon their classification needs a split of
the profile into a dominant configuration and a subdominant remainder, i.e. an explicit formula.
This file replaces the sharp horizon by the Abel weight `e^{−2cu}` and reads the escape states
directly from the symbol on vertical lines.

* **Wiener–Khinchin** (`integral_translate_mul_translate`). For real `ψ ∈ L¹ ∩ L²`,
  `∫ ψ(u − a) ψ(u − b) du = (2π)⁻¹ ∫ ‖ψ̂(y)‖² cos(y(a − b)) dy`.
* **The Abel Gram is spectral** (`abelGram_spectral`). The Abel Gram
  `A_c(a, b) = ∫ e^{−2cu} g(u − a) g(u − b) du` equals
  `e^{−c(a+b)} (2π)⁻¹ ∫ ‖G(c + iy)‖² cos(y(a − b)) dy`: an exponential weight times the cosine
  transform of the energy density of the symbol on `Re s = c`.
* **Exact dilation covariance** (`abelGram_add_add`). `A_c(a + t, b + t) = e^{−2ct} A_c(a, b)`: on
  Abel Grams dilation by `p` is the scalar `p^{−2c}`; the phase rotation of the horizon escape
  states (`OnEscapeStatesDilationIsTheArchimedeanFlow`) is averaged out.
* **The atom law** (`tendsto_window_atom`). A simple pole `r/(s − θ − iy₀)` of the symbol on the
  line `Re s = θ` with bounded regular part carries, in the scaled limit `ε = c − θ ↓ 0`, the spectral
  atom `π ‖r‖² δ_{y₀}`; a window on which the symbol stays bounded carries nothing
  (`tendsto_window_regular`).
* **The Abel escape law** (`tendsto_abelGram_of_poles`, `tendsto_abelGram_div_of_poles`). If the
  poles of the symbol on the abscissa line are `θ + iy_k` with residues `r_k` and the spectral mass
  outside their windows is `o(1/ε)`, then
  `ε A_{θ+ε}(a, b) → e^{−θ(a+b)} Σ_k (‖r_k‖²/2) cos(y_k(a − b))`, and the normalized Abel Grams
  converge to the diagonal kernel of the poles, one rank-one term per character.
* **Escape at infinite height** (`tendsto_window_mass_div_zero`). If the symbol extends boundedly
  across the abscissa line on every compact window and the Abel energy diverges, the normalized
  spectral measure leaves every compact window: the escape lives at infinite height.

So the finite-height part of an Abel escape state is determined by the poles of the symbol on its
abscissa line alone — no contour shift and no growth bound between zeros enter — and the only
remaining datum is the spectral mass at infinite height.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open _root_.RHTower (laplaceBoundary integral_norm_sq_laplaceBoundary
  integrable_norm_sq_laplaceBoundary)

/-! ### Wiener–Khinchin for real profiles -/

/-- The boundary character `e^{−iyu}` has modulus one. -/
theorem norm_boundaryChar (y u : ℝ) : ‖Complex.exp (-((y : ℂ) * I) * (u : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-((y : ℂ) * I) * (u : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [this, Real.exp_zero]

theorem integrable_boundaryChar_mul {f : ℝ → ℂ} (hf : Integrable f) (y : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (-((y : ℂ) * I) * (u : ℂ)) * f u) := by
  refine hf.bdd_mul (c := 1) ?_ ?_
  · exact (by fun_prop :
      Measurable fun u : ℝ => Complex.exp (-((y : ℂ) * I) * (u : ℂ))).aestronglyMeasurable
  · filter_upwards [] with u
    rw [norm_boundaryChar]

/-- Additivity of the boundary transform on integrable inputs. -/
theorem laplaceBoundary_add {f h : ℝ → ℂ} (hf : Integrable f) (hh : Integrable h) (y : ℝ) :
    laplaceBoundary (fun u => f u + h u) y = laplaceBoundary f y + laplaceBoundary h y := by
  rw [laplaceBoundary, laplaceBoundary, laplaceBoundary, ← integral_add
    (integrable_boundaryChar_mul hf y) (integrable_boundaryChar_mul hh y)]
  refine integral_congr_ae ?_
  filter_upwards [] with u
  ring

/-- **Translation is a character.** Shifting the profile by `a` multiplies its boundary transform
by `e^{−iya}`. -/
theorem laplaceBoundary_translate (f : ℝ → ℂ) (a y : ℝ) :
    laplaceBoundary (fun u => f (u - a)) y =
      Complex.exp (-((y : ℂ) * I) * (a : ℂ)) * laplaceBoundary f y := by
  rw [laplaceBoundary, laplaceBoundary,
    ← integral_add_right_eq_self (fun u : ℝ => Complex.exp (-((y : ℂ) * I) * (u : ℂ)) * f (u - a)) a,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [] with u
  simp only [add_sub_cancel_right]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-- The pointwise polarization behind Wiener–Khinchin:
`‖(e_a + e_b) z‖² − ‖(e_a − e_b) z‖² = 4 ‖z‖² cos(y(a − b))` for boundary characters. -/
theorem norm_sq_char_add_sub (z : ℂ) (a b y : ℝ) :
    ‖Complex.exp (-((y : ℂ) * I) * (a : ℂ)) * z + Complex.exp (-((y : ℂ) * I) * (b : ℂ)) * z‖ ^ 2
      - ‖Complex.exp (-((y : ℂ) * I) * (a : ℂ)) * z - Complex.exp (-((y : ℂ) * I) * (b : ℂ)) * z‖ ^ 2
      = 4 * ‖z‖ ^ 2 * Real.cos (y * (a - b)) := by
  have ea : Complex.exp (-((y : ℂ) * I) * (a : ℂ)) = Real.cos (y * a) - Real.sin (y * a) * I := by
    rw [show -((y : ℂ) * I) * (a : ℂ) = ((-(y * a) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have eb : Complex.exp (-((y : ℂ) * I) * (b : ℂ)) = Real.cos (y * b) - Real.sin (y * b) * I := by
    rw [show -((y : ℂ) * I) * (b : ℂ) = ((-(y * b) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hp : Complex.exp (-((y : ℂ) * I) * (a : ℂ)) + Complex.exp (-((y : ℂ) * I) * (b : ℂ)) =
      ((Real.cos (y * a) + Real.cos (y * b) : ℝ) : ℂ) +
        ((-(Real.sin (y * a) + Real.sin (y * b)) : ℝ) : ℂ) * I := by
    rw [ea, eb]; push_cast; ring
  have hm : Complex.exp (-((y : ℂ) * I) * (a : ℂ)) - Complex.exp (-((y : ℂ) * I) * (b : ℂ)) =
      ((Real.cos (y * a) - Real.cos (y * b) : ℝ) : ℂ) +
        ((-(Real.sin (y * a) - Real.sin (y * b)) : ℝ) : ℂ) * I := by
    rw [ea, eb]; push_cast; ring
  rw [← add_mul, ← sub_mul, norm_mul, norm_mul, mul_pow, mul_pow, hp, hm]
  simp only [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [show y * (a - b) = y * a - y * b by ring, Real.cos_sub]
  ring

/-- **Wiener–Khinchin for real profiles.** The autocorrelation of a real `ψ ∈ L¹ ∩ L²` is the
cosine transform of its energy density:
`∫ ψ(u − a) ψ(u − b) du = (2π)⁻¹ ∫ ‖ψ̂(y)‖² cos(y(a − b)) dy`, `ψ̂` the boundary transform. -/
theorem integral_translate_mul_translate {ψ : ℝ → ℝ} (h1 : Integrable ψ) (h2 : MemLp ψ 2)
    (a b : ℝ) :
    ∫ u, ψ (u - a) * ψ (u - b) =
      (2 * Real.pi)⁻¹ * ∫ y, ‖laplaceBoundary (fun u => (ψ u : ℂ)) y‖ ^ 2 * Real.cos (y * (a - b)) := by
  set ψc : ℝ → ℂ := fun u => (ψ u : ℂ) with hψc
  have hc1 : Integrable ψc := h1.ofReal
  have hc2 : MemLp ψc 2 := h2.ofReal
  have ta1 : Integrable (fun u => ψc (u - a)) := hc1.comp_sub_right a
  have tb1 : Integrable (fun u => ψc (u - b)) := hc1.comp_sub_right b
  have ta2 : MemLp (fun u => ψc (u - a)) 2 := hc2.comp_measurePreserving (measurePreserving_sub_right _ a)
  have tb2 : MemLp (fun u => ψc (u - b)) 2 := hc2.comp_measurePreserving (measurePreserving_sub_right _ b)
  have tb1n : Integrable (fun u => -ψc (u - b)) := tb1.neg
  have tb2n : MemLp (fun u => -ψc (u - b)) 2 := tb2.neg
  have Pp := integral_norm_sq_laplaceBoundary (g := fun u => ψc (u - a) + ψc (u - b)) (ta1.add tb1) (ta2.add tb2)
  have Pm := integral_norm_sq_laplaceBoundary (g := fun u => ψc (u - a) + -ψc (u - b)) (ta1.add tb1n) (ta2.add tb2n)
  -- the transforms of the sum and the difference
  have Lp : ∀ y, laplaceBoundary (fun u => ψc (u - a) + ψc (u - b)) y =
      Complex.exp (-((y : ℂ) * I) * (a : ℂ)) * laplaceBoundary ψc y +
        Complex.exp (-((y : ℂ) * I) * (b : ℂ)) * laplaceBoundary ψc y := by
    intro y
    rw [laplaceBoundary_add ta1 tb1, laplaceBoundary_translate, laplaceBoundary_translate]
  have Lm : ∀ y, laplaceBoundary (fun u => ψc (u - a) + -ψc (u - b)) y =
      Complex.exp (-((y : ℂ) * I) * (a : ℂ)) * laplaceBoundary ψc y -
        Complex.exp (-((y : ℂ) * I) * (b : ℂ)) * laplaceBoundary ψc y := by
    intro y
    rw [laplaceBoundary_add ta1 tb1n]
    have hneg : laplaceBoundary (fun u => -ψc (u - b)) y =
        -laplaceBoundary (fun u => ψc (u - b)) y := by
      rw [laplaceBoundary, laplaceBoundary, ← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [] with u
      ring
    rw [hneg, laplaceBoundary_translate, laplaceBoundary_translate]
    ring
  -- integrability of the four energy densities
  have iLp := integrable_norm_sq_laplaceBoundary (g := fun u => ψc (u - a) + ψc (u - b)) (ta1.add tb1) (ta2.add tb2)
  have iLm := integrable_norm_sq_laplaceBoundary (g := fun u => ψc (u - a) + -ψc (u - b)) (ta1.add tb1n) (ta2.add tb2n)
  have iUp : Integrable (fun u => ‖ψc (u - a) + ψc (u - b)‖ ^ 2) :=
    (ta2.add tb2).integrable_norm_pow (p := 2) two_ne_zero
  have iUm : Integrable (fun u => ‖ψc (u - a) + -ψc (u - b)‖ ^ 2) :=
    (ta2.add tb2n).integrable_norm_pow (p := 2) two_ne_zero
  -- the time side: `‖F₊‖² − ‖F₋‖² = 4 ψ(u−a) ψ(u−b)`
  have hU : ∫ u, ψ (u - a) * ψ (u - b) =
      4⁻¹ * ((∫ u, ‖ψc (u - a) + ψc (u - b)‖ ^ 2) - ∫ u, ‖ψc (u - a) + -ψc (u - b)‖ ^ 2) := by
    rw [← integral_sub iUp iUm, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [] with u
    simp only [hψc, ← Complex.ofReal_neg, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    ring
  -- the frequency side
  have hY : (∫ y, ‖laplaceBoundary (fun u => ψc (u - a) + ψc (u - b)) y‖ ^ 2) -
      (∫ y, ‖laplaceBoundary (fun u => ψc (u - a) + -ψc (u - b)) y‖ ^ 2) =
      4 * ∫ y, ‖laplaceBoundary ψc y‖ ^ 2 * Real.cos (y * (a - b)) := by
    rw [← integral_sub iLp iLm, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [] with y
    rw [Lp y, Lm y, norm_sq_char_add_sub]
    ring
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [hU]
  have e1 : (∫ u, ‖ψc (u - a) + ψc (u - b)‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ y, ‖laplaceBoundary (fun u => ψc (u - a) + ψc (u - b)) y‖ ^ 2 := by
    rw [Pp]; field_simp
  have e2 : (∫ u, ‖ψc (u - a) + -ψc (u - b)‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ y, ‖laplaceBoundary (fun u => ψc (u - a) + -ψc (u - b)) y‖ ^ 2 := by
    rw [Pm]; field_simp
  rw [e1, e2, ← mul_sub, hY]
  ring


/-- The boundary transform of an integrable function is continuous. -/
theorem continuous_laplaceBoundary {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (laplaceBoundary f) := by
  refine continuous_of_dominated (bound := fun u => ‖f u‖) (fun y => ?_) (fun y => ?_) hf.norm ?_
  · exact (integrable_boundaryChar_mul hf y).aestronglyMeasurable
  · filter_upwards [] with u
    rw [norm_mul, norm_boundaryChar, one_mul]
  · filter_upwards [] with u
    exact (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp (-((y : ℂ) * I) * (u : ℂ))).mul continuous_const

/-! ### The Abel Gram and its spectral form -/

/-- The **Abel Gram** `A_c(a, b) = ∫ e^{−2cu} g(u − a) g(u − b) du` of a profile `g`. -/
def abelGram (g : ℝ → ℝ) (c a b : ℝ) : ℝ :=
  ∫ u, Real.exp (-(2 * c * u)) * (g (u - a) * g (u - b))

/-- The damped profile `e^{−cu} g(u)`. -/
def dampedProfile (g : ℝ → ℝ) (c u : ℝ) : ℝ := Real.exp (-(c * u)) * g u

/-- The symbol on the line `Re s = c`: `G(c + iy) = ∫ e^{−(c + iy)u} g(u) du`. -/
def lineSymbol (g : ℝ → ℝ) (c y : ℝ) : ℂ :=
  laplaceBoundary (fun u => (dampedProfile g c u : ℂ)) y

/-- The Abel weight factors through the damped profile:
`e^{−2cu} g(u − a) g(u − b) = e^{−c(a+b)} ψ_c(u − a) ψ_c(u − b)`. -/
theorem abelGram_eq_integral_dampedProfile (g : ℝ → ℝ) (c a b : ℝ) :
    abelGram g c a b = Real.exp (-(c * (a + b))) *
      ∫ u, dampedProfile g c (u - a) * dampedProfile g c (u - b) := by
  rw [abelGram, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [] with u
  simp only [dampedProfile]
  have : Real.exp (-(2 * c * u)) =
      Real.exp (-(c * (a + b))) * (Real.exp (-(c * (u - a))) * Real.exp (-(c * (u - b)))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [this]; ring

/-- **The Abel Gram is spectral.** For `ψ_c = e^{−cu} g ∈ L¹ ∩ L²`,
`A_c(a, b) = e^{−c(a+b)} (2π)⁻¹ ∫ ‖G(c + iy)‖² cos(y(a − b)) dy`. -/
theorem abelGram_spectral {g : ℝ → ℝ} {c : ℝ} (h1 : Integrable (dampedProfile g c))
    (h2 : MemLp (dampedProfile g c) 2) (a b : ℝ) :
    abelGram g c a b = Real.exp (-(c * (a + b))) *
      ((2 * Real.pi)⁻¹ * ∫ y, ‖lineSymbol g c y‖ ^ 2 * Real.cos (y * (a - b))) := by
  rw [abelGram_eq_integral_dampedProfile, integral_translate_mul_translate h1 h2]
  rfl

/-- **Exact dilation covariance.** `A_c(a + t, b + t) = e^{−2ct} A_c(a, b)`. -/
theorem abelGram_add_add (g : ℝ → ℝ) (c a b t : ℝ) :
    abelGram g c (a + t) (b + t) = Real.exp (-(2 * c * t)) * abelGram g c a b := by
  rw [abelGram, abelGram, ← integral_const_mul,
    ← integral_add_right_eq_self
      (fun u : ℝ => Real.exp (-(2 * c * u)) * (g (u - (a + t)) * g (u - (b + t)))) t]
  refine integral_congr_ae ?_
  filter_upwards [] with u
  simp only [add_sub_add_right_eq_sub]
  rw [show -(2 * c * (u + t)) = -(2 * c * t) + -(2 * c * u) by ring, Real.exp_add]
  ring

/-- The diagonal Abel Gram is the Abel energy `∫ e^{−2cu} g(u)² du`, and the total spectral mass
of the line is `2π` times it. -/
theorem integral_norm_sq_lineSymbol {g : ℝ → ℝ} {c : ℝ} (h1 : Integrable (dampedProfile g c))
    (h2 : MemLp (dampedProfile g c) 2) :
    ∫ y, ‖lineSymbol g c y‖ ^ 2 = 2 * Real.pi * abelGram g c 0 0 := by
  have h := abelGram_spectral h1 h2 0 0
  simp only [add_zero, mul_zero, neg_zero, Real.exp_zero, one_mul, sub_zero, Real.cos_zero,
    mul_one] at h
  rw [h]
  field_simp

/-! ### The atom law -/

/-- `ε/√(ε² + τ²) ≤ 1`. -/
theorem div_sqrt_sq_add_sq_le_one {ε τ : ℝ} (hε : 0 < ε) : ε / Real.sqrt (ε ^ 2 + τ ^ 2) ≤ 1 := by
  have hpos : 0 < Real.sqrt (ε ^ 2 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_one hpos]
  calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
    _ ≤ Real.sqrt (ε ^ 2 + τ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg τ])

/-- **The Poisson tail vanishes.** `∫_{y₀−δ}^{y₀+δ} ε/√(ε² + (y−y₀)²) dy → 0` as `ε ↓ 0`. -/
theorem tendsto_integral_poissonTail (y₀ δ : ℝ) :
    Tendsto (fun ε : ℝ => ∫ y in (y₀ - δ)..(y₀ + δ), ε / Real.sqrt (ε ^ 2 + (y - y₀) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _y in (y₀ - δ)..(y₀ + δ), (0 : ℝ)) by simp]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine (Continuous.div continuous_const (by fun_prop) fun y => ?_).aestronglyMeasurable
    exact (Real.sqrt_pos.mpr (by have : (0 : ℝ) < ε := hε; positivity)).ne'
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [] with y _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (le_of_lt hε) (Real.sqrt_nonneg _))]
    exact div_sqrt_sq_add_sq_le_one hε
  · have hae : ∀ᵐ y : ℝ ∂volume, y ≠ y₀ := by
      rw [ae_iff]; simp
    filter_upwards [hae] with y hy _
    have hτ : 0 < (y - y₀) ^ 2 := by
      have : y - y₀ ≠ 0 := sub_ne_zero.mpr hy
      positivity
    have hc : ContinuousAt (fun ε : ℝ => ε / Real.sqrt (ε ^ 2 + (y - y₀) ^ 2)) 0 := by
      refine ContinuousAt.div continuousAt_id (by fun_prop) ?_
      rw [zero_pow two_ne_zero, zero_add]
      exact (Real.sqrt_pos.mpr hτ).ne'
    have := hc.tendsto
    simp only [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds

/-- `ε ∫_{y₀−δ}^{y₀+δ} dy/(ε² + (y−y₀)²) = 2 arctan(δ/ε)`. -/
theorem mul_integral_lorentz (y₀ δ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ y in (y₀ - δ)..(y₀ + δ), 1 / (ε ^ 2 + (y - y₀) ^ 2) = 2 * Real.arctan (δ / ε) := by
  rw [intervalIntegral.integral_comp_sub_right (fun τ => 1 / (ε ^ 2 + τ ^ 2)) y₀]
  simp only [sub_sub_cancel_left, add_sub_cancel_left]
  have hrw : (fun τ : ℝ => 1 / (ε ^ 2 + τ ^ 2)) = fun τ => (ε ^ 2)⁻¹ * (1 / (1 + (τ / ε) ^ 2)) := by
    funext τ
    field_simp
  rw [hrw, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x => 1 / (1 + x ^ 2)) hε.ne', integral_one_div_one_add_sq,
    neg_div, Real.arctan_neg, smul_eq_mul]
  field_simp
  ring

/-- `2 arctan(δ/ε) → π` as `ε ↓ 0`. -/
theorem tendsto_two_arctan_div (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ => 2 * Real.arctan (δ / ε)) (𝓝[>] 0) (𝓝 Real.pi) := by
  have h1 : Tendsto (fun ε : ℝ => δ / ε) (𝓝[>] 0) atTop := by
    simp only [div_eq_mul_inv]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop hδ
  have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
  have h3 := h2.const_mul 2
  rwa [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at h3


/-- `‖ε + τ i‖ = √(ε² + τ²)`. -/
theorem norm_ofReal_add_mul_I (ε τ : ℝ) : ‖(ε : ℂ) + (τ : ℂ) * I‖ = Real.sqrt (ε ^ 2 + τ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_add_mul_I]

/-- **The pointwise atom estimate.** Near a simple pole `r/(ε + iτ)` of a symbol `G` with bounded
regular part, `ε ‖G‖² w` differs from the Lorentzian `ε ‖r‖² w(y₀)/(ε² + τ²)` by at most
`(2WM‖r‖ + ‖r‖²L) ε/√(ε² + τ²) + W M² ε`. -/
theorem norm_atom_integrand_sub_le {g r : ℂ} {ε τ M L W wy w₀ : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hg : ‖g - r / ((ε : ℂ) + (τ : ℂ) * I)‖ ≤ M)
    (hwL : |wy - w₀| ≤ L * |τ|) (hwW : |wy| ≤ W) :
    ‖ε * (‖g‖ ^ 2 * wy) - ε * (‖r‖ ^ 2 * w₀ / (ε ^ 2 + τ ^ 2))‖ ≤
      (2 * W * M * ‖r‖ + ‖r‖ ^ 2 * L) * (ε / Real.sqrt (ε ^ 2 + τ ^ 2)) + W * M ^ 2 * ε := by
  set D := ε ^ 2 + τ ^ 2 with hD
  set S := Real.sqrt D with hS
  have hDpos : 0 < D := by positivity
  have hSpos : 0 < S := Real.sqrt_pos.mpr hDpos
  have hSS : S ^ 2 = D := Real.sq_sqrt hDpos.le
  have hτS : |τ| ≤ S := by
    rw [hS, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  set P := r / ((ε : ℂ) + (τ : ℂ) * I) with hP
  have hPn : ‖P‖ = ‖r‖ / S := by rw [hP, norm_div, norm_ofReal_add_mul_I]
  have hP2 : ‖P‖ ^ 2 = ‖r‖ ^ 2 / D := by rw [hPn, div_pow, hSS]
  have hgP : |‖g‖ - ‖P‖| ≤ M := (abs_norm_sub_norm_le g P).trans hg
  have hgle : ‖g‖ ≤ ‖P‖ + M := by linarith [abs_le.mp hgP]
  have hsq : |‖g‖ ^ 2 - ‖P‖ ^ 2| ≤ M * (2 * ‖P‖ + M) := by
    rw [show ‖g‖ ^ 2 - ‖P‖ ^ 2 = (‖g‖ - ‖P‖) * (‖g‖ + ‖P‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ‖g‖ + ‖P‖)]
    exact mul_le_mul hgP (by linarith) (by positivity) hM
  have hsplit : ε * (‖g‖ ^ 2 * wy) - ε * (‖r‖ ^ 2 * w₀ / D) =
      ε * ((‖g‖ ^ 2 - ‖P‖ ^ 2) * wy) + ε * (‖P‖ ^ 2 * (wy - w₀)) := by
    rw [hP2]; field_simp; ring
  rw [Real.norm_eq_abs, hsplit]
  have h1 : |ε * ((‖g‖ ^ 2 - ‖P‖ ^ 2) * wy)| ≤ 2 * W * M * ‖r‖ * (ε / S) + W * M ^ 2 * ε := by
    rw [abs_mul, abs_mul, abs_of_pos hε]
    calc ε * (|‖g‖ ^ 2 - ‖P‖ ^ 2| * |wy|) ≤ ε * ((M * (2 * ‖P‖ + M)) * W) := by
          gcongr
      _ = 2 * W * M * ‖r‖ * (ε / S) + W * M ^ 2 * ε := by rw [hPn]; ring
  have h2 : |ε * (‖P‖ ^ 2 * (wy - w₀))| ≤ ‖r‖ ^ 2 * L * (ε / S) := by
    rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_nonneg (sq_nonneg _), hP2]
    calc ε * (‖r‖ ^ 2 / D * |wy - w₀|) ≤ ε * (‖r‖ ^ 2 / D * (L * |τ|)) := by gcongr
      _ ≤ ε * (‖r‖ ^ 2 / D * (L * S)) := by gcongr
      _ = ‖r‖ ^ 2 * L * (ε / S) := by rw [← hSS]; field_simp
  calc |ε * ((‖g‖ ^ 2 - ‖P‖ ^ 2) * wy) + ε * (‖P‖ ^ 2 * (wy - w₀))|
      ≤ |ε * ((‖g‖ ^ 2 - ‖P‖ ^ 2) * wy)| + |ε * (‖P‖ ^ 2 * (wy - w₀))| := abs_add_le _ _
    _ ≤ _ := by linarith


/-- **The atom law.** Let `S ε y` be a symbol on the lines `Re s = θ + ε` (`S ε y = G(θ + ε + iy)`)
with a simple pole `r/(ε + i(y − y₀))` at `θ + iy₀` and regular part bounded by `M` on the box
`0 < ε < δ`, `|y − y₀| ≤ δ`. Then for every Lipschitz bounded weight `w` the `ε`-scaled spectral
mass of the window converges to the atom of the pole:
`ε ∫_{y₀−δ}^{y₀+δ} ‖S ε y‖² w(y) dy → π ‖r‖² w(y₀)` as `ε ↓ 0`. -/
theorem tendsto_window_atom {S : ℝ → ℝ → ℂ} {y₀ δ M L W : ℝ} {r : ℂ} {w : ℝ → ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hcont : ∀ ε ∈ Ioo 0 δ,
      ContinuousOn (fun y : ℝ => S ε y) (Icc (y₀ - δ) (y₀ + δ)))
    (hpole : ∀ ε ∈ Ioo 0 δ, ∀ y ∈ Icc (y₀ - δ) (y₀ + δ),
      ‖S ε y - r / ((ε : ℂ) + ((y - y₀ : ℝ) : ℂ) * I)‖ ≤ M)
    (hw : Continuous w) (hwL : ∀ y, |w y - w y₀| ≤ L * |y - y₀|) (hwW : ∀ y, |w y| ≤ W) :
    Tendsto (fun ε : ℝ =>
        ε * ∫ y in (y₀ - δ)..(y₀ + δ), ‖S ε y‖ ^ 2 * w y)
      (𝓝[>] 0) (𝓝 (Real.pi * ‖r‖ ^ 2 * w y₀)) := by
  have hab : y₀ - δ ≤ y₀ + δ := by linarith
  set K₁ := 2 * W * M * ‖r‖ + ‖r‖ ^ 2 * L with hK₁
  set K₂ := W * M ^ 2 with hK₂
  -- the Lorentzian main term
  have hmain : Tendsto (fun ε : ℝ => ‖r‖ ^ 2 * w y₀ *
      (ε * ∫ y in (y₀ - δ)..(y₀ + δ), 1 / (ε ^ 2 + (y - y₀) ^ 2)))
      (𝓝[>] 0) (𝓝 (Real.pi * ‖r‖ ^ 2 * w y₀)) := by
    have h := (tendsto_two_arctan_div δ hδ).const_mul (‖r‖ ^ 2 * w y₀)
    rw [show ‖r‖ ^ 2 * w y₀ * Real.pi = Real.pi * ‖r‖ ^ 2 * w y₀ by ring] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [mul_integral_lorentz y₀ δ hε]
  -- the bound on the difference
  have hbound : Tendsto (fun ε : ℝ =>
      K₁ * (∫ y in (y₀ - δ)..(y₀ + δ), ε / Real.sqrt (ε ^ 2 + (y - y₀) ^ 2)) +
        K₂ * ε * (2 * δ)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (tendsto_integral_poissonTail y₀ δ).const_mul K₁
    have h2 : Tendsto (fun ε : ℝ => K₂ * ε * (2 * δ)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => K₂ * ε * (2 * δ)) (𝓝 0) (𝓝 (K₂ * 0 * (2 * δ))) :=
        ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using h1.add h2
  have hdiff : Tendsto (fun ε : ℝ =>
      ε * (∫ y in (y₀ - δ)..(y₀ + δ), ‖S ε y‖ ^ 2 * w y) -
        ‖r‖ ^ 2 * w y₀ * (ε * ∫ y in (y₀ - δ)..(y₀ + δ), 1 / (ε ^ 2 + (y - y₀) ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    have hδmem : Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ
    filter_upwards [hδmem] with ε hε
    have hε0 : 0 < ε := hε.1
    have hGi : IntervalIntegrable (fun y : ℝ => ‖S ε y‖ ^ 2 * w y)
        volume (y₀ - δ) (y₀ + δ) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      exact ((hcont ε hε).norm.pow 2).mul hw.continuousOn
    have hLc : Continuous fun y : ℝ => ‖r‖ ^ 2 * w y₀ / (ε ^ 2 + (y - y₀) ^ 2) :=
      Continuous.div continuous_const (by fun_prop) fun y => by positivity
    have hLi := hLc.intervalIntegrable (μ := volume) (y₀ - δ) (y₀ + δ)
    have hrw : ε * (∫ y in (y₀ - δ)..(y₀ + δ), ‖S ε y‖ ^ 2 * w y) -
        ‖r‖ ^ 2 * w y₀ * (ε * ∫ y in (y₀ - δ)..(y₀ + δ), 1 / (ε ^ 2 + (y - y₀) ^ 2)) =
        ∫ y in (y₀ - δ)..(y₀ + δ), (ε * (‖S ε y‖ ^ 2 * w y) -
          ε * (‖r‖ ^ 2 * w y₀ / (ε ^ 2 + (y - y₀) ^ 2))) := by
      rw [intervalIntegral.integral_sub (hGi.const_mul ε) (hLi.const_mul ε),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      have hc : (∫ x in (y₀ - δ)..(y₀ + δ), ‖r‖ ^ 2 * w y₀ / (ε ^ 2 + (x - y₀) ^ 2)) =
          ‖r‖ ^ 2 * w y₀ * ∫ x in (y₀ - δ)..(y₀ + δ), 1 / (ε ^ 2 + (x - y₀) ^ 2) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext x
        ring
      rw [hc]
      ring
    rw [hrw]
    have hti : IntervalIntegrable (fun y : ℝ => K₁ * (ε / Real.sqrt (ε ^ 2 + (y - y₀) ^ 2)) +
        K₂ * ε) volume (y₀ - δ) (y₀ + δ) := by
      refine Continuous.intervalIntegrable ?_ _ _
      refine Continuous.add (Continuous.mul continuous_const
        (Continuous.div continuous_const (by fun_prop) fun y => ?_)) continuous_const
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    calc ‖∫ y in (y₀ - δ)..(y₀ + δ), (ε * (‖S ε y‖ ^ 2 * w y) -
          ε * (‖r‖ ^ 2 * w y₀ / (ε ^ 2 + (y - y₀) ^ 2)))‖
        ≤ ∫ y in (y₀ - δ)..(y₀ + δ), (K₁ * (ε / Real.sqrt (ε ^ 2 + (y - y₀) ^ 2)) + K₂ * ε) := by
          refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hti
          filter_upwards [] with y hy
          have hyI : y ∈ Icc (y₀ - δ) (y₀ + δ) := Ioc_subset_Icc_self hy
          exact norm_atom_integrand_sub_le hε0 hM hL (hpole ε hε y hyI)
            (hwL y) (hwW y)
      _ = K₁ * (∫ y in (y₀ - δ)..(y₀ + δ), ε / Real.sqrt (ε ^ 2 + (y - y₀) ^ 2)) +
            K₂ * ε * (2 * δ) := by
          rw [intervalIntegral.integral_add ?_ intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          · simp only [smul_eq_mul]; ring
          · refine Continuous.intervalIntegrable ?_ _ _
            refine Continuous.mul continuous_const
              (Continuous.div continuous_const (by fun_prop) fun y => ?_)
            exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have := hdiff.add hmain
  simp only [sub_add_cancel, zero_add] at this
  exact this


/-- **A regular window carries no atom.** If the symbol stays bounded on a window, the `ε`-scaled
spectral mass of the window tends to zero. -/
theorem tendsto_window_regular {S : ℝ → ℝ → ℂ} {y₁ y₂ δ B W : ℝ} {w : ℝ → ℝ} (hδ : 0 < δ)
    (hbd : ∀ ε ∈ Ioo 0 δ, ∀ y ∈ uIcc y₁ y₂, ‖S ε y‖ ≤ B) (hwW : ∀ y, |w y| ≤ W) :
    Tendsto (fun ε : ℝ => ε * ∫ y in y₁..y₂, ‖S ε y‖ ^ 2 * w y) (𝓝[>] 0) (𝓝 0) := by
  have hlin : Tendsto (fun ε : ℝ => ε * (B ^ 2 * W * |y₂ - y₁|)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => ε * (B ^ 2 * W * |y₂ - y₁|)) (𝓝 0)
        (𝓝 (0 * (B ^ 2 * W * |y₂ - y₁|))) := (continuous_id.mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlin
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hε.1]
  refine mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const ?_) hε.1.le
  intro y hy
  rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
  have hB := hbd ε hε y (uIoc_subset_uIcc hy)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hB 2) (hwW y) (abs_nonneg _) (by positivity)

/-- The boundary symbol of an integrable damped profile is continuous in the height. -/
theorem continuous_lineSymbol {g : ℝ → ℝ} {c : ℝ} (h1 : Integrable (dampedProfile g c)) :
    Continuous (lineSymbol g c) :=
  continuous_laplaceBoundary h1.ofReal

/-- The spectral density `‖G(c + iy)‖² cos(y h)` of an `L¹ ∩ L²` damped profile is integrable. -/
theorem integrable_lineSymbol_sq_mul_cos {g : ℝ → ℝ} {c : ℝ} (h1 : Integrable (dampedProfile g c))
    (h2 : MemLp (dampedProfile g c) 2) (h : ℝ) :
    Integrable (fun y => ‖lineSymbol g c y‖ ^ 2 * Real.cos (y * h)) :=
  (integrable_norm_sq_laplaceBoundary h1.ofReal h2.ofReal).mul_bdd (c := 1)
    (by fun_prop : Continuous fun y : ℝ => Real.cos (y * h)).aestronglyMeasurable
    (by filter_upwards [] with y; rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- **The Abel escape law.** Let the symbol of a profile have, on the abscissa line `Re s = θ`,
simple poles `θ + iy_k` (`k ∈ s`) with residues `r_k` and regular parts bounded on disjoint windows,
and let the spectral mass outside the windows be `o(1/ε)`. Then the scaled Abel Grams converge to
the diagonal kernel of the poles:
`ε A_{θ+ε}(a, b) → e^{−θ(a+b)} Σ_k (‖r_k‖²/2) cos(y_k(a − b))`. -/
theorem tendsto_abelGram_of_poles {g : ℝ → ℝ} {θ δ M : ℝ} {ι : Type*} (s : Finset ι)
    (y₀ : ι → ℝ) (r : ι → ℂ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (h1 : ∀ ε ∈ Ioo 0 δ, Integrable (dampedProfile g (θ + ε)))
    (h2 : ∀ ε ∈ Ioo 0 δ, MemLp (dampedProfile g (θ + ε)) 2)
    (hdisj : (s : Set ι).Pairwise (Function.onFun Disjoint fun k => Icc (y₀ k - δ) (y₀ k + δ)))
    (hpole : ∀ k ∈ s, ∀ ε ∈ Ioo 0 δ, ∀ y ∈ Icc (y₀ k - δ) (y₀ k + δ),
      ‖lineSymbol g (θ + ε) y - r k / ((ε : ℂ) + ((y - y₀ k : ℝ) : ℂ) * I)‖ ≤ M)
    (hout : Tendsto (fun ε : ℝ => ε * ∫ y in (⋃ k ∈ s, Icc (y₀ k - δ) (y₀ k + δ))ᶜ,
      ‖lineSymbol g (θ + ε) y‖ ^ 2) (𝓝[>] 0) (𝓝 0)) (a b : ℝ) :
    Tendsto (fun ε : ℝ => ε * abelGram g (θ + ε) a b) (𝓝[>] 0)
      (𝓝 (Real.exp (-(θ * (a + b))) * ∑ k ∈ s, ‖r k‖ ^ 2 / 2 * Real.cos (y₀ k * (a - b)))) := by
  set U := ⋃ k ∈ s, Icc (y₀ k - δ) (y₀ k + δ) with hU
  set f : ℝ → ℝ → ℝ := fun ε y => ‖lineSymbol g (θ + ε) y‖ ^ 2 * Real.cos (y * (a - b)) with hf
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion s fun _ _ => measurableSet_Icc
  -- the windows: each carries its atom
  have hwin : Tendsto (fun ε : ℝ => ∑ k ∈ s, ε * ∫ y in (y₀ k - δ)..(y₀ k + δ), f ε y) (𝓝[>] 0)
      (𝓝 (∑ k ∈ s, Real.pi * ‖r k‖ ^ 2 * Real.cos (y₀ k * (a - b)))) := by
    refine tendsto_finsetSum s fun k hk => ?_
    refine tendsto_window_atom (S := fun ε y => lineSymbol g (θ + ε) y) (L := |a - b|) (W := 1)
      hδ hM (abs_nonneg _) (fun ε hε => (continuous_lineSymbol (h1 ε hε)).continuousOn)
      (fun ε hε y hy => hpole k hk ε hε y hy) (by fun_prop) (fun y => ?_)
      (fun y => Real.abs_cos_le_one _)
    calc |Real.cos (y * (a - b)) - Real.cos (y₀ k * (a - b))| ≤ |y * (a - b) - y₀ k * (a - b)| :=
          Real.abs_cos_sub_cos_le _ _
      _ = |a - b| * |y - y₀ k| := by rw [← sub_mul, abs_mul, mul_comm]
  -- the complement: bounded by the outside mass
  have hcomp : Tendsto (fun ε : ℝ => ε * ∫ y in Uᶜ, f ε y) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hout
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hε.1]
    refine mul_le_mul_of_nonneg_left ?_ hε.1.le
    refine (norm_integral_le_integral_norm _).trans (setIntegral_mono ?_ ?_ fun y => ?_)
    · exact (integrable_lineSymbol_sq_mul_cos (h1 ε hε) (h2 ε hε) (a - b)).norm.integrableOn
    · exact (integrable_norm_sq_laplaceBoundary (h1 ε hε).ofReal (h2 ε hε).ofReal).integrableOn
    · simp only [hf, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have hexp : Tendsto (fun ε : ℝ => Real.exp (-((θ + ε) * (a + b)))) (𝓝[>] 0)
      (𝓝 (Real.exp (-(θ * (a + b))))) := by
    have : Continuous fun ε : ℝ => Real.exp (-((θ + ε) * (a + b))) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hall := hexp.mul (((hwin.add hcomp).const_mul (2 * Real.pi)⁻¹))
  have hlim : Real.exp (-(θ * (a + b))) * ((2 * Real.pi)⁻¹ *
      ((∑ k ∈ s, Real.pi * ‖r k‖ ^ 2 * Real.cos (y₀ k * (a - b))) + 0)) =
      Real.exp (-(θ * (a + b))) * ∑ k ∈ s, ‖r k‖ ^ 2 / 2 * Real.cos (y₀ k * (a - b)) := by
    rw [add_zero, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [hlim] at hall
  refine hall.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hI : Integrable (f ε) := integrable_lineSymbol_sq_mul_cos (h1 ε hε) (h2 ε hε) (a - b)
  have hsplit : ∫ y, f ε y =
      (∑ k ∈ s, ∫ y in (y₀ k - δ)..(y₀ k + δ), f ε y) + ∫ y in Uᶜ, f ε y := by
    rw [← integral_add_compl hUm hI, hU, integral_biUnion_finset s (fun _ _ => measurableSet_Icc)
      hdisj (fun _ _ => hI.integrableOn)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  have hfe : (∫ y, ‖lineSymbol g (θ + ε) y‖ ^ 2 * Real.cos (y * (a - b))) = ∫ y, f ε y := rfl
  rw [abelGram_spectral (h1 ε hε) (h2 ε hε), hfe, hsplit, ← Finset.mul_sum]
  ring

/-- **The normalized Abel escape state.** Under the hypotheses of the escape law, with some
nonzero residue, the normalized Abel Grams converge to the normalized diagonal kernel of the poles:
`A_{θ+ε}(a, b)/A_{θ+ε}(0, 0) → e^{−θ(a+b)} Σ_k ‖r_k‖² cos(y_k(a − b)) / Σ_k ‖r_k‖²`. -/
theorem tendsto_abelGram_div_of_poles {g : ℝ → ℝ} {θ δ M : ℝ} {ι : Type*} (s : Finset ι)
    (y₀ : ι → ℝ) (r : ι → ℂ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (h1 : ∀ ε ∈ Ioo 0 δ, Integrable (dampedProfile g (θ + ε)))
    (h2 : ∀ ε ∈ Ioo 0 δ, MemLp (dampedProfile g (θ + ε)) 2)
    (hdisj : (s : Set ι).Pairwise (Function.onFun Disjoint fun k => Icc (y₀ k - δ) (y₀ k + δ)))
    (hpole : ∀ k ∈ s, ∀ ε ∈ Ioo 0 δ, ∀ y ∈ Icc (y₀ k - δ) (y₀ k + δ),
      ‖lineSymbol g (θ + ε) y - r k / ((ε : ℂ) + ((y - y₀ k : ℝ) : ℂ) * I)‖ ≤ M)
    (hout : Tendsto (fun ε : ℝ => ε * ∫ y in (⋃ k ∈ s, Icc (y₀ k - δ) (y₀ k + δ))ᶜ,
      ‖lineSymbol g (θ + ε) y‖ ^ 2) (𝓝[>] 0) (𝓝 0))
    (hr : 0 < ∑ k ∈ s, ‖r k‖ ^ 2) (a b : ℝ) :
    Tendsto (fun ε : ℝ => abelGram g (θ + ε) a b / abelGram g (θ + ε) 0 0) (𝓝[>] 0)
      (𝓝 (Real.exp (-(θ * (a + b))) * (∑ k ∈ s, ‖r k‖ ^ 2 * Real.cos (y₀ k * (a - b))) /
        ∑ k ∈ s, ‖r k‖ ^ 2)) := by
  have hab := tendsto_abelGram_of_poles s y₀ r hδ hM h1 h2 hdisj hpole hout a b
  have h00 := tendsto_abelGram_of_poles s y₀ r hδ hM h1 h2 hdisj hpole hout 0 0
  simp only [add_zero, mul_zero, neg_zero, Real.exp_zero, one_mul, sub_zero, Real.cos_zero,
    mul_one] at h00
  have hne : (∑ k ∈ s, ‖r k‖ ^ 2 / 2) ≠ 0 := by
    rw [← Finset.sum_div]; positivity
  have hq := hab.div h00 hne
  have hval : Real.exp (-(θ * (a + b))) * (∑ k ∈ s, ‖r k‖ ^ 2 / 2 * Real.cos (y₀ k * (a - b))) /
      (∑ k ∈ s, ‖r k‖ ^ 2 / 2) = Real.exp (-(θ * (a + b))) *
        (∑ k ∈ s, ‖r k‖ ^ 2 * Real.cos (y₀ k * (a - b))) / ∑ k ∈ s, ‖r k‖ ^ 2 := by
    rw [← Finset.sum_div]
    have h2s : ∑ k ∈ s, ‖r k‖ ^ 2 / 2 * Real.cos (y₀ k * (a - b)) =
        (∑ k ∈ s, ‖r k‖ ^ 2 * Real.cos (y₀ k * (a - b))) / 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [h2s, mul_div_assoc, div_div_div_cancel_right₀ two_ne_zero, mul_div_assoc]
  rw [hval] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact mul_div_mul_left _ _ (ne_of_gt hε)

/-- **Escape at infinite height.** If the symbol stays bounded on a compact window uniformly near
the abscissa line while the total spectral mass diverges, the normalized spectral mass of the
window tends to zero. -/
theorem tendsto_window_mass_div_zero {S : ℝ → ℝ → ℂ} {y₁ y₂ δ B : ℝ} (hδ : 0 < δ)
    (hbd : ∀ ε ∈ Ioo 0 δ, ∀ y ∈ uIcc y₁ y₂, ‖S ε y‖ ≤ B)
    (htot : Tendsto (fun ε : ℝ => ∫ y, ‖S ε y‖ ^ 2) (𝓝[>] 0) atTop) :
    Tendsto (fun ε : ℝ => (∫ y in y₁..y₂, ‖S ε y‖ ^ 2) / ∫ y, ‖S ε y‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hC := (tendsto_const_nhds (x := B ^ 2 * |y₂ - y₁|)).div_atTop htot
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [Ioo_mem_nhdsGT hδ, htot.eventually_gt_atTop 0] with ε hε hpos
  rw [norm_div, Real.norm_eq_abs (∫ y, ‖S ε y‖ ^ 2), abs_of_pos hpos]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
  rw [norm_pow, norm_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbd ε hε y (uIoc_subset_uIcc hy)) 2

/-- **Abel escape without poles lives at infinite height.** If the Abel energy
`A_{θ+ε}(0, 0)` diverges and the symbol of the profile stays bounded on a compact window near the
abscissa line, the share of the window in the spectral measure of the line tends to zero. -/
theorem tendsto_lineSymbol_window_share_zero {g : ℝ → ℝ} {θ δ B y₁ y₂ : ℝ} (hδ : 0 < δ)
    (h1 : ∀ ε ∈ Ioo 0 δ, Integrable (dampedProfile g (θ + ε)))
    (h2 : ∀ ε ∈ Ioo 0 δ, MemLp (dampedProfile g (θ + ε)) 2)
    (hbd : ∀ ε ∈ Ioo 0 δ, ∀ y ∈ uIcc y₁ y₂, ‖lineSymbol g (θ + ε) y‖ ≤ B)
    (hesc : Tendsto (fun ε : ℝ => abelGram g (θ + ε) 0 0) (𝓝[>] 0) atTop) :
    Tendsto (fun ε : ℝ => (∫ y in y₁..y₂, ‖lineSymbol g (θ + ε) y‖ ^ 2) /
      ∫ y, ‖lineSymbol g (θ + ε) y‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_window_mass_div_zero (S := fun ε y => lineSymbol g (θ + ε) y) hδ hbd ?_
  have h2pi : Tendsto (fun ε : ℝ => 2 * Real.pi * abelGram g (θ + ε) 0 0) (𝓝[>] 0) atTop :=
    hesc.const_mul_atTop (by positivity)
  refine h2pi.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  rw [integral_norm_sq_lineSymbol (h1 ε hε) (h2 ε hε)]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
