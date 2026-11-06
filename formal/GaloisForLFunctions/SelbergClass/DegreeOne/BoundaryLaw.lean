import GaloisForLFunctions.SelbergClass.DegreeOne.ArchimedeanSymbol
import GaloisForLFunctions.SelbergClass.DegreeOne.LeftLineExpansion
import GaloisForLFunctions.SelbergClass.DegreeOne.AbelianBoundaryLimit
import GaloisForLFunctions.RHTower.SelbergShiftLatticeRegularity
import GaloisForLFunctions.RHTower.SelbergClass.FullConjugate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The boundary law of the exponential series at degree one

Let `F` have degree one, conductor `q`, internal shift `θ`, and put `f(z) = Σ a(n) e^{−nz}`.  There is a
constant `C ≠ 0` such that, as `y → 0⁺`,

* `y^{1−iθ} f(y + 2πim/q) → C · ā(m) · m^{−iθ}` for every integer `m ≥ 1`;
* `y^{1−iθ} f(y + iβ) → 0` for every other `β > 0` (`exists_boundary_law`).

So the boundary singularities of `f` on the positive imaginary axis lie on the lattice `(2π/q)ℕ`, and
their strengths are the conjugate coefficients.

**Mechanism.**  Past a far-left line the functional equation turns the Mellin integral of `Γ(u)F(u)` into
`Σ_n ā(n) n^{σ−1} ∫ z^{−u} n^{it} A(t) dt`.  By the symbol law, `A(t)` is
`e^{−πt/2} (q/2π)^{−it} t^{−iθ}` up to a constant, so each integral is a Laplace transform at
`ε + iτₙ`, where `ε = π/2 − arg z` and `τₙ = log(|z|q/2πn)`.  The Abelian limit detects `τₙ = 0`, and
Tannery's theorem passes the limit through the sum over `n`.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-! ### Geometry of the approach to the boundary -/

/-- The angle from `z` to the positive imaginary axis. -/
def gapAngle (z : ℂ) : ℝ := π / 2 - Complex.arg z

/-- The vertical approach to `iβ`. -/
def boundaryPath (β y : ℝ) : ℂ := (y : ℂ) + (β : ℂ) * I

theorem boundaryPath_re (β y : ℝ) : (boundaryPath β y).re = y := by simp [boundaryPath]

theorem boundaryPath_im (β y : ℝ) : (boundaryPath β y).im = β := by simp [boundaryPath]

theorem boundaryPath_ne_zero {β : ℝ} (hβ : 0 < β) (y : ℝ) : boundaryPath β y ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [boundaryPath_im] at this
  simp at this
  exact hβ.ne' this

theorem gapAngle_pos {z : ℂ} (hz : 0 < z.re) : 0 < gapAngle z := by
  have := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  unfold gapAngle
  linarith

theorem gapAngle_le {z : ℂ} (hz : 0 ≤ z.im) : gapAngle z ≤ π / 2 := by
  have := Complex.arg_nonneg_iff.mpr hz
  unfold gapAngle
  linarith

theorem sin_gapAngle {z : ℂ} (hz : z ≠ 0) : Real.sin (gapAngle z) = z.re / ‖z‖ := by
  unfold gapAngle
  rw [Real.sin_pi_div_two_sub, Complex.cos_arg hz]

theorem le_norm_boundaryPath {β : ℝ} (hβ : 0 < β) (y : ℝ) : β ≤ ‖boundaryPath β y‖ := by
  have h := Complex.abs_im_le_norm (boundaryPath β y)
  rw [boundaryPath_im, abs_of_pos hβ] at h
  exact h

theorem norm_boundaryPath_le {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) :
    ‖boundaryPath β y‖ ≤ y + β := by
  have h := norm_add_le (y : ℂ) ((β : ℂ) * I)
  simpa [boundaryPath, abs_of_pos hβ, abs_of_pos hy] using h

/-- The modulus exceeds `β` only to second order in `y`. -/
theorem norm_boundaryPath_le_second {β y : ℝ} (hβ : 0 < β) :
    ‖boundaryPath β y‖ ≤ β + y ^ 2 / (2 * β) := by
  have hnn : 0 ≤ β + y ^ 2 / (2 * β) := by positivity
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero, Complex.sq_norm, Complex.normSq_apply,
    boundaryPath_re, boundaryPath_im]
  have hcomp : (β + y ^ 2 / (2 * β)) ^ 2 = β ^ 2 + y ^ 2 + (y ^ 2 / (2 * β)) ^ 2 := by
    field_simp
    ring
  rw [hcomp]
  nlinarith [sq_nonneg (y ^ 2 / (2 * β))]

/-- `y/ε ≤ |z|`: the gap angle is at least the sine it subtends. -/
theorem div_gapAngle_le {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) :
    y / gapAngle (boundaryPath β y) ≤ ‖boundaryPath β y‖ := by
  have hz := boundaryPath_ne_zero hβ y
  have hgap := gapAngle_pos (z := boundaryPath β y) (by rwa [boundaryPath_re])
  have hsin := sin_gapAngle hz
  rw [boundaryPath_re] at hsin
  have hle := Real.sin_le hgap.le
  have hn : 0 < ‖boundaryPath β y‖ := norm_pos_iff.mpr hz
  rw [div_le_iff₀ hgap]
  rw [hsin, div_le_iff₀ hn] at hle
  linarith

theorem gapAngle_le_mul {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) :
    gapAngle (boundaryPath β y) ≤ π / 2 * (y / β) := by
  have hz := boundaryPath_ne_zero hβ y
  have hgap := gapAngle_pos (z := boundaryPath β y) (by rwa [boundaryPath_re])
  have hgap2 := gapAngle_le (z := boundaryPath β y) (by rw [boundaryPath_im]; exact hβ.le)
  have hsin := sin_gapAngle hz
  rw [boundaryPath_re] at hsin
  have hmul := Real.mul_le_sin hgap.le hgap2
  rw [hsin] at hmul
  have hle : y / ‖boundaryPath β y‖ ≤ y / β :=
    div_le_div_of_nonneg_left hy.le hβ (le_norm_boundaryPath hβ y)
  have hπ := Real.pi_pos
  have h2 : 2 / π * gapAngle (boundaryPath β y) ≤ y / β := hmul.trans hle
  have e : gapAngle (boundaryPath β y) = π / 2 * (2 / π * gapAngle (boundaryPath β y)) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem tendsto_gapAngle {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun y => gapAngle (boundaryPath β y)) (𝓝[>] 0) (𝓝 0) := by
  have hlin : Tendsto (fun y : ℝ => π / 2 * (y / β)) (𝓝[>] 0) (𝓝 (π / 2 * (0 / β))) :=
    ((continuous_id.div_const β).const_mul (π / 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [zero_div, mul_zero] at hlin
  refine squeeze_zero' ?_ ?_ hlin
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (gapAngle_pos (by rwa [boundaryPath_re])).le
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact gapAngle_le_mul hβ hy

theorem continuous_boundaryPath (β : ℝ) : Continuous (boundaryPath β) := by
  unfold boundaryPath
  fun_prop

theorem tendsto_boundaryPath (β : ℝ) :
    Tendsto (boundaryPath β) (𝓝[>] 0) (𝓝 ((β : ℂ) * I)) := by
  have h := (continuous_boundaryPath β).continuousAt.tendsto (x := (0 : ℝ))
  simp only [boundaryPath, Complex.ofReal_zero, zero_add] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_norm_boundaryPath (β : ℝ) {hβ : 0 < β} :
    Tendsto (fun y => ‖boundaryPath β y‖) (𝓝[>] 0) (𝓝 β) := by
  have h := (tendsto_boundaryPath β).norm
  simpa [abs_of_pos hβ] using h

/-- `y/ε → β`. -/
theorem tendsto_div_gapAngle {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun y => y / gapAngle (boundaryPath β y)) (𝓝[>] 0) (𝓝 β) := by
  have hs : Tendsto (fun y => Real.sinc (gapAngle (boundaryPath β y))) (𝓝[>] 0) (𝓝 1) := by
    have h := Real.continuous_sinc.continuousAt.tendsto.comp (tendsto_gapAngle hβ)
    simpa [Function.comp_def, Real.sinc_zero] using h
  have hmul := (tendsto_norm_boundaryPath β (hβ := hβ)).mul hs
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : (0 : ℝ) < y := hy
  have hz := boundaryPath_ne_zero hβ y
  have hgap := gapAngle_pos (z := boundaryPath β y) (by rwa [boundaryPath_re])
  have hsin := sin_gapAngle hz
  rw [boundaryPath_re] at hsin
  have hn : ‖boundaryPath β y‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [Real.sinc_of_ne_zero hgap.ne', hsin]
  field_simp

/-! ### The Abelian limit in the variable `y` -/

section Limits

variable {r : ℝ → ℂ} {c : ℂ} {R : ℝ}

theorem tendsto_cpow_abelExponent_zero (ϑ : ℝ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent ϑ) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_id.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (norm_ofReal_cpow_abelExponent hy ϑ).le

/-- The resonant Abelian limit along the path. -/
theorem tendsto_path_resonant (hr : AEStronglyMeasurable r (volume.restrict (Ioi 0)))
    (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (hlim : Tendsto r atTop (𝓝 c)) (ϑ : ℝ) {β : ℝ} (hβ : 0 < β)
    {τ : ℝ → ℝ} (hτ : Tendsto (fun y => τ y / gapAngle (boundaryPath β y)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent ϑ * abelIntegral r ϑ
      ((gapAngle (boundaryPath β y) : ℂ) + (τ y : ℂ) * I)) (𝓝[>] 0)
      (𝓝 ((β : ℂ) ^ abelExponent ϑ * (c * Complex.Gamma (abelExponent ϑ)))) := by
  have hpos : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < gapAngle (boundaryPath β y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact gapAngle_pos (by rwa [boundaryPath_re])
  have hres := tendsto_abelIntegral_resonant hr hb hlim ϑ hpos (tendsto_gapAngle hβ) hτ
  have hslit : (β : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hβ)
  have hratio : Tendsto (fun y : ℝ => (((y / gapAngle (boundaryPath β y) : ℝ) : ℂ)) ^
      abelExponent ϑ) (𝓝[>] 0) (𝓝 ((β : ℂ) ^ abelExponent ϑ)) :=
    (continuousAt_cpow_const hslit).tendsto.comp
      ((Complex.continuous_ofReal.tendsto β).comp (tendsto_div_gapAngle hβ))
  refine (hratio.mul hres).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hpos] with y hy hgap
  have hy0 : (0 : ℝ) < y := hy
  have hsplit : (y : ℂ) = ((y / gapAngle (boundaryPath β y) : ℝ) : ℂ) *
      (gapAngle (boundaryPath β y) : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hgap.ne']
  conv_rhs => rw [hsplit]
  rw [ofReal_mul_cpow (div_pos hy0 hgap) (Complex.ofReal_ne_zero.mpr hgap.ne')]
  ring

/-- The non-resonant Abelian limit along the path. -/
theorem tendsto_path_off (hr : AEStronglyMeasurable r (volume.restrict (Ioi 0)))
    (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (hlim : Tendsto r atTop (𝓝 c)) (ϑ : ℝ) {β : ℝ} (hβ : 0 < β)
    {τ : ℝ → ℝ} {τ₀ : ℝ} (hτ : Tendsto τ (𝓝[>] 0) (𝓝 τ₀)) (hτ₀ : τ₀ ≠ 0) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ abelExponent ϑ * abelIntegral r ϑ
      ((gapAngle (boundaryPath β y) : ℂ) + (τ y : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < gapAngle (boundaryPath β y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact gapAngle_pos (by rwa [boundaryPath_re])
  have hoff := tendsto_abelIntegral_off hr hb hlim ϑ hpos (tendsto_gapAngle hβ) hτ hτ₀
  have hprod := (tendsto_div_gapAngle hβ).mul hoff
  rw [mul_zero] at hprod
  refine squeeze_zero_norm' ?_ hprod
  filter_upwards [self_mem_nhdsWithin, hpos] with y hy hgap
  have hy0 : (0 : ℝ) < y := hy
  rw [norm_mul, norm_ofReal_cpow_abelExponent hy0]
  apply le_of_eq
  field_simp

/-- A uniform bound for the normalized transform along the path. -/
theorem norm_path_le (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (hR : 0 ≤ R) (ϑ : ℝ) {β y : ℝ} (hβ : 0 < β)
    (hy : 0 < y) (hy1 : y < 1) (τ : ℝ) :
    ‖(y : ℂ) ^ abelExponent ϑ * abelIntegral r ϑ
      ((gapAngle (boundaryPath β y) : ℂ) + (τ : ℂ) * I)‖ ≤ R * (1 + β) := by
  have hgap := gapAngle_pos (z := boundaryPath β y) (by rwa [boundaryPath_re])
  have hw : 0 < ((gapAngle (boundaryPath β y) : ℂ) + (τ : ℂ) * I).re := by simpa using hgap
  have h := norm_abelIntegral_le hb ϑ hw
  have hre : ((gapAngle (boundaryPath β y) : ℂ) + (τ : ℂ) * I).re = gapAngle (boundaryPath β y) := by
    simp
  rw [hre] at h
  rw [norm_mul, norm_ofReal_cpow_abelExponent hy]
  have hq := (div_gapAngle_le hβ hy).trans (norm_boundaryPath_le hβ hy)
  calc y * ‖abelIntegral r ϑ _‖ ≤ y * (R / gapAngle (boundaryPath β y)) :=
        mul_le_mul_of_nonneg_left h hy.le
    _ = R * (y / gapAngle (boundaryPath β y)) := by ring
    _ ≤ R * (1 + β) := mul_le_mul_of_nonneg_left (by linarith) hR

end Limits

end GaloisForLFunctions.SelbergClass.DegreeOne
