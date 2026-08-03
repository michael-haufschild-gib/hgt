import Mathlib.Analysis.Calculus.SmoothSeries
import GaloisForLFunctions.HTGeometry.ClockStripCauchyScale

/-!
# Differentiating a series of holomorphic functions on a strip

The sum of the clock iterates has to be differentiated twice in the transverse variable, term by
term. mathlib's term-by-term differentiation asks for a summable bound on the derivatives; on a
strip that bound is Cauchy's estimate, which converts a summable bound on the functions themselves
into one on the derivatives at the cost of a slightly smaller strip.

Since the strip is convex, hence preconnected, the localised form of the theorem applies, and no
global hypothesis on the plane is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

theorem convex_imStrip (ρ : ℝ) : Convex ℝ (imStrip ρ) := by
  have hEq : imStrip ρ = Complex.imLm ⁻¹' Set.Ioo (-ρ) ρ := by
    ext z
    constructor
    · intro hz
      exact Set.mem_Ioo.mpr (abs_lt.mp (mem_imStrip.mp hz))
    · intro hz
      exact mem_imStrip.mpr (abs_lt.mpr (Set.mem_Ioo.mp hz))
  rw [hEq]
  exact (convex_Ioo (-ρ) ρ).linear_preimage Complex.imLm

theorem isPreconnected_imStrip (ρ : ℝ) : IsPreconnected (imStrip ρ) :=
  (convex_imStrip ρ).isPreconnected

/-- **A series of holomorphic functions with summable sup-bounds may be differentiated term by
term.** -/
theorem hasDerivAt_tsum_of_holomorphic {ρ₁ ρ' : ℝ} (hρ : ρ₁ < ρ')
    {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, DifferentiableOn ℂ (f m) (imStrip ρ'))
    (hM : ∀ m, ∀ w ∈ imStrip ρ', ‖f m w‖ ≤ M m) (hMs : Summable M)
    {z : ℂ} (hz : z ∈ imStrip ρ₁) :
    HasDerivAt (fun w => ∑' m, f m w) (∑' m, deriv (f m) z) z := by
  have hgap : (0 : ℝ) < ρ' - ρ₁ := by linarith
  have hu : Summable fun m : ℕ => 2 * M m / (ρ' - ρ₁) := by
    simpa [mul_div_assoc] using (hMs.mul_left 2).div_const (ρ' - ρ₁)
  have hsub : imStrip ρ₁ ⊆ imStrip ρ' := imStrip_mono hρ.le
  have hderiv : ∀ (m : ℕ), ∀ y ∈ imStrip ρ₁, HasDerivAt (f m) (deriv (f m) y) y := by
    intro m y hy
    exact ((hf m).differentiableAt ((isOpen_imStrip ρ').mem_nhds (hsub hy))).hasDerivAt
  have hbound : ∀ (m : ℕ), ∀ y ∈ imStrip ρ₁, ‖deriv (f m) y‖ ≤ 2 * M m / (ρ' - ρ₁) := by
    intro m y hy
    exact norm_deriv_le_on_imStrip hρ (hf m) (hM m) (le_of_lt (mem_imStrip.mp hy))
  have hg0 : Summable fun m : ℕ => f m z := by
    refine Summable.of_norm_bounded hMs fun m => ?_
    exact hM m z (hsub hz)
  exact hasDerivAt_tsum_of_isPreconnected hu (isOpen_imStrip ρ₁) (isPreconnected_imStrip ρ₁)
    hderiv hbound hz hg0 hz

/-- The sum of a series of holomorphic functions is holomorphic. -/
theorem differentiableOn_tsum_of_holomorphic {ρ₁ ρ' : ℝ} (hρ : ρ₁ < ρ')
    {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, DifferentiableOn ℂ (f m) (imStrip ρ'))
    (hM : ∀ m, ∀ w ∈ imStrip ρ', ‖f m w‖ ≤ M m) (hMs : Summable M) :
    DifferentiableOn ℂ (fun w => ∑' m, f m w) (imStrip ρ₁) :=
  fun _ hz => (hasDerivAt_tsum_of_holomorphic hρ hf hM hMs hz).differentiableAt
    |>.differentiableWithinAt

/-- The derivative of the sum is the sum of the derivatives, as functions on the smaller strip. -/
theorem deriv_tsum_of_holomorphic {ρ₁ ρ' : ℝ} (hρ : ρ₁ < ρ')
    {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, DifferentiableOn ℂ (f m) (imStrip ρ'))
    (hM : ∀ m, ∀ w ∈ imStrip ρ', ‖f m w‖ ≤ M m) (hMs : Summable M)
    {z : ℂ} (hz : z ∈ imStrip ρ₁) :
    deriv (fun w => ∑' m, f m w) z = ∑' m, deriv (f m) z :=
  (hasDerivAt_tsum_of_holomorphic hρ hf hM hMs hz).deriv

/-! ## The second derivative

Iterating the previous statement on the family of first derivatives, which is again holomorphic and
carries the summable bound supplied by Cauchy's estimate.
-/

theorem differentiableOn_deriv_of_holomorphic {ρ₁ ρ' : ℝ} (hρ : ρ₁ < ρ')
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (imStrip ρ')) :
    DifferentiableOn ℂ (deriv g) (imStrip ρ₁) :=
  (((hg.analyticOnNhd (isOpen_imStrip ρ')).deriv_of_isOpen (isOpen_imStrip ρ')).mono
    (imStrip_mono hρ.le)).differentiableOn

/-- **The second derivative of the sum is the sum of the second derivatives.** -/
theorem deriv_deriv_tsum_of_holomorphic {ρ₂ ρ₁ ρ' : ℝ} (h21 : ρ₂ < ρ₁) (h1ρ : ρ₁ < ρ')
    {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, DifferentiableOn ℂ (f m) (imStrip ρ'))
    (hM : ∀ m, ∀ w ∈ imStrip ρ', ‖f m w‖ ≤ M m) (hMs : Summable M)
    {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    deriv (deriv (fun w => ∑' m, f m w)) z = ∑' m, deriv (deriv (f m)) z := by
  have hgap : (0 : ℝ) < ρ' - ρ₁ := by linarith
  have hz1 : z ∈ imStrip ρ₁ := imStrip_mono h21.le hz
  -- the derivative of the sum agrees with the sum of the derivatives near `z`
  have hEq : deriv (fun w => ∑' m, f m w) =ᶠ[nhds z] fun w => ∑' m, deriv (f m) w := by
    refine Filter.eventuallyEq_of_mem ((isOpen_imStrip ρ₁).mem_nhds hz1) fun w hw => ?_
    exact deriv_tsum_of_holomorphic h1ρ hf hM hMs hw
  rw [hEq.deriv_eq]
  -- the family of derivatives is holomorphic on the middle strip, with summable bounds
  have hfd : ∀ m, DifferentiableOn ℂ (deriv (f m)) (imStrip ρ₁) := fun m =>
    differentiableOn_deriv_of_holomorphic h1ρ (hf m)
  have hMd : ∀ m, ∀ w ∈ imStrip ρ₁, ‖deriv (f m) w‖ ≤ 2 * M m / (ρ' - ρ₁) := by
    intro m w hw
    exact norm_deriv_le_on_imStrip h1ρ (hf m) (hM m) (le_of_lt (mem_imStrip.mp hw))
  have hMds : Summable fun m : ℕ => 2 * M m / (ρ' - ρ₁) := by
    simpa [mul_div_assoc] using (hMs.mul_left 2).div_const (ρ' - ρ₁)
  exact deriv_tsum_of_holomorphic h21 hfd hMd hMds hz

end GaloisForLFunctions.HTGeometry
