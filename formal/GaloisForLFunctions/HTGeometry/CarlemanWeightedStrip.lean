import GaloisForLFunctions.HTGeometry.ShiftedDerivativeCoercivity

/-!
# A Carleman estimate on an exponentially weighted line

Conjugating by an exponential weight turns the derivative into a shifted derivative:

`(e^{σt} u)' − σ (e^{σt} u) = e^{σt} u'`.

So the coercivity of the shifted derivative transfers verbatim to the weighted problem and gives

`σ² ∫ e^{2σt} ‖u‖² ≤ ∫ e^{2σt} ‖u'‖²`,

a Carleman estimate with constant `1/σ`: the weighted mass of a profile is controlled by the
weighted mass of its derivative, uniformly in the weight parameter.  No Fourier transform and no
Plancherel theorem enters — the whole content is one integration by parts, already carried by the
shifted-derivative coercivity.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The exponentially weighted profile. -/
noncomputable def carlemanConjugate (σ : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (σ * t) : ℂ) * u t

/-- The weight is differentiable with the expected derivative. -/
theorem hasDerivAt_carlemanWeight (σ t : ℝ) :
    HasDerivAt (fun x : ℝ => ((Real.exp (σ * x) : ℝ) : ℂ))
      ((σ * Real.exp (σ * t) : ℝ) : ℂ) t := by
  have hlin : HasDerivAt (fun x : ℝ => σ * x) σ t := by
    have h := (hasDerivAt_id t).const_mul σ
    simpa using h
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (σ * x)) (Real.exp (σ * t) * σ) t := hlin.exp
  have hval : Real.exp (σ * t) * σ = σ * Real.exp (σ * t) := by ring
  rw [hval] at hexp
  exact hexp.ofReal_comp

/-- **The conjugation identity.**  Differentiating the weighted profile produces the weight times
the shifted derivative plus the shift term. -/
theorem hasDerivAt_carlemanConjugate {σ : ℝ} {u : ℝ → ℂ} (hu : Differentiable ℝ u) (t : ℝ) :
    HasDerivAt (carlemanConjugate σ u)
      (((σ * Real.exp (σ * t) : ℝ) : ℂ) * u t + ((Real.exp (σ * t) : ℝ) : ℂ) * deriv u t) t :=
  (hasDerivAt_carlemanWeight σ t).mul (hu t).hasDerivAt

/-- The conjugated profile is differentiable. -/
theorem differentiable_carlemanConjugate {σ : ℝ} {u : ℝ → ℂ} (hu : Differentiable ℝ u) :
    Differentiable ℝ (carlemanConjugate σ u) := fun t =>
  (hasDerivAt_carlemanConjugate hu t).differentiableAt

/-- The derivative of the conjugated profile, in closed form. -/
theorem deriv_carlemanConjugate {σ : ℝ} {u : ℝ → ℂ} (hu : Differentiable ℝ u) (t : ℝ) :
    deriv (carlemanConjugate σ u) t
      = ((σ * Real.exp (σ * t) : ℝ) : ℂ) * u t + ((Real.exp (σ * t) : ℝ) : ℂ) * deriv u t :=
  (hasDerivAt_carlemanConjugate hu t).deriv

/-- **The shift is exactly cancelled.**  Subtracting `σ` times the conjugated profile leaves the
weight times the plain derivative — this is why the Carleman estimate is the coercivity estimate. -/
theorem deriv_carlemanConjugate_sub {σ : ℝ} {u : ℝ → ℂ} (hu : Differentiable ℝ u) (t : ℝ) :
    deriv (carlemanConjugate σ u) t - (σ : ℂ) * carlemanConjugate σ u t
      = ((Real.exp (σ * t) : ℝ) : ℂ) * deriv u t := by
  rw [deriv_carlemanConjugate hu t]
  unfold carlemanConjugate
  push_cast
  ring

/-- The conjugated profile keeps compact support. -/
theorem hasCompactSupport_carlemanConjugate {σ : ℝ} {u : ℝ → ℂ} (hc : HasCompactSupport u) :
    HasCompactSupport (carlemanConjugate σ u) := by
  refine HasCompactSupport.intro hc fun x hx => ?_
  unfold carlemanConjugate
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- The squared norm of the conjugated profile is the weighted squared norm. -/
theorem normSq_carlemanConjugate (σ : ℝ) (u : ℝ → ℂ) (t : ℝ) :
    ‖carlemanConjugate σ u t‖ ^ (2 : ℕ) = Real.exp (2 * σ * t) * ‖u t‖ ^ (2 : ℕ) := by
  unfold carlemanConjugate
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 2
  ring

/-- **The Carleman estimate on an exponentially weighted line.**  The weighted mass of a compactly
supported `C¹` profile is controlled by the weighted mass of its derivative, with constant `1/σ`
uniform in the weight. -/
theorem carleman_weighted_estimate (σ : ℝ) {u : ℝ → ℂ} (hdiff : Differentiable ℝ u)
    (hcont : Continuous (deriv u)) (hc : HasCompactSupport u) :
    σ ^ (2 : ℕ) * (∫ t, Real.exp (2 * σ * t) * ‖u t‖ ^ (2 : ℕ))
      ≤ ∫ t, Real.exp (2 * σ * t) * ‖deriv u t‖ ^ (2 : ℕ) := by
  have hYdiff : Differentiable ℝ (carlemanConjugate σ u) := differentiable_carlemanConjugate hdiff
  have hYderiv : deriv (carlemanConjugate σ u)
      = fun t => ((σ * Real.exp (σ * t) : ℝ) : ℂ) * u t
        + ((Real.exp (σ * t) : ℝ) : ℂ) * deriv u t := by
    funext t
    exact deriv_carlemanConjugate hdiff t
  have hYcont : Continuous (deriv (carlemanConjugate σ u)) := by
    rw [hYderiv]
    exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul hdiff.continuous).add
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul hcont)
  have hYc : HasCompactSupport (carlemanConjugate σ u) := hasCompactSupport_carlemanConjugate hc
  have hkey := sq_mul_integral_normSq_le σ hYdiff hYcont hYc
  have hL : (∫ t, ‖carlemanConjugate σ u t‖ ^ (2 : ℕ))
      = ∫ t, Real.exp (2 * σ * t) * ‖u t‖ ^ (2 : ℕ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => normSq_carlemanConjugate σ u t)
  have hR : (∫ t, ‖deriv (carlemanConjugate σ u) t - (σ : ℂ) * carlemanConjugate σ u t‖ ^ (2 : ℕ))
      = ∫ t, Real.exp (2 * σ * t) * ‖deriv u t‖ ^ (2 : ℕ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ‖deriv (carlemanConjugate σ u) t - (σ : ℂ) * carlemanConjugate σ u t‖ ^ (2 : ℕ)
      = Real.exp (2 * σ * t) * ‖deriv u t‖ ^ (2 : ℕ)
    rw [deriv_carlemanConjugate_sub hdiff t, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hL, hR] at hkey
  exact hkey

end GaloisForLFunctions.HTGeometry
