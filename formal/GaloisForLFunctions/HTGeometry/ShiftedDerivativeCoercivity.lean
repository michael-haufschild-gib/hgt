import Mathlib

/-!
# The shifted derivative is coercive

For a compactly supported `C¹` function the cross term in

`‖Y' − σ Y‖² = ‖Y'‖² − 2σ ∫ Re(Y' conj Y) + σ² ‖Y‖²`

vanishes, because `2 Re(Y' conj Y)` is the derivative of `‖Y‖²` and that derivative integrates to
zero over the line.  Hence

`‖Y' − σ Y‖₂² = ‖Y'‖₂² + σ² ‖Y‖₂²  ≥  σ² ‖Y‖₂²`,

which is the resolvent estimate `σ ‖Y‖₂ ≤ ‖(∂ − σ)Y‖₂` with no Fourier transform and no Plancherel
theorem: one integration by parts does it.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- The derivative of the squared modulus along a differentiable path. -/
theorem hasDerivAt_normSq_comp {Y : ℝ → ℂ} {Y' : ℂ} {x : ℝ} (hY : HasDerivAt Y Y' x) :
    HasDerivAt (fun t => ‖Y t‖ ^ (2 : ℕ)) (2 * (Y' * (starRingEnd ℂ) (Y x)).re) x := by
  have hre : HasDerivAt (fun t => (Y t).re) Y'.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hY
  have him : HasDerivAt (fun t => (Y t).im) Y'.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hY
  have h1 : HasDerivAt (fun t => (Y t).re * (Y t).re)
      (Y'.re * (Y x).re + (Y x).re * Y'.re) x := hre.mul hre
  have h2 : HasDerivAt (fun t => (Y t).im * (Y t).im)
      (Y'.im * (Y x).im + (Y x).im * Y'.im) x := him.mul him
  have hsum := h1.add h2
  have hnorm : (fun t => ‖Y t‖ ^ (2 : ℕ)) =
      fun t => (Y t).re * (Y t).re + (Y t).im * (Y t).im := by
    funext t
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hsum' : HasDerivAt (fun t => (Y t).re * (Y t).re + (Y t).im * (Y t).im)
      (Y'.re * (Y x).re + (Y x).re * Y'.re + (Y'.im * (Y x).im + (Y x).im * Y'.im)) x := hsum
  have hval : 2 * (Y' * (starRingEnd ℂ) (Y x)).re =
      Y'.re * (Y x).re + (Y x).re * Y'.re + (Y'.im * (Y x).im + (Y x).im * Y'.im) := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hnorm, hval]
  exact hsum'

/-! ## The coercivity estimate -/

/-- The pointwise expansion of the shifted derivative. -/
theorem normSq_shifted (σ : ℝ) (a b : ℂ) :
    ‖a - (σ : ℂ) * b‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) - σ * (2 * (a * (starRingEnd ℂ) b).re) + σ ^ (2 : ℕ) * ‖b‖ ^ (2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The cross term integrates to zero.**  For a compactly supported differentiable path the
derivative of the squared modulus has vanishing total integral. -/
theorem integral_cross_eq_zero {Y : ℝ → ℂ} (hdiff : Differentiable ℝ Y)
    (hcont : Continuous (deriv Y)) (hc : HasCompactSupport Y) :
    (∫ x, 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re) = 0 := by
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall 0
  set R : ℝ := |R₀| + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hout : ∀ x : ℝ, |R₀| < |x| → Y x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have hmem' := hR₀ hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem'
    exact absurd (hmem'.trans (le_abs_self R₀)) (not_le.mpr hx)
  have hzeroOut : ∀ x ∉ Set.Icc (-R) R, 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re = 0 := by
    intro x hx
    have habs : R < |x| := by
      rcases lt_or_ge x 0 with hneg | hpos
      · rw [abs_of_neg hneg]
        by_contra hcon
        exact hx ⟨by linarith [not_lt.mp hcon], by linarith⟩
      · rw [abs_of_nonneg hpos]
        by_contra hcon
        exact hx ⟨by linarith, not_lt.mp hcon⟩
    rw [hout x (by linarith [habs])]
    simp
  have hbridge : (∫ x, 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re) =
      ∫ x in (-R)..R, 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re := by
    rw [intervalIntegral.integral_of_le (by linarith : (-R : ℝ) ≤ R),
      ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Icc (-R) R) hzeroOut]
    exact (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc).symm
  rw [hbridge]
  have hderiv : ∀ x ∈ Set.uIcc (-R) R,
      HasDerivAt (fun t => ‖Y t‖ ^ (2 : ℕ)) (2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re) x :=
    fun x _ => hasDerivAt_normSq_comp (hdiff x).hasDerivAt
  have hint : IntervalIntegrable
      (fun x => 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re) MeasureTheory.volume (-R) R := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (Complex.continuous_re.comp (hcont.mul (Complex.continuous_conj.comp hdiff.continuous)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hplus : Y R = 0 := hout R (by rw [abs_of_pos hRpos]; linarith [abs_nonneg R₀])
  have hminus : Y (-R) = 0 := hout (-R) (by rw [abs_neg, abs_of_pos hRpos]; linarith [abs_nonneg R₀])
  rw [hplus, hminus]
  simp

/-- **Coercivity of the shifted derivative.**  For a compactly supported differentiable path,
`sigma^(2 : ℕ) ‖Y‖² ≤ ‖Y' − sigma Y‖²` in `L²`, by one integration by parts.  No Fourier transform and
no Plancherel theorem enters. -/
theorem sq_mul_integral_normSq_le (σ : ℝ) {Y : ℝ → ℂ} (hdiff : Differentiable ℝ Y)
    (hcont : Continuous (deriv Y)) (hc : HasCompactSupport Y) :
    σ ^ (2 : ℕ) * (∫ x, ‖Y x‖ ^ (2 : ℕ)) ≤ ∫ x, ‖deriv Y x - (σ : ℂ) * Y x‖ ^ (2 : ℕ) := by
  have hcY : Continuous Y := hdiff.continuous
  have hcd : HasCompactSupport (deriv Y) := hc.deriv
  have hsY : HasCompactSupport fun x => ‖Y x‖ ^ (2 : ℕ) :=
    HasCompactSupport.intro hc fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx]; simp
  have hsD : HasCompactSupport fun x => ‖deriv Y x‖ ^ (2 : ℕ) :=
    HasCompactSupport.intro hcd fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx]; simp
  have iY : MeasureTheory.Integrable fun x => ‖Y x‖ ^ (2 : ℕ) :=
    (hcY.norm.pow 2).integrable_of_hasCompactSupport hsY
  have iD : MeasureTheory.Integrable fun x => ‖deriv Y x‖ ^ (2 : ℕ) :=
    (hcont.norm.pow 2).integrable_of_hasCompactSupport hsD
  have hcross : Continuous fun x => 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re :=
    continuous_const.mul
      (Complex.continuous_re.comp (hcont.mul (Complex.continuous_conj.comp hcY)))
  have iC : MeasureTheory.Integrable fun x => 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re := by
    refine hcross.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hc fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  have hpoint : ∀ x, ‖deriv Y x - (σ : ℂ) * Y x‖ ^ (2 : ℕ) =
      ‖deriv Y x‖ ^ (2 : ℕ) - σ * (2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re) + σ ^ (2 : ℕ) * ‖Y x‖ ^ (2 : ℕ) :=
    fun x => normSq_shifted σ _ _
  have hsplit : (∫ x, ‖deriv Y x - (σ : ℂ) * Y x‖ ^ (2 : ℕ)) =
      (∫ x, ‖deriv Y x‖ ^ (2 : ℕ)) - σ * (∫ x, 2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re) +
        σ ^ (2 : ℕ) * ∫ x, ‖Y x‖ ^ (2 : ℕ) := by
    have e1 : MeasureTheory.Integrable
        (fun x => ‖deriv Y x‖ ^ (2 : ℕ) - σ * (2 * (deriv Y x * (starRingEnd ℂ) (Y x)).re)) :=
      iD.sub (iC.const_mul σ)
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub iD (iC.const_mul σ),
      ← MeasureTheory.integral_add e1 (iY.const_mul (σ ^ (2 : ℕ)))]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => hpoint x)
  rw [hsplit, integral_cross_eq_zero hdiff hcont hc]
  have hDnn : 0 ≤ ∫ x, ‖deriv Y x‖ ^ (2 : ℕ) :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  linarith

/-- **The resolvent estimate in norm form.**  Taking square roots turns the coercivity into the
shape the flux system consumes: `|σ| ‖Y‖₂ ≤ ‖Y' − σY‖₂`. -/
theorem abs_mul_sqrt_integral_normSq_le (σ : ℝ) {Y : ℝ → ℂ} (hdiff : Differentiable ℝ Y)
    (hcont : Continuous (deriv Y)) (hc : HasCompactSupport Y) :
    |σ| * Real.sqrt (∫ x, ‖Y x‖ ^ (2 : ℕ)) ≤ Real.sqrt (∫ x, ‖deriv Y x - (σ : ℂ) * Y x‖ ^ (2 : ℕ)) := by
  have hsq := sq_mul_integral_normSq_le σ hdiff hcont hc
  have hAnn : 0 ≤ ∫ x, ‖Y x‖ ^ (2 : ℕ) :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hstep : Real.sqrt (σ ^ (2 : ℕ) * ∫ x, ‖Y x‖ ^ (2 : ℕ)) ≤
      Real.sqrt (∫ x, ‖deriv Y x - (σ : ℂ) * Y x‖ ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq_eq_abs] at hstep

end GaloisForLFunctions.HTGeometry
