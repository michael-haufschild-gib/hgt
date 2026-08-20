import GaloisForLFunctions.RHTower.LevinsonDetectorPolar
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# The phase advance of Levinson's detector

The polar phase of `e^{iθ}·G` along the critical segment has an explicit primitive: its derivative
is the imaginary part of the logarithmic derivative of `e^{iθ(τ)}·G(½+iτ)`, and that logarithmic
derivative is `i·(θ'(τ) + (G'/G)(½+iτ))`.  Hence

```text
ψ(T₂) - ψ(T₁) = (θ(T₂) - θ(T₁)) + ∫_{T₁}^{T₂} Re[(G'/G)(½+iτ)] dτ,
```

the second term being exactly the variation of the argument of `G` along the segment.  The
archimedean term is the main term — of size `½(T₂-T₁)·log T` — so a bound on the argument variation
of `G` converts directly into a lower bound for the number of sign changes of `Z`, and therefore
into a lower bound for the number of odd-order critical ordinates.
-/

open Complex Set MeasureTheory


noncomputable section

namespace RHTower

/-- **The Riemann--Siegel phase is the primitive of its velocity.** -/
theorem integral_gammaHardyPhaseRate (a b : ℝ) :
    ∫ τ in a..b, gammaHardyPhaseRate τ = gammaHardyTheta b - gammaHardyTheta a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_gammaHardyTheta x)
    (continuous_gammaHardyPhaseRate.intervalIntegrable a b)

/-- The logarithmic derivative of the detector carrier `e^{iθ}·G(½+i·)` is
`i·(θ' + (G'/G)(½+i·))`. -/
theorem detector_logDeriv_eq {lam : ℝ} {τ : ℝ}
    (hne : levinsonG (lam : ℂ) (linePt τ) ≠ 0) :
    (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * (I * (gammaHardyPhaseRate τ : ℂ))
          * levinsonG (lam : ℂ) (linePt τ)
        + Complex.exp (I * (gammaHardyTheta τ : ℂ))
          * (deriv (levinsonG (lam : ℂ)) (linePt τ) * I))
      / (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * levinsonG (lam : ℂ) (linePt τ))
      = I * ((gammaHardyPhaseRate τ : ℂ)
          + deriv (levinsonG (lam : ℂ)) (linePt τ) / levinsonG (lam : ℂ) (linePt τ)) := by
  have hexp : Complex.exp (I * (gammaHardyTheta τ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  try ring

/-- The imaginary part of that logarithmic derivative — the phase velocity of the detector. -/
theorem im_detector_logDeriv_eq {lam : ℝ} {τ : ℝ}
    (hne : levinsonG (lam : ℂ) (linePt τ) ≠ 0) :
    ((Complex.exp (I * (gammaHardyTheta τ : ℂ)) * (I * (gammaHardyPhaseRate τ : ℂ))
          * levinsonG (lam : ℂ) (linePt τ)
        + Complex.exp (I * (gammaHardyTheta τ : ℂ))
          * (deriv (levinsonG (lam : ℂ)) (linePt τ) * I))
      / (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * levinsonG (lam : ℂ) (linePt τ))).im
      = gammaHardyPhaseRate τ
        + (deriv (levinsonG (lam : ℂ)) (linePt τ) / levinsonG (lam : ℂ) (linePt τ)).re := by
  rw [detector_logDeriv_eq hne]
  simp [Complex.mul_im]

/-- **The phase advance of Levinson's detector.**  On a window above height `20` where `G` does not
vanish, Hardy's `Z` has a polar form whose phase advances by the archimedean phase increment plus
the argument variation of `G` along the segment. -/
theorem exists_polar_hardyZ_advance_of_levinsonG_ne_zero {lam : ℝ} (hlam : lam ≤ 0)
    {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ ≤ T₂)
    (hne : ∀ τ ∈ Icc T₁ T₂, levinsonG (lam : ℂ) (linePt τ) ≠ 0) :
    ∃ ρ ψ : ℝ → ℝ, ContinuousOn ψ (Icc T₁ T₂) ∧ (∀ τ ∈ Icc T₁ T₂, 0 < ρ τ) ∧
      (∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ)) ∧
      ψ T₂ - ψ T₁ = (gammaHardyTheta T₂ - gammaHardyTheta T₁)
        + ∫ τ in T₁..T₂,
            (deriv (levinsonG (lam : ℂ)) (linePt τ) / levinsonG (lam : ℂ) (linePt τ)).re := by
  classical
  set g : ℝ → ℂ := fun τ =>
    Complex.exp (I * (gammaHardyTheta τ : ℂ)) * levinsonG (lam : ℂ) (linePt τ) with hgdef
  set g' : ℝ → ℂ := fun τ =>
    Complex.exp (I * (gammaHardyTheta τ : ℂ)) * (I * (gammaHardyPhaseRate τ : ℂ))
        * levinsonG (lam : ℂ) (linePt τ)
      + Complex.exp (I * (gammaHardyTheta τ : ℂ))
        * (deriv (levinsonG (lam : ℂ)) (linePt τ) * I) with hg'def
  have hgderiv : ∀ τ, HasDerivAt g (g' τ) τ := fun τ => hasDerivAt_detectorPhase lam τ
  have hgne : ∀ τ ∈ Icc T₁ T₂, g τ ≠ 0 := by
    intro τ hτ
    exact mul_ne_zero (Complex.exp_ne_zero _) (hne τ hτ)
  have hexpc : Continuous fun τ : ℝ => Complex.exp (I * (gammaHardyTheta τ : ℂ)) := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_gammaHardyTheta τ).continuousAt)
  have hGc : Continuous fun τ : ℝ => levinsonG (lam : ℂ) (linePt τ) :=
    continuous_iff_continuousAt.mpr fun τ =>
      ((analyticAt_levinsonG (lam : ℂ) (linePt_ne_one' τ)).continuousAt).comp
        continuous_linePt'.continuousAt
  have hG'c : Continuous fun τ : ℝ => deriv (levinsonG (lam : ℂ)) (linePt τ) :=
    continuous_iff_continuousAt.mpr fun τ =>
      (((analyticAt_levinsonG (lam : ℂ) (linePt_ne_one' τ)).deriv).continuousAt).comp
        continuous_linePt'.continuousAt
  have hg'c : Continuous g' := by
    rw [hg'def]
    exact ((hexpc.mul (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_gammaHardyPhaseRate))).mul hGc).add
      (hexpc.mul (hG'c.mul continuous_const))
  have hgc : Continuous g := by
    rw [hgdef]
    exact hexpc.mul hGc
  have hquot : ContinuousOn (fun τ => g' τ / g τ) (Icc T₁ T₂) :=
    ContinuousOn.div hg'c.continuousOn hgc.continuousOn hgne
  obtain ⟨r, ψ, hψc, hrpos, hpolar, hadv⟩ :=
    exists_continuousOn_polar_advance (f := g) (f' := g') hT (fun τ _ => hgderiv τ) hquot hgne
  have hY : ∀ τ ∈ Icc T₁ T₂, (0 : ℝ) < (levinsonY (lam : ℂ) (linePt τ)).re := by
    intro τ hτ
    rw [levinsonY_line_eq, Complex.ofReal_re]
    have hd := log_pi_lt_re_digamma_quarter (le_trans h20 hτ.1)
    nlinarith
  refine ⟨fun τ => 2 * r τ / (levinsonY (lam : ℂ) (linePt τ)).re, ψ, hψc, ?_, ?_, ?_⟩
  · intro τ hτ
    have := hrpos τ hτ
    have := hY τ hτ
    positivity
  · intro τ hτ
    have hYτ := hY τ hτ
    have hid : ((levinsonY (lam : ℂ) (linePt τ)).re * hardyZ τ : ℝ) = 2 * (g τ).re :=
      levinsonY_line_mul_hardyZ lam τ
    rw [hpolar τ hτ] at hid
    field_simp
    linarith [hid]
  · rw [hadv]
    have hsplit : ∀ τ ∈ Set.uIcc T₁ T₂, (g' τ / g τ).im
        = gammaHardyPhaseRate τ
          + (deriv (levinsonG (lam : ℂ)) (linePt τ) / levinsonG (lam : ℂ) (linePt τ)).re := by
      intro τ hτ
      rw [Set.uIcc_of_le hT] at hτ
      exact im_detector_logDeriv_eq (hne τ hτ)
    rw [intervalIntegral.integral_congr hsplit]
    have hint₁ : IntervalIntegrable gammaHardyPhaseRate volume T₁ T₂ :=
      continuous_gammaHardyPhaseRate.intervalIntegrable T₁ T₂
    have hint₂ : IntervalIntegrable
        (fun τ => (deriv (levinsonG (lam : ℂ)) (linePt τ)
          / levinsonG (lam : ℂ) (linePt τ)).re) volume T₁ T₂ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hT]
      exact Complex.continuous_re.comp_continuousOn
        (ContinuousOn.div hG'c.continuousOn hGc.continuousOn hne)
    rw [intervalIntegral.integral_add hint₁ hint₂, integral_gammaHardyPhaseRate]

end RHTower

end
