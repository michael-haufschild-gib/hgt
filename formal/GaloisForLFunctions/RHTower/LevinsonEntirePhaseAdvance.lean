import GaloisForLFunctions.RHTower.LevinsonPhaseAdvance
import GaloisForLFunctions.RHTower.LevinsonEntireDetector

/-!
# The phase advance of the detector in entire form

Passing from `G` to the entire multiple `G♯ = (s-1)^2 G` changes the logarithmic derivative on the
critical line by `Re[2/(-½+iτ)] = -(¼+τ²)^{-1} ≤ 0`.  The correction therefore only helps: the phase
advance of Hardy's `Z` is bounded below by the archimedean increment plus the argument variation of
the *entire* detector,

```text
θ(T₂) - θ(T₁) + ∫_{T₁}^{T₂} Re (G♯'/G♯)(½+it) dt  ≤  ψ(T₂) - ψ(T₁),
```

which is the form the rectangle argument principle bounds.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

theorem linePt_sub_one_re (τ : ℝ) : (linePt τ - 1).re = -(1 / 2) := by
  rw [Complex.sub_re, linePt_re, Complex.one_re]; norm_num

theorem linePt_sub_one_im (τ : ℝ) : (linePt τ - 1).im = τ := by
  rw [Complex.sub_im, linePt_im, Complex.one_im]; ring

theorem re_two_div_linePt_sub_one (τ : ℝ) :
    ((2 : ℂ) / (linePt τ - 1)).re = -(1 / (1 / 4 + τ ^ 2)) := by
  have hns : Complex.normSq (linePt τ - 1) = 1 / 4 + τ ^ 2 := by
    rw [Complex.normSq_apply, linePt_sub_one_re, linePt_sub_one_im]; ring
  rw [Complex.div_re, hns, linePt_sub_one_re, linePt_sub_one_im]
  simp only [Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem linePt_ne_one (τ : ℝ) : linePt τ ≠ 1 := linePt_ne_one' τ

/-- On the critical line the logarithmic derivative of `G` exceeds that of its entire multiple by
the positive quantity `(¼+τ²)^{-1}`. -/
theorem re_logDeriv_levinsonG_line (lam : ℂ) {τ : ℝ}
    (hG : levinsonG lam (linePt τ) ≠ 0) :
    (logDeriv (levinsonG lam) (linePt τ)).re
      = (logDeriv (levinsonGEntire lam) (linePt τ)).re + 1 / (1 / 4 + τ ^ 2) := by
  rw [logDeriv_levinsonGEntire lam (linePt_ne_one τ) hG, Complex.add_re,
    re_two_div_linePt_sub_one]
  ring

theorem levinsonGEntire_line_ne_zero {lam : ℂ} {τ : ℝ}
    (hG : levinsonG lam (linePt τ) ≠ 0) :
    levinsonGEntire lam (linePt τ) ≠ 0 := by
  rw [Ne, levinsonGEntire_eq_zero_iff lam (linePt_ne_one τ)]
  exact hG

theorem continuousOn_re_logDeriv_levinsonGEntire_line (lam : ℂ) {S : Set ℝ}
    (hne : ∀ τ ∈ S, levinsonG lam (linePt τ) ≠ 0) :
    ContinuousOn (fun τ : ℝ => (logDeriv (levinsonGEntire lam) (linePt τ)).re) S := by
  have hnum : Continuous fun τ : ℝ => deriv (levinsonGEntire lam) (linePt τ) :=
    continuous_iff_continuousAt.mpr fun τ =>
      (((analyticOnNhd_levinsonGEntire lam).deriv _
        (Set.mem_univ _)).continuousAt).comp continuous_linePt'.continuousAt
  have hden : Continuous fun τ : ℝ => levinsonGEntire lam (linePt τ) :=
    (differentiable_levinsonGEntire lam).continuous.comp continuous_linePt'
  have hdiv : ContinuousOn (fun τ : ℝ =>
      deriv (levinsonGEntire lam) (linePt τ) / levinsonGEntire lam (linePt τ)) S :=
    ContinuousOn.div hnum.continuousOn hden.continuousOn
      (fun τ hτ => levinsonGEntire_line_ne_zero (hne τ hτ))
  exact Complex.continuous_re.comp_continuousOn hdiv

/-- **Lower bound for the detector phase advance.**  On a window above height `20` where `G` does
not vanish, Hardy's `Z` has a polar form whose phase advance is at least the archimedean increment
plus the argument variation of the entire detector. -/
theorem exists_polar_hardyZ_advance_entire_le {lam : ℝ} (hlam : lam ≤ 0)
    {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ ≤ T₂)
    (hne : ∀ τ ∈ Icc T₁ T₂, levinsonG (lam : ℂ) (linePt τ) ≠ 0) :
    ∃ ρ ψ : ℝ → ℝ, ContinuousOn ψ (Icc T₁ T₂) ∧ (∀ τ ∈ Icc T₁ T₂, 0 < ρ τ) ∧
      (∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ)) ∧
      (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ τ in T₁..T₂, (logDeriv (levinsonGEntire (lam : ℂ)) (linePt τ)).re)
        ≤ ψ T₂ - ψ T₁ := by
  obtain ⟨ρ, ψ, hψc, hρ, hpolar, hadv⟩ :=
    exists_polar_hardyZ_advance_of_levinsonG_ne_zero hlam h20 hT hne
  refine ⟨ρ, ψ, hψc, hρ, hpolar, ?_⟩
  have huIcc : uIcc T₁ T₂ = Icc T₁ T₂ := uIcc_of_le hT
  have hEcont : ContinuousOn
      (fun τ : ℝ => (logDeriv (levinsonGEntire ((lam : ℝ) : ℂ)) (linePt τ)).re)
      (uIcc T₁ T₂) := by
    rw [huIcc]
    exact continuousOn_re_logDeriv_levinsonGEntire_line _ hne
  have hEint : IntervalIntegrable
      (fun τ : ℝ => (logDeriv (levinsonGEntire ((lam : ℝ) : ℂ)) (linePt τ)).re)
      volume T₁ T₂ := hEcont.intervalIntegrable
  have hCint : IntervalIntegrable (fun τ : ℝ => 1 / (1 / 4 + τ ^ 2)) volume T₁ T₂ := by
    refine Continuous.intervalIntegrable ?_ _ _
    have : ∀ τ : ℝ, (1 : ℝ) / 4 + τ ^ 2 ≠ 0 := fun τ => by positivity
    fun_prop (disch := intro τ; positivity)
  have hsplit : ∀ τ ∈ uIcc T₁ T₂,
      (deriv (levinsonG ((lam : ℝ) : ℂ)) (linePt τ)
          / levinsonG ((lam : ℝ) : ℂ) (linePt τ)).re
        = (logDeriv (levinsonGEntire ((lam : ℝ) : ℂ)) (linePt τ)).re
          + 1 / (1 / 4 + τ ^ 2) := by
    intro τ hτ
    rw [huIcc] at hτ
    have := re_logDeriv_levinsonG_line ((lam : ℝ) : ℂ) (hne τ hτ)
    rw [logDeriv_apply] at this
    exact this
  rw [hadv, intervalIntegral.integral_congr hsplit,
    intervalIntegral.integral_add hEint hCint]
  have hpos : (0 : ℝ) ≤ ∫ τ in T₁..T₂, 1 / (1 / 4 + τ ^ 2) :=
    intervalIntegral.integral_nonneg hT (fun τ _ => by positivity)
  linarith

end RHTower

end
