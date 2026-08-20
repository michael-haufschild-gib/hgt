import GaloisForLFunctions.RHTower.CompletedLinePolar
import GaloisForLFunctions.HTGeometry.SegmentPolarForm

/-!
# The polar representation of Hardy's `Z` produced by Levinson's detector

Combining the detector identity `Y·Λ = 2·Re[Γ_ℝ·G]` with the polar identities
`Γ_ℝ(½+iτ) = ‖Γ_ℝ(½+iτ)‖·exp(iθ(τ))` and `Λ(½+iτ) = ‖Γ_ℝ(½+iτ)‖·Z(τ)`, the archimedean modulus
cancels and leaves

```text
Y(½+iτ)·Z(τ) = 2·Re[ exp(iθ(τ))·G(½+iτ) ].
```

On a window above height `20` where `G` does not vanish, the right-hand side has a continuous polar
form, so `Z = ρ·cos ψ` with `ρ = 2r/Y > 0` and `ψ` continuous — the phase being the archimedean
phase `θ` plus the phase of `G`.  This is exactly the input
`PhaseAdvanceToSingletonFibre.xiSingletonFiberCount_ge_of_phase_advance` consumes.
-/

open Complex Set


noncomputable section

namespace RHTower

/-- **The detector identity in Hardy-`Z` form.**  `Y(τ)·Z(τ) = 2·Re[e^{iθ(τ)}·G(½+iτ)]`. -/
theorem levinsonY_line_mul_hardyZ (lam : ℝ) (τ : ℝ) :
    ((levinsonY (lam : ℂ) (linePt τ)).re * hardyZ τ : ℝ)
      = 2 * (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * levinsonG (lam : ℂ) (linePt τ)).re := by
  have hnorm : (0 : ℝ) < ‖Complex.Gammaℝ (linePt τ)‖ :=
    norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ))
  have hkey := levinsonY_mul_completed_line lam τ
  rw [completedRiemannZeta_line_eq_norm_mul_hardyZ, levinsonY_line_eq] at hkey
  have hgam := Gammaℝ_line_eq_norm_mul_exp_theta τ
  have hprod : Complex.Gammaℝ (linePt τ) * levinsonG (lam : ℂ) (linePt τ)
      = ((‖Complex.Gammaℝ (linePt τ)‖ : ℝ) : ℂ)
        * (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * levinsonG (lam : ℂ) (linePt τ)) := by
    conv_lhs => rw [hgam]
    ring
  rw [hprod, Complex.re_ofReal_mul] at hkey
  have hcast : ((2 - lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
        + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi) : ℝ) : ℂ)
      * ((‖Complex.Gammaℝ (linePt τ)‖ * hardyZ τ : ℝ) : ℂ)
      = (((2 - lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
        + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi))
        * (‖Complex.Gammaℝ (linePt τ)‖ * hardyZ τ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast] at hkey
  have hreal : ((2 - lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
        + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi))
        * (‖Complex.Gammaℝ (linePt τ)‖ * hardyZ τ))
      = 2 * (‖Complex.Gammaℝ (linePt τ)‖
        * (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * levinsonG (lam : ℂ) (linePt τ)).re) := by
    exact_mod_cast hkey
  have hYre : (levinsonY (lam : ℂ) (linePt τ)).re
      = 2 - lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
        + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi) := by
    rw [levinsonY_line_eq, Complex.ofReal_re]
  rw [hYre]
  refine mul_left_cancel₀ hnorm.ne' ?_
  linear_combination hreal

/-! ## Analyticity of the detector -/

theorem analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hana : AnalyticOnNhd ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt) hopen
  exact hana s hs

theorem analyticAt_levinsonG (lam : ℂ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (levinsonG lam) s := by
  have hz := analyticAt_riemannZeta_of_ne_one hs
  exact hz.add (analyticAt_const.mul hz.deriv)

theorem linePt_ne_one' (τ : ℝ) : linePt τ ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [linePt_re, Complex.one_re] at hre
  norm_num at hre

theorem hasDerivAt_detectorPhase (lam : ℝ) (τ : ℝ) :
    HasDerivAt (fun u : ℝ =>
        Complex.exp (I * (gammaHardyTheta u : ℂ)) * levinsonG (lam : ℂ) (linePt u))
      (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * (I * (gammaHardyPhaseRate τ : ℂ))
          * levinsonG (lam : ℂ) (linePt τ)
        + Complex.exp (I * (gammaHardyTheta τ : ℂ))
          * (deriv (levinsonG (lam : ℂ)) (linePt τ) * I)) τ := by
  have hθ : HasDerivAt (fun u : ℝ => I * (gammaHardyTheta u : ℂ))
      (I * (gammaHardyPhaseRate τ : ℂ)) τ :=
    ((hasDerivAt_gammaHardyTheta τ).ofReal_comp).const_mul I
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (I * (gammaHardyTheta u : ℂ)))
      (Complex.exp (I * (gammaHardyTheta τ : ℂ)) * (I * (gammaHardyPhaseRate τ : ℂ))) τ := by
    simpa [mul_comm] using hθ.cexp
  have hpath : HasDerivAt linePt I τ := by
    unfold linePt
    have h := ((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const I).const_add
      (((1 / 2 : ℝ) : ℂ))
    simpa using h
  have hG : HasDerivAt (levinsonG (lam : ℂ))
      (deriv (levinsonG (lam : ℂ)) (linePt τ)) (linePt τ) :=
    (analyticAt_levinsonG (lam : ℂ) (linePt_ne_one' τ)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => levinsonG (lam : ℂ) (linePt u))
      (deriv (levinsonG (lam : ℂ)) (linePt τ) * I) τ := hG.comp τ hpath
  exact hexp.mul hcomp

theorem continuous_linePt' : Continuous linePt := by
  unfold linePt
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- **The polar representation of Hardy's `Z` produced by Levinson's detector.**  On a window above
height `20` where `G` does not vanish, `Z = ρ·cos ψ` with `ρ > 0` and `ψ` continuous; the phase is
the archimedean phase `θ` plus the phase of `G`. -/
theorem exists_polar_hardyZ_of_levinsonG_ne_zero {lam : ℝ} (hlam : lam ≤ 0)
    {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ ≤ T₂)
    (hne : ∀ τ ∈ Icc T₁ T₂, levinsonG (lam : ℂ) (linePt τ) ≠ 0) :
    ∃ ρ ψ : ℝ → ℝ, ContinuousOn ψ (Icc T₁ T₂) ∧ (∀ τ ∈ Icc T₁ T₂, 0 < ρ τ) ∧
      (∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ)) := by
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
  have hratec : Continuous gammaHardyPhaseRate := continuous_gammaHardyPhaseRate
  have hg'c : Continuous g' := by
    rw [hg'def]
    exact ((hexpc.mul (continuous_const.mul
      (Complex.continuous_ofReal.comp hratec))).mul hGc).add
      (hexpc.mul (hG'c.mul continuous_const))
  have hgc : Continuous g := by
    rw [hgdef]
    exact hexpc.mul hGc
  have hquot : ContinuousOn (fun τ => g' τ / g τ) (Icc T₁ T₂) :=
    ContinuousOn.div hg'c.continuousOn hgc.continuousOn hgne
  obtain ⟨r, ψ, hψc, hrpos, _, hpolar⟩ :=
    exists_continuousOn_polar (f := g) (f' := g') hT (fun τ _ => hgderiv τ) hquot hgne
  refine ⟨fun τ => 2 * r τ / (levinsonY (lam : ℂ) (linePt τ)).re, ψ, hψc, ?_, ?_⟩
  · intro τ hτ
    have hY : (0 : ℝ) < (levinsonY (lam : ℂ) (linePt τ)).re := by
      rw [levinsonY_line_eq, Complex.ofReal_re]
      have hd := log_pi_lt_re_digamma_quarter (le_trans h20 hτ.1)
      nlinarith
    have := hrpos τ hτ
    positivity
  · intro τ hτ
    have hY : (0 : ℝ) < (levinsonY (lam : ℂ) (linePt τ)).re := by
      rw [levinsonY_line_eq, Complex.ofReal_re]
      have hd := log_pi_lt_re_digamma_quarter (le_trans h20 hτ.1)
      nlinarith
    have hid : ((levinsonY (lam : ℂ) (linePt τ)).re * hardyZ τ : ℝ) = 2 * (g τ).re :=
      levinsonY_line_mul_hardyZ lam τ
    rw [hpolar τ hτ] at hid
    field_simp
    linarith [hid]

end RHTower

end
