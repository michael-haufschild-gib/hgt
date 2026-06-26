/-
# Per-arc winding contributions of the `∂F` contour

Along each boundary arc of the `Γ(2)` fundamental domain `λ` is real (`ModularLambdaCovering`
boundary correspondence). For a target `w ∉ ℝ` the arc never meets `w`, so the interval closed-loop
FTC (`IntervalLogDerivFTC.exp_integral_logDeriv_interval`) gives the winding contribution as an
endpoint ratio. `arc_winding` packages this for an arbitrary path; the three boundary arcs are direct
instances. These are the per-arc summands of the `∮_{∂F} λ'/(λ−w)` argument-principle count.
-/
import GaloisForLFunctions.Bottcher.IntervalLogDerivFTC
import GaloisForLFunctions.Bottcher.ModularLambdaCovering
open Complex Metric Set Filter Topology

namespace Bottcher

/-- **Arc winding contribution.** Along any smooth path `p` into `ℍ` on an open convex `s` where `λ∘p`
is real, for `w ∉ ℝ` the contour integral of `(λ∘p)'/(λ∘p − w)` exponentiates to the endpoint ratio:
`exp(∫ₐᵇ pd·λ'(p)/(λ(p)−w)) = (λ(p b)−w)/(λ(p a)−w)`. The arc never meets `w` (λ(p)∈ℝ, w∉ℝ). -/
theorem arc_winding {p pd : ℝ → ℂ} {s : Set ℝ} (hsopen : IsOpen s) (hsconv : Convex ℝ s)
    (hp : ∀ θ ∈ s, HasDerivAt p (pd θ) θ) (him : ∀ θ ∈ s, 0 < (p θ).im)
    (hreal : ∀ θ ∈ s, (modularLambda (p θ)).im = 0)
    (hcont_pd : ContinuousOn pd s) (hcont_p : ContinuousOn p s)
    {w : ℂ} (hw : w.im ≠ 0) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    Complex.exp (∫ θ in a..b, (pd θ * deriv modularLambda (p θ)) / (modularLambda (p θ) - w))
      = (modularLambda (p b) - w) / (modularLambda (p a) - w) := by
  set g : ℝ → ℂ := fun θ => modularLambda (p θ) - w with hgdef
  set g' : ℝ → ℂ := fun θ => pd θ * deriv modularLambda (p θ) with hg'def
  have hderiv : ∀ θ ∈ s, HasDerivAt g (g' θ) θ := fun θ hθ => by
    have hsc := ((differentiableAt_modularLambda_of_im_pos (him θ hθ)).hasDerivAt).scomp θ (hp θ hθ)
    have hd := hsc.sub_const w
    rw [hgdef, hg'def, smul_eq_mul] at *
    exact hd
  have hg : ∀ θ ∈ s, g θ ≠ 0 := fun θ hθ h0 => by
    apply hw
    have h1 : modularLambda (p θ) = w := sub_eq_zero.mp h0
    rw [← h1]; exact hreal θ hθ
  have hcont' : ContinuousOn g' s := by
    have hdml : ContinuousOn (fun θ => deriv modularLambda (p θ)) s :=
      continuousOn_deriv_modularLambda.comp hcont_p (fun θ hθ => him θ hθ)
    exact hcont_pd.mul hdml
  have hsub : uIcc a b ⊆ s := by rw [← segment_eq_uIcc]; exact hsconv.segment_subset ha hb
  exact exp_integral_logDeriv_interval hsopen hsconv hsub hderiv hg hcont'

/-- Re=0 arc winding (imaginary axis), image `(0,1)`. -/
theorem imAxis_winding {w : ℂ} (hw : w.im ≠ 0) {Y₁ Y₂ : ℝ} (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    Complex.exp (∫ t in Y₁..Y₂,
        (Complex.I * deriv modularLambda ((t:ℂ)*Complex.I)) / (modularLambda ((t:ℂ)*Complex.I) - w))
      = (modularLambda ((Y₂:ℂ)*Complex.I) - w) / (modularLambda ((Y₁:ℂ)*Complex.I) - w) :=
  arc_winding (p := fun t => (t:ℂ)*Complex.I) (pd := fun _ => Complex.I) isOpen_Ioi (convex_Ioi 0)
    (fun θ _ => by simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I)
    (fun θ hθ => by
      simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_one, mul_zero, add_zero]; exact hθ)
    (fun θ _ => modularLambda_im_axis_real)
    continuousOn_const (Complex.continuous_ofReal.mul continuous_const).continuousOn
    hw hY₁ hY₂

/-- Re=1 arc winding, image `(−∞,0)`. -/
theorem reOne_winding {w : ℂ} (hw : w.im ≠ 0) {Y₁ Y₂ : ℝ} (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    Complex.exp (∫ t in Y₁..Y₂,
        (Complex.I * deriv modularLambda (1 + (t:ℂ)*Complex.I)) / (modularLambda (1 + (t:ℂ)*Complex.I) - w))
      = (modularLambda (1 + (Y₂:ℂ)*Complex.I) - w) / (modularLambda (1 + (Y₁:ℂ)*Complex.I) - w) :=
  arc_winding (p := fun t => 1 + (t:ℂ)*Complex.I) (pd := fun _ => Complex.I) isOpen_Ioi (convex_Ioi 0)
    (fun θ _ => by
      have hmI : HasDerivAt (fun t : ℝ => (t:ℂ)*Complex.I) Complex.I θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
      have h := (hasDerivAt_const θ (1:ℂ)).add hmI
      rwa [zero_add] at h)
    (fun θ hθ => by
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero, zero_add]; exact hθ)
    (fun θ _ => modularLambda_re_one_real)
    continuousOn_const
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    hw hY₁ hY₂

/-- Semicircle arc `|2τ−1|=1` winding, image `(1,∞)`. -/
theorem circle_winding {w : ℂ} (hw : w.im ≠ 0) {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ Ioo 0 Real.pi) (hθ₂ : θ₂ ∈ Ioo 0 Real.pi) :
    Complex.exp (∫ θ in θ₁..θ₂,
        ((Complex.I * Complex.exp (Complex.I*(θ:ℂ))/2) * deriv modularLambda ((1 + Complex.exp (Complex.I*(θ:ℂ)))/2))
          / (modularLambda ((1 + Complex.exp (Complex.I*(θ:ℂ)))/2) - w))
      = (modularLambda ((1 + Complex.exp (Complex.I*(θ₂:ℂ)))/2) - w)
          / (modularLambda ((1 + Complex.exp (Complex.I*(θ₁:ℂ)))/2) - w) := by
  have hpim : ∀ θ : ℝ, ((1 + Complex.exp (Complex.I*(θ:ℂ)))/2).im = Real.sin θ / 2 := by
    intro θ
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.div_ofReal_im,
        show Complex.I*(θ:ℂ) = (θ:ℂ)*Complex.I from mul_comm _ _]
    simp [Complex.exp_ofReal_mul_I_im]
  apply arc_winding (p := fun θ => (1 + Complex.exp (Complex.I*(θ:ℂ)))/2)
    (pd := fun θ => Complex.I * Complex.exp (Complex.I*(θ:ℂ))/2) isOpen_Ioo (convex_Ioo 0 Real.pi)
  · intro θ _
    have hexp : HasDerivAt (fun u:ℝ => Complex.exp (Complex.I*(u:ℂ)))
        (Complex.I * Complex.exp (Complex.I*(θ:ℂ))) θ := by
      have h1 : HasDerivAt (fun u:ℝ => Complex.I*(u:ℂ)) Complex.I θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x:=θ)).const_mul Complex.I
      simpa using (Complex.hasDerivAt_exp (Complex.I*(θ:ℂ))).scomp θ h1
    have h := ((hasDerivAt_const θ (1:ℂ)).add hexp).div_const 2
    simpa using h
  · intro θ hθ
    rw [hpim θ]; exact div_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) two_pos
  · intro θ hθ
    apply modularLambda_circle_real
    · rw [hpim θ]; exact div_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) two_pos
    · have hsimp : 2 * ((1 + Complex.exp (Complex.I*(θ:ℂ)))/2) - 1 = Complex.exp (Complex.I*(θ:ℂ)) := by
        ring
      rw [hsimp, show Complex.I*(θ:ℂ) = (θ:ℂ)*Complex.I from mul_comm _ _, Complex.normSq_apply,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      linear_combination Real.sin_sq_add_cos_sq θ
  · exact ((continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).div_const 2).continuousOn
  · exact ((continuous_const.add (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).div_const 2).continuousOn
  · exact hw
  · exact hθ₁
  · exact hθ₂

/-- **Cusp-∞ truncation limit (imaginary-axis arc).** As the top truncation `Y₂ → ∞` (the `i∞` cusp,
`λ → 0`), the imaginary-axis arc winding converges: `exp(∫_{Y₁}^{Y₂} …) → −w/(λ(iY₁)−w)`. -/
theorem imAxis_winding_atTop {w : ℂ} (hw : w.im ≠ 0) {Y₁ : ℝ} (hY₁ : 0 < Y₁) :
    Tendsto (fun Y₂ : ℝ => Complex.exp (∫ t in Y₁..Y₂,
        (Complex.I * deriv modularLambda ((t:ℂ)*Complex.I)) / (modularLambda ((t:ℂ)*Complex.I) - w)))
      atTop (𝓝 ((0 - w) / (modularLambda ((Y₁:ℂ)*Complex.I) - w))) := by
  have hden : modularLambda ((Y₁:ℂ)*Complex.I) - w ≠ 0 := by
    intro h0; apply hw
    have h1 : modularLambda ((Y₁:ℂ)*Complex.I) = w := sub_eq_zero.mp h0
    rw [← h1]; exact modularLambda_im_axis_real
  -- the endpoint ratio tends to the limit
  have hratio : Tendsto (fun Y₂ : ℝ =>
      (modularLambda ((Y₂:ℂ)*Complex.I) - w) / (modularLambda ((Y₁:ℂ)*Complex.I) - w))
      atTop (𝓝 ((0 - w) / (modularLambda ((Y₁:ℂ)*Complex.I) - w))) :=
    ((tendsto_modularLambda_imAxis_atTop.sub_const w)).div_const _
  -- exp(∫) equals the ratio for Y₂ > 0
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Y₂ hY₂
  exact (imAxis_winding hw hY₁ hY₂).symm

end Bottcher
