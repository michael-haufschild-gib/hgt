import GaloisForLFunctions.RHTower.ThetaCuspSchwartzComplexTranslation
import Mathlib.Analysis.Calculus.MeanValue

/-!
Uniform quadratic Taylor estimates for the literal theta source's complex jets.
Two mean-value estimates on nested complex discs preserve exponential decay
in the real spatial variable.
-/

open Set
open scoped ContDiff SchwartzMap

noncomputable section

namespace RHTower

private theorem thetaComplex_taylor_quadratic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f f₁ f₂ : ℂ → F} {z h : ℂ} {ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hh : ‖h‖ ≤ ρ)
    (hf : ∀ w ∈ Metric.closedBall z ρ, HasDerivAt f (f₁ w) w)
    (hf₁ : ∀ w ∈ Metric.closedBall z ρ, HasDerivAt f₁ (f₂ w) w)
    (hbound : ∀ w ∈ Metric.closedBall z ρ, ‖f₂ w‖ ≤ B) :
    ‖f (z + h) - f z - h • f₁ z‖ ≤ B * ‖h‖ ^ 2 := by
  have hz : z ∈ Metric.closedBall z ρ := Metric.mem_closedBall_self hρ
  have h₁ : ∀ w ∈ Metric.closedBall z ρ, ‖f₁ w - f₁ z‖ ≤ B * ‖w - z‖ := by
    intro w hw
    apply Convex.norm_image_sub_le_of_norm_deriv_le
      (fun v hv => (hf₁ v hv).differentiableAt)
      (fun v hv => by rw [(hf₁ v hv).deriv]; exact hbound v hv)
      (convex_closedBall z ρ) hz hw
  let g : ℂ → F := fun w => f w - f z - (w - z) • f₁ z
  have hg : ∀ w ∈ Metric.closedBall z ρ, HasDerivAt g (f₁ w - f₁ z) w := by
    intro w hw
    convert!
      ((hf w hw).sub_const (f z)).sub
        (((hasDerivAt_id w).sub_const z).smul_const (f₁ z)) using 1
    simp only [one_smul]
  have hsmall : Metric.closedBall z ‖h‖ ⊆ Metric.closedBall z ρ :=
    Metric.closedBall_subset_closedBall hh
  have hgBound : ∀ w ∈ Metric.closedBall z ‖h‖,
      ‖deriv g w‖ ≤ B * ‖h‖ := by
    intro w hw
    rw [(hg w (hsmall hw)).deriv]
    have hn : ‖w - z‖ ≤ ‖h‖ := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
    exact (h₁ w (hsmall hw)).trans (mul_le_mul_of_nonneg_left hn hB)
  have hzSmall : z ∈ Metric.closedBall z ‖h‖ :=
    Metric.mem_closedBall_self (norm_nonneg h)
  have hhSmall : z + h ∈ Metric.closedBall z ‖h‖ := by
    apply Metric.mem_closedBall.mpr
    simp only [dist_eq_norm, add_sub_cancel_left]
    exact le_rfl
  have ht := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hg w (hsmall hw)).differentiableAt) hgBound
    (convex_closedBall z ‖h‖) hzSmall hhSmall
  simpa only [g, add_sub_cancel_left, sub_self, zero_smul, sub_zero, mul_pow,
    pow_two, mul_assoc] using ht

private theorem thetaComplex_absIm_shift_le {w z : ℂ} {r : ℝ}
    (h : ‖w - z‖ ≤ r) : |w.im| ≤ |z.im| + r := by
  have him := (Complex.abs_im_le_norm (w - z)).trans h
  rw [Complex.sub_im] at him
  calc
    |w.im| = |z.im + (w.im - z.im)| := by congr 1; ring
    _ ≤ |z.im| + |w.im - z.im| := abs_add_le _ _
    _ ≤ |z.im| + r := by gcongr

private theorem thetaComplex_expRe_shift_le {w z : ℂ} {r : ℝ}
    (h : ‖w - z‖ ≤ r) : Real.exp (-|w.re|) ≤ Real.exp r * Real.exp (-|z.re|) := by
  have hre := (Complex.abs_re_le_norm (w - z)).trans h
  rw [Complex.sub_re] at hre
  have hz : |z.re| ≤ |w.re| + r := by
    calc
      |z.re| = |w.re + (z.re - w.re)| := by congr 1; ring
      _ ≤ |w.re| + |z.re - w.re| := abs_add_le _ _
      _ = |w.re| + |w.re - z.re| := by rw [abs_sub_comm]
      _ ≤ |w.re| + r := by gcongr
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

private theorem thetaReal_expAbs_shift_le (a x : ℝ) :
    Real.exp (-|x + a|) ≤ Real.exp |a| * Real.exp (-|x|) := by
  have hx : |x| ≤ |x + a| + |a| := by
    calc
      |x| = |(x + a) + (-a)| := by congr 1; ring
      _ ≤ |x + a| + |-a| := abs_add_le _ _
      _ = |x + a| + |a| := by rw [abs_neg]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Uniform quadratic Taylor control of the actual complex source jets on closed substrips. -/
theorem thetaCuspStripSource_complexJet_taylor_substrip {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) (n : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : ℂ, |a.im| ≤ δ → ∀ h : ℂ, ‖h‖ ≤ ρ → ∀ x : ℝ,
        ‖iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a + h) -
          iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a) -
          h * iteratedDeriv (n + 1) thetaCuspStripSource ((x : ℂ) + a)‖ ≤
            C * Real.exp |a.re| * Real.exp (-|x|) * ‖h‖ ^ 2 := by
  let ρ := (Real.pi / 4 - δ) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hδρ0 : 0 ≤ δ + ρ := by linarith
  have hδρ4 : 2 * (δ + ρ) < Real.pi / 2 := by dsimp [ρ]; linarith
  obtain ⟨C, hC, hbound⟩ :=
    thetaCuspStripSource_complexJet_exp_decay hδρ0 hδρ4 (n + 2)
  refine ⟨ρ, hρ, C * Real.exp ρ, by positivity, ?_⟩
  intro a ha h hh x
  let z : ℂ := (x : ℂ) + a
  have hzIm : |z.im| ≤ δ := by
    simpa only [z, Complex.add_im, Complex.ofReal_im, zero_add] using ha
  have hwIm : ∀ w ∈ Metric.closedBall z ρ, |w.im| ≤ δ + ρ := by
    intro w hw
    have hn : ‖w - z‖ ≤ ρ := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
    exact (thetaComplex_absIm_shift_le hn).trans (by gcongr)
  have hwStrip : ∀ w ∈ Metric.closedBall z ρ, w ∈ thetaCuspStrip := by
    intro w hw
    change |w.im| < Real.pi / 4
    have hi := hwIm w hw
    linarith
  have hf : ∀ w ∈ Metric.closedBall z ρ,
      HasDerivAt (iteratedDeriv n thetaCuspStripSource)
        (iteratedDeriv (n + 1) thetaCuspStripSource w) w := by
    intro w hw
    simpa only [iteratedDeriv_succ] using
      (thetaCuspStripSource_complexJet_analyticAt n (hwStrip w hw)).differentiableAt.hasDerivAt
  have hf₁ : ∀ w ∈ Metric.closedBall z ρ,
      HasDerivAt (iteratedDeriv (n + 1) thetaCuspStripSource)
        (iteratedDeriv (n + 2) thetaCuspStripSource w) w := by
    intro w hw
    simpa only [iteratedDeriv_succ, Nat.add_assoc] using
      (thetaCuspStripSource_complexJet_analyticAt (n + 1)
        (hwStrip w hw)).differentiableAt.hasDerivAt
  have hsecond : ∀ w ∈ Metric.closedBall z ρ,
      ‖iteratedDeriv (n + 2) thetaCuspStripSource w‖ ≤
        C * Real.exp ρ * Real.exp |a.re| * Real.exp (-|x|) := by
    intro w hw
    have hn : ‖w - z‖ ≤ ρ := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
    have he := thetaComplex_expRe_shift_le hn
    have hz : Real.exp (-|z.re|) ≤ Real.exp |a.re| * Real.exp (-|x|) := by
      simpa only [z, Complex.add_re, Complex.ofReal_re] using
        thetaReal_expAbs_shift_le a.re x
    calc
      ‖iteratedDeriv (n + 2) thetaCuspStripSource w‖ ≤ C * Real.exp (-|w.re|) :=
        hbound w (hwIm w hw)
      _ ≤ C * (Real.exp ρ * Real.exp (-|z.re|)) := by gcongr
      _ ≤ C * (Real.exp ρ * (Real.exp |a.re| * Real.exp (-|x|))) := by gcongr
      _ = C * Real.exp ρ * Real.exp |a.re| * Real.exp (-|x|) := by ring
  simpa only [smul_eq_mul] using
    thetaComplex_taylor_quadratic hρ.le (by positivity) hh hf hf₁ hsecond

end RHTower
