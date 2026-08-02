import GaloisForLFunctions.RHTower.DeningerMeyerFullXiJetAdmissionBoundary

/-!
# Cofinal Xi synthesis is singular to every finite differential order

Literal Meyer cohomology realizes every finite actual-Xi jet packet, but the
finite synthesis cannot remain regular along a cofinal divisor exhaustion.
This module makes that failure quantitative to every differential order.

For the weighted logarithmic profile

`h_σ(t) = exp(σt) g(t)`,

the `n`-fold derivative is again a weighted all-weight Meyer profile.  Fourier
integration by parts therefore gives the exact family of estimates

`|τ|^n ‖M_g(σ+iτ)‖ ≤ ∫ ‖h_σ^(n)(t)‖ dt`.

An actual sequence of Xi divisor points has `|Im ρ_j| > j+1`.  Finite packet
surjectivity supplies a literal source at each stage whose value there is one,
but every such source has order-`n` weighted Sobolev cost strictly greater than
`(j+1)^n`, for every `n > 0`.  Thus all finite divisor packets are algebraically
synthesizable while every cofinal unit synthesis becomes singular at every
fixed positive differential order.

This is the quantitative finite-to-infinite boundary required by source
conservation.  It rules out a uniformly regular inverse-limit section; it does
not assume or manufacture an arithmetic source comparison.

All results are unconditional.  No RH, simplicity, positivity, trace,
numerical computation, inverse Mellin theorem, or global synthesis premise is
used.
-/

open Complex Filter Function Set Topology MeasureTheory
open scoped Classical FourierTransform

namespace RHTower

noncomputable section

/--
Conjugated derivative on an exponentially weighted logarithmic profile.
-/
def deningerMeyerWeightedEuler
    (sigma : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  (sigma : ℂ) • g + deriv g

/-- Iterates of the conjugated weighted derivative. -/
def deningerMeyerWeightedEulerIterate (sigma : ℝ) :
    ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, g => g
  | n + 1, g =>
      deningerMeyerWeightedEuler sigma
        (deningerMeyerWeightedEulerIterate sigma n g)

theorem DeningerMeyerStrongLogDecay.weightedEuler
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma : ℝ) :
    DeningerMeyerStrongLogDecay
      (deningerMeyerWeightedEuler sigma g) := by
  exact (hg.smul (sigma : ℂ)).add hg.deriv

theorem DeningerMeyerStrongLogDecay.weightedEulerIterate
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma : ℝ) (n : ℕ) :
    DeningerMeyerStrongLogDecay
      (deningerMeyerWeightedEulerIterate sigma n g) := by
  induction n with
  | zero => exact hg
  | succ n ih => exact ih.weightedEuler sigma

theorem deriv_deningerMeyerWeightedLogProfile
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma : ℝ) :
    deriv (deningerMeyerWeightedLogProfile sigma g) =
      deningerMeyerWeightedLogProfile sigma
        (deningerMeyerWeightedEuler sigma g) := by
  funext t
  rw [(hasDerivAt_deningerMeyerWeightedLogProfile hg sigma t).deriv]
  simp only [deningerMeyerWeightedLogProfile,
    deningerMeyerWeightedEuler, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/--
Every iterated derivative of a weighted profile is the same weight applied to
the corresponding conjugated Euler iterate.
-/
theorem iteratedDeriv_deningerMeyerWeightedLogProfile
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma : ℝ) (n : ℕ) :
    iteratedDeriv n
        (deningerMeyerWeightedLogProfile sigma g) =
      deningerMeyerWeightedLogProfile sigma
        (deningerMeyerWeightedEulerIterate sigma n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      rw [ih]
      exact
        deriv_deningerMeyerWeightedLogProfile
          (hg.weightedEulerIterate sigma n) sigma

theorem integrable_iteratedDeriv_deningerMeyerWeightedLogProfile
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma : ℝ) (n : ℕ) :
    Integrable
      (iteratedDeriv n
        (deningerMeyerWeightedLogProfile sigma g)) := by
  rw [iteratedDeriv_deningerMeyerWeightedLogProfile hg sigma n]
  exact
    integrable_deningerMeyerWeightedLogProfile
      (hg.weightedEulerIterate sigma n) sigma

/--
All-orders vertical Mellin estimate obtained by exact repeated Fourier
integration by parts.
-/
theorem abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le
    (g : DeningerMeyerStrongLogTarget)
    (n : ℕ) (sigma tau : ℝ) :
    |tau| ^ n *
        ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ ≤
      ∫ t : ℝ,
        ‖iteratedDeriv n
          (deningerMeyerWeightedLogProfile sigma g) t‖ := by
  let w : ℝ := -tau / (2 * Real.pi)
  have hsmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (deningerMeyerWeightedLogProfile sigma g) := by
    unfold deningerMeyerWeightedLogProfile
    have hlin :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun t : ℝ => sigma * t) :=
      contDiff_const.mul contDiff_id
    have hexpR :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun t : ℝ => Real.exp (sigma * t)) :=
      Real.contDiff_exp.comp hlin
    exact
      (Complex.ofRealCLM.contDiff.comp hexpR).mul
        g.property.smooth
  have hint :
      ∀ m : ℕ, (m : ℕ∞) ≤ (⊤ : ℕ∞) →
        Integrable
          (iteratedDeriv m
            (deningerMeyerWeightedLogProfile sigma g)) := by
    intro m _hm
    exact
      integrable_iteratedDeriv_deningerMeyerWeightedLogProfile
        g.property sigma m
  have hfour :=
    congrFun
      (Real.fourier_iteratedDeriv
        (N := (⊤ : ℕ∞)) hsmooth hint
          (by simp : (n : ℕ∞) ≤ (⊤ : ℕ∞)))
      w
  have hscalar :
      ((2 * Real.pi * Complex.I * w : ℂ)) =
        (-tau : ℂ) * Complex.I := by
    dsimp only [w]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hfourBound :
      ‖FourierTransform.fourier
          (iteratedDeriv n
            (deningerMeyerWeightedLogProfile sigma g)) w‖ ≤
        ∫ t : ℝ,
          ‖iteratedDeriv n
            (deningerMeyerWeightedLogProfile sigma g) t‖ := by
    simpa only [Real.fourier_real_eq,
      Fourier.fourierIntegral_def] using
      (Fourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar MeasureTheory.volume
        (iteratedDeriv n
          (deningerMeyerWeightedLogProfile sigma g)) w)
  calc
    |tau| ^ n *
        ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ =
      ‖((2 * Real.pi * Complex.I * w : ℂ) ^ n) •
        FourierTransform.fourier
          (deningerMeyerWeightedLogProfile sigma g) w‖ := by
        rw [deningerMeyerStrongLogMellin_eq_fourier_weighted]
        rw [hscalar]
        simp only [norm_smul, norm_pow, norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          norm_neg, Complex.norm_I, mul_one]
        rfl
    _ =
        ‖FourierTransform.fourier
          (iteratedDeriv n
            (deningerMeyerWeightedLogProfile sigma g)) w‖ := by
      rw [hfour]
    _ ≤
        ∫ t : ℝ,
          ‖iteratedDeriv n
            (deningerMeyerWeightedLogProfile sigma g) t‖ :=
      hfourBound

/--
Natural order-`n` `L¹` Sobolev cost on the vertical line `Re s = sigma`.
-/
def deningerMeyerVerticalSobolevCost
    (n : ℕ) (sigma : ℝ)
    (g : DeningerMeyerStrongLogTarget) : ℝ :=
  ∫ t : ℝ,
    ‖iteratedDeriv n
      (deningerMeyerWeightedLogProfile sigma g) t‖

/--
Any literal source taking value one at the `stage`-th escaping actual Xi point
has order-`n` source cost greater than `(stage+1)^n`.
-/
theorem deningerMeyerVerticalSobolevCost_gt_pow_of_unit_at_xiEscape
    (g : DeningerMeyerStrongLogTarget)
    (stage order : ℕ) (horder : order ≠ 0)
    (hvalue :
      deningerMeyerStrongLogMellin g
        (deningerMeyerXiVerticalEscape stage : ℂ) = 1) :
    ((stage : ℝ) + 1) ^ order <
      deningerMeyerVerticalSobolevCost order
        (deningerMeyerXiVerticalEscape stage : ℂ).re g := by
  have hheight :=
    deningerMeyerXiVerticalEscape_abs_im_gt stage
  have hpow :
      ((stage : ℝ) + 1) ^ order <
        |(deningerMeyerXiVerticalEscape stage : ℂ).im| ^ order :=
    pow_lt_pow_left₀ hheight (by positivity) horder
  have hbound :=
    abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le
      g order
      (deningerMeyerXiVerticalEscape stage : ℂ).re
      (deningerMeyerXiVerticalEscape stage : ℂ).im
  rw [Complex.re_add_im] at hbound
  rw [hvalue, norm_one, mul_one] at hbound
  exact hpow.trans_le hbound

/--
Finite Xi packet surjectivity supplies a literal source taking value one at
each member of the chosen cofinal divisor sequence.
-/
theorem exists_deningerMeyerXiCofinalUnitSynthesis :
    ∃ source : ℕ → DeningerMeyerStrongLogTarget,
      ∀ stage,
        deningerMeyerStrongLogMellin (source stage)
          (deningerMeyerXiVerticalEscape stage : ℂ) = 1 := by
  have hcohom :
      ∀ stage : ℕ,
        ∃ u : DeningerMeyerStrongLogCohomology,
          deningerMeyerXiJetPacketLM
              (deningerMeyerXiVerticalEscape stage) u =
            fun _ => 1 := by
    intro stage
    exact
      deningerMeyerXiJetPacketLM_surjective
        (deningerMeyerXiVerticalEscape stage) (fun _ => 1)
  choose u hu using hcohom
  have hsource :
      ∀ stage : ℕ,
        ∃ g : DeningerMeyerStrongLogTarget,
          Submodule.Quotient.mk g = u stage := by
    intro stage
    exact
      Submodule.Quotient.mk_surjective
        (LinearMap.range deningerMeyerStrongLogSumLM)
        (u stage)
  choose source hsource using hsource
  refine ⟨source, ?_⟩
  intro stage
  let k0 :
      DeningerArithmeticJetIndex
        (deningerMeyerXiVerticalEscape stage) :=
    ⟨0, xiSupportMultiplicity_pos
      (deningerMeyerXiVerticalEscape stage)⟩
  have hcoord := congrFun (hu stage) k0
  rw [← hsource stage] at hcoord
  simpa only [
    deningerMeyerXiJetPacketLM_apply,
    deningerMeyerXiSupportJetEvaluationLM_mk,
    k0,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    iteratedDeriv_zero] using hcoord

/-- One chosen literal cofinal unit synthesis. -/
noncomputable def deningerMeyerXiCofinalUnitSynthesis :
    ℕ → DeningerMeyerStrongLogTarget :=
  Classical.choose exists_deningerMeyerXiCofinalUnitSynthesis

theorem deningerMeyerXiCofinalUnitSynthesis_value
    (stage : ℕ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerXiCofinalUnitSynthesis stage)
        (deningerMeyerXiVerticalEscape stage : ℂ) = 1 :=
  Classical.choose_spec
    exists_deningerMeyerXiCofinalUnitSynthesis stage

/--
Exact all-orders synthesis singularity: at order `n > 0`, cofinal unit
synthesis costs more than `(stage+1)^n`.
-/
theorem deningerMeyerXiCofinalUnitSynthesis_cost_gt_pow
    (stage order : ℕ) (horder : order ≠ 0) :
    ((stage : ℝ) + 1) ^ order <
      deningerMeyerVerticalSobolevCost order
        (deningerMeyerXiVerticalEscape stage : ℂ).re
        (deningerMeyerXiCofinalUnitSynthesis stage) :=
  deningerMeyerVerticalSobolevCost_gt_pow_of_unit_at_xiEscape
    (deningerMeyerXiCofinalUnitSynthesis stage)
    stage order horder
    (deningerMeyerXiCofinalUnitSynthesis_value stage)

end

end RHTower
