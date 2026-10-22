import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBogoliubovBornEndpoint
import GaloisForLFunctions.RHTower.XiCentralDiscBound
import GaloisForLFunctions.HTGeometry.HolomorphicSchwarzPolarization
import GaloisForLFunctions.Bottcher.AnalyticDomain
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Bulk holomorphic Hermitian optical landing: local no-go

This module kills the same-complex-variable bulk-local candidate for the missing phase-sensitive
Hawking optical theorem.  The actual balanced theta-cusp Hawking Born amplitude is entire and
nonconstant: it vanishes at zero and is nonzero at one.  By contrast, every pointwise Hermitian
anomaly

`conj (B z) * C z + conj (C z) * B z`

is fixed by conjugation.  Therefore equality, up to any fixed nonzero complex phase, on even one
nonempty open complex-frequency domain would make a fixed rescaling of the Born amplitude a
real-valued holomorphic function on an interior ball.  It is constant there and hence, by analytic
continuation, constant everywhere, contradicting the exact values at zero and one.  No regularity
of `B` or `C` is assumed.

**Route killed.** A same-variable pointwise bulk holomorphic Hermitian identity cannot supply the
opposite-sign causal orbit required by the HB chain

`optical identity -> total-cokernel extinction -> source-FE unit clock gain -> Ward cancellation`.

This excludes neither a real-axis/distributional boundary identity nor a nonlocal identity.  The
sharp analytic survivor is Schwarz polarization: put conjugated coefficient families in an
independent variable `w`, where `conj (B (conj w))` is holomorphic, and recover the Hermitian term
only after restricting to `w = conj z`.
-/

open Complex Real Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Pointwise same-variable Hermitian anomaly proposed as a local Hawking optical producer. -/
def thetaCuspHawkingLocalHermitianAnomaly
    (boundary response : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (boundary z) * response z +
    (starRingEnd ℂ) (response z) * boundary z

/-- Every pointwise Hermitian anomaly is fixed by conjugation, without regularity assumptions. -/
theorem star_thetaCuspHawkingLocalHermitianAnomaly
    (boundary response : ℂ → ℂ) (z : ℂ) :
    (starRingEnd ℂ)
        (thetaCuspHawkingLocalHermitianAnomaly boundary response z) =
      thetaCuspHawkingLocalHermitianAnomaly boundary response z := by
  simp [thetaCuspHawkingLocalHermitianAnomaly]
  ring

/-- Stronger global landing, retained as a convenient named special case. -/
def ThetaCuspHawkingSameVariableBulkHermitianOpticalLanding : Prop :=
  ∃ phase : ℂ, phase ≠ 0 ∧
    ∃ boundary response : ℂ → ℂ,
      ∀ z : ℂ,
        thetaCuspBalancedHawkingBornAmplitude z =
          phase * thetaCuspHawkingLocalHermitianAnomaly boundary response z

/-- Local landing on an arbitrary nonempty open complex-frequency domain.  The domain need not be
connected, and the boundary/response families need not themselves be regular. -/
def ThetaCuspHawkingSameVariableLocalHermitianOpticalLanding : Prop :=
  ∃ Ω : Set ℂ, IsOpen Ω ∧ Ω.Nonempty ∧
    ∃ phase : ℂ, phase ≠ 0 ∧
      ∃ boundary response : ℂ → ℂ,
        ∀ z ∈ Ω,
          thetaCuspBalancedHawkingBornAmplitude z =
            phase * thetaCuspHawkingLocalHermitianAnomaly boundary response z

private theorem differentiable_thetaCuspBalancedHawkingBornAmplitude :
    Differentiable ℂ thetaCuspBalancedHawkingBornAmplitude := by
  unfold thetaCuspBalancedHawkingBornAmplitude
  exact (((differentiable_const _).mul differentiable_id).mul
    HedenmalmThetaSource.differentiable_thetaCuspFourierLaplace_all)

/-- Exact zero anchor for the balanced Hawking Born amplitude. -/
theorem thetaCuspBalancedHawkingBornAmplitude_zero :
    thetaCuspBalancedHawkingBornAmplitude 0 = 0 := by
  simp [thetaCuspBalancedHawkingBornAmplitude]

/-- Exact nonzero anchor, using the proved central-disc zero-free theorem for `XiC`. -/
theorem thetaCuspBalancedHawkingBornAmplitude_one_ne_zero :
    thetaCuspBalancedHawkingBornAmplitude 1 ≠ 0 := by
  rw [thetaCuspBalancedHawkingBornAmplitude_eq_XiC]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcoeff : -Complex.I / (4 * (Real.pi : ℂ)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (mul_ne_zero (by norm_num) hpi)
  have hxi : XiC (1 : ℂ) ≠ 0 := XiC_ne_zero_of_norm_le_one (by norm_num)
  simpa using mul_ne_zero hcoeff hxi

/-- No global same-variable Hermitian landing exists. -/
theorem not_thetaCuspHawkingSameVariableBulkHermitianOpticalLanding :
    ¬ ThetaCuspHawkingSameVariableBulkHermitianOpticalLanding := by
  rintro ⟨phase, hphase, boundary, response, hlanding⟩
  let scaled : ℂ → ℂ := fun z => phase⁻¹ * thetaCuspBalancedHawkingBornAmplitude z
  have hscaledDiff : Differentiable ℂ scaled :=
    (differentiable_const phase⁻¹).mul
      differentiable_thetaCuspBalancedHawkingBornAmplitude
  have hscaledAnomaly : ∀ z : ℂ,
      scaled z = thetaCuspHawkingLocalHermitianAnomaly boundary response z := by
    intro z
    dsimp [scaled]
    rw [hlanding z]
    simp [hphase]
  have hscaledStar :
      Differentiable ℂ (fun z => (starRingEnd ℂ) (scaled z)) := by
    have heq : (fun z => (starRingEnd ℂ) (scaled z)) = scaled := by
      funext z
      rw [hscaledAnomaly z,
        star_thetaCuspHawkingLocalHermitianAnomaly,
        ← hscaledAnomaly z]
    rw [heq]
    exact hscaledDiff
  have hconst := eq_of_differentiable_pointwiseStar
    hscaledDiff hscaledStar (1 : ℂ)
  change phase⁻¹ * thetaCuspBalancedHawkingBornAmplitude 1 =
    phase⁻¹ * thetaCuspBalancedHawkingBornAmplitude 0 at hconst
  have honeZero : thetaCuspBalancedHawkingBornAmplitude 1 = 0 := by
    rw [thetaCuspBalancedHawkingBornAmplitude_zero] at hconst
    simp only [mul_zero] at hconst
    exact (mul_eq_zero.mp hconst).resolve_left (inv_ne_zero hphase)
  exact thetaCuspBalancedHawkingBornAmplitude_one_ne_zero honeZero

/-- **Local-open route kill.**  Equality on any nonempty open complex-frequency domain is already
impossible.  An interior ball makes the rescaled amplitude real-valued and holomorphic, hence
constant; open-set uniqueness then propagates that constant to the entire plane. -/
theorem not_thetaCuspHawkingSameVariableLocalHermitianOpticalLanding :
    ¬ ThetaCuspHawkingSameVariableLocalHermitianOpticalLanding := by
  rintro ⟨Ω, hΩ, hΩne, phase, hphase, boundary, response, hlanding⟩
  obtain ⟨s₀, hs₀⟩ := hΩne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ s₀ hs₀
  let scaled : ℂ → ℂ := fun z => phase⁻¹ * thetaCuspBalancedHawkingBornAmplitude z
  have hscaledDiff : Differentiable ℂ scaled :=
    (differentiable_const phase⁻¹).mul
      differentiable_thetaCuspBalancedHawkingBornAmplitude
  have hscaledAn : AnalyticOnNhd ℂ scaled Set.univ :=
    hscaledDiff.differentiableOn.analyticOnNhd isOpen_univ
  have hscaledAnBall : AnalyticOnNhd ℂ scaled (Metric.ball s₀ ε) :=
    hscaledAn.mono (fun _ _ => Set.mem_univ _)
  have hscaledAnomaly : ∀ z ∈ Metric.ball s₀ ε,
      scaled z = thetaCuspHawkingLocalHermitianAnomaly boundary response z := by
    intro z hz
    dsimp [scaled]
    rw [hlanding z (hball hz)]
    simp [hphase]
  have hscaledIm : ∀ z ∈ Metric.ball s₀ ε, (scaled z).im = 0 := by
    intro z hz
    have hself : (starRingEnd ℂ) (scaled z) = scaled z := by
      rw [hscaledAnomaly z hz,
        star_thetaCuspHawkingLocalHermitianAnomaly,
        ← hscaledAnomaly z hz]
    have him := congrArg Complex.im hself
    rw [Complex.conj_im] at him
    linarith
  obtain ⟨c, hconst⟩ := AnalyticOnNhd.eq_const_of_im_eq_const
    hscaledAnBall hscaledIm Metric.isOpen_ball (Metric.isConnected_ball hε)
  have hglobal : Set.EqOn scaled (fun _ => c) Set.univ :=
    Bottcher.analyticOnNhd_eqOn_of_eqOn_isOpen
      hscaledAn analyticOnNhd_const isPreconnected_univ
      (fun _ _ => Set.mem_univ _)
      Metric.isOpen_ball
      ⟨s₀, Metric.mem_ball_self hε⟩
      (fun z hz => hconst z hz)
  have hconst10 : scaled 1 = scaled 0 :=
    (hglobal (Set.mem_univ 1)).trans (hglobal (Set.mem_univ 0)).symm
  change phase⁻¹ * thetaCuspBalancedHawkingBornAmplitude 1 =
    phase⁻¹ * thetaCuspBalancedHawkingBornAmplitude 0 at hconst10
  rw [thetaCuspBalancedHawkingBornAmplitude_zero] at hconst10
  simp only [mul_zero] at hconst10
  have honeZero : thetaCuspBalancedHawkingBornAmplitude 1 = 0 :=
    (mul_eq_zero.mp hconst10).resolve_left (inv_ne_zero hphase)
  exact thetaCuspBalancedHawkingBornAmplitude_one_ne_zero honeZero

/-- Two-variable Schwarz-polarized replacement for the forbidden same-variable anomaly. -/
def thetaCuspHawkingSchwarzPolarizedAnomaly
    (boundary response : ℂ → ℂ) (z w : ℂ) : ℂ :=
  schwarzPolarizedPartner boundary w * response z +
    schwarzPolarizedPartner response w * boundary z

/-- Restriction to the Schwarz diagonal recovers the pointwise Hermitian anomaly exactly. -/
theorem thetaCuspHawkingSchwarzPolarizedAnomaly_diagonal
    (boundary response : ℂ → ℂ) (z : ℂ) :
    thetaCuspHawkingSchwarzPolarizedAnomaly boundary response z
        ((starRingEnd ℂ) z) =
      thetaCuspHawkingLocalHermitianAnomaly boundary response z := by
  rw [thetaCuspHawkingSchwarzPolarizedAnomaly,
    thetaCuspHawkingLocalHermitianAnomaly]
  change schwarzPolarizedPartner boundary (star z) * response z +
      schwarzPolarizedPartner response (star z) * boundary z = _
  rw [schwarzPolarizedPartner_star, schwarzPolarizedPartner_star]
  simp only [starRingEnd_apply]

/-- The polarized anomaly is holomorphic in the physical variable when both families are. -/
theorem differentiable_thetaCuspHawkingSchwarzPolarizedAnomaly_left
    {boundary response : ℂ → ℂ}
    (hboundary : Differentiable ℂ boundary)
    (hresponse : Differentiable ℂ response) (w : ℂ) :
    Differentiable ℂ
      (fun z => thetaCuspHawkingSchwarzPolarizedAnomaly boundary response z w) := by
  unfold thetaCuspHawkingSchwarzPolarizedAnomaly
  exact ((differentiable_const _).mul hresponse).add
    ((differentiable_const _).mul hboundary)

/-- The polarized anomaly is holomorphic in the independent Schwarz variable. -/
theorem differentiable_thetaCuspHawkingSchwarzPolarizedAnomaly_right
    {boundary response : ℂ → ℂ}
    (hboundary : Differentiable ℂ boundary)
    (hresponse : Differentiable ℂ response) (z : ℂ) :
    Differentiable ℂ
      (fun w => thetaCuspHawkingSchwarzPolarizedAnomaly boundary response z w) := by
  unfold thetaCuspHawkingSchwarzPolarizedAnomaly
  exact (differentiable_schwarzPolarizedPartner hboundary).mul (differentiable_const _)
    |>.add ((differentiable_schwarzPolarizedPartner hresponse).mul (differentiable_const _))

/-- Closed route-kill certificate together with the exact Schwarz-diagonal survivor. -/
def ThetaCuspHawkingBulkHermitianOpticalNoGoCertificate : Prop :=
  (¬ ThetaCuspHawkingSameVariableLocalHermitianOpticalLanding) ∧
    ∀ boundary response : ℂ → ℂ, ∀ z : ℂ,
      thetaCuspHawkingSchwarzPolarizedAnomaly boundary response z
          ((starRingEnd ℂ) z) =
        thetaCuspHawkingLocalHermitianAnomaly boundary response z

theorem thetaCuspHawkingBulkHermitianOpticalNoGoCertificate :
    ThetaCuspHawkingBulkHermitianOpticalNoGoCertificate := by
  exact ⟨not_thetaCuspHawkingSameVariableLocalHermitianOpticalLanding,
    thetaCuspHawkingSchwarzPolarizedAnomaly_diagonal⟩

end

end RHTower
