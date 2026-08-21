import GaloisForLFunctions.RHTower.ThetaTiltFluxCarrier
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss

/-!
# Literal theta-cusp source weld for the tilt-flux route

The abstract tilt-flux carrier requires a positive even kernel with a pointwise envelope at every
exponential rate.  The arithmetic theta-cusp source was already known to have all exponential
moments and an all-plane Fourier--Laplace transform, but those statements did not instantiate the
stronger `ThetaSource` interface.

This module closes that source weld.  The explicit theta envelope and the elementary estimate
`exp (2t) >= 2t^2` give the global bound

`k(x) <= U exp ((|M|+5)^2/24) exp (-M|x|)`.

The resulting literal source has bilateral Laplace transform exactly `xiCent` on the whole plane.
Consequently the abstract source Bezoutian and neutral tilt-flux RH criteria now specialize with no
source-construction premise.  No flux sign or Riemann-hypothesis conclusion is asserted here.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Explicit constant for the theta-cusp envelope at arbitrary real exponential rate. -/
def thetaCuspTiltDecayConstant (M : ℝ) : ℝ :=
  thetaEnvelopeUpper * Real.exp ((|M| + 5) ^ 2 / 24)

theorem thetaCuspTiltDecayConstant_pos (M : ℝ) :
    0 < thetaCuspTiltDecayConstant M := by
  exact mul_pos thetaEnvelopeUpper_pos (Real.exp_pos _)

/-- **Global pointwise superexponential law.**  The literal completed theta source is dominated
by an explicit exponential envelope at every requested real rate. -/
theorem thetaCuspFullSource_le_tiltDecayConstant (M x : ℝ) :
    thetaCuspFullSource x ≤
      thetaCuspTiltDecayConstant M * Real.exp (-(M * |x|)) := by
  let A : ℝ := |M| + 5
  let t : ℝ := |x|
  have ht : 0 ≤ t := abs_nonneg x
  have hsourceAbs : thetaCuspFullSource x = thetaCuspFullSource t := by
    rcases le_total 0 x with hx | hx
    · simp [t, abs_of_nonneg hx]
    · rw [show x = -(-x) by ring, thetaCuspFullSource_neg]
      simp [t, abs_of_nonpos hx]
  have hsource := thetaCuspFullSource_le_envelope ht
  have hexpQuad : 2 * t ^ 2 ≤ Real.exp (2 * t) := by
    have h := Real.pow_div_factorial_le_exp
      (x := 2 * t) (show 0 ≤ 2 * t by positivity) 2
    norm_num at h ⊢
    nlinarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpiQuad : 6 * t ^ 2 ≤ Real.pi * Real.exp (2 * t) := by
    nlinarith [mul_le_mul_of_nonneg_left hexpQuad (show 0 ≤ Real.pi by positivity)]
  have hlinear : (M + 9 / 2) * t ≤ A * t := by
    have hM : M ≤ |M| := le_abs_self M
    dsimp only [A]
    nlinarith
  have hsquare : 0 ≤ (t - A / 12) ^ 2 := sq_nonneg _
  have hexponent :
      9 * t / 2 - Real.pi * Real.exp (2 * t) ≤ A ^ 2 / 24 - M * t := by
    nlinarith
  rw [hsourceAbs]
  calc
    thetaCuspFullSource t ≤ thetaEnvelopeUpper * thetaEnvelope t := hsource
    _ = thetaEnvelopeUpper * Real.exp
        (9 * t / 2 - Real.pi * Real.exp (2 * t)) := by
      rw [thetaEnvelope, ← Real.exp_add]
      ring_nf
    _ ≤ thetaEnvelopeUpper * Real.exp (A ^ 2 / 24 - M * t) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        thetaEnvelopeUpper_pos.le
    _ = thetaCuspTiltDecayConstant M * Real.exp (-(M * |x|)) := by
      dsimp only [thetaCuspTiltDecayConstant, A, t]
      rw [mul_assoc]
      rw [← Real.exp_add]
      congr 2

theorem thetaCuspFullSource_superexponential_envelope (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      thetaCuspFullSource x ≤ C * Real.exp (-(M * |x|)) := by
  exact ⟨thetaCuspTiltDecayConstant M, thetaCuspTiltDecayConstant_pos M,
    thetaCuspFullSource_le_tiltDecayConstant M⟩

/-- The literal completed theta-cusp density as an abstract tilt-flux source. -/
def thetaCuspTiltSource : ThetaSource where
  k := thetaCuspFullSource
  pos := thetaCuspFullSource_pos
  even' := thetaCuspFullSource_neg
  cont := contDiff_thetaCuspFullSource.continuous
  decay := thetaCuspFullSource_superexponential_envelope

@[simp] theorem thetaCuspTiltSource_k (x : ℝ) :
    thetaCuspTiltSource.k x = thetaCuspFullSource x := rfl

/-- **Global arithmetic source weld.**  The bilateral Laplace transform of the literal
theta-cusp tilt source is the centered completed Riemann function on all of `ℂ`. -/
theorem bilateralLaplace_thetaCuspTiltSource_eq_xiCent (w : ℂ) :
    bilateralLaplace thetaCuspTiltSource w = xiCent w := by
  rw [xiCent_eq_XiC, ← thetaCuspFourierLaplace_eq_XiC_all]
  rw [bilateralLaplace, thetaCuspFourierLaplace]
  have href := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ =>
      (thetaCuspTiltSource.k x : ℂ) * Complex.exp (w * (x : ℂ))) volume
  rw [← href]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [thetaCuspTiltSource_k, thetaCuspFullSource_neg]
  change
    (thetaCuspFullSource x : ℂ) * Complex.exp (w * ((-x : ℝ) : ℂ)) =
      Complex.exp (-I * (-I * w) * (x : ℂ)) * (thetaCuspFullSource x : ℂ)
  rw [mul_comm]
  congr 1
  apply congrArg Complex.exp
  calc
    w * ((-x : ℝ) : ℂ) = -(w * (x : ℂ)) := by push_cast; ring
    _ = ((-I) * (-I)) * w * (x : ℂ) := by
      rw [neg_mul_neg, I_mul_I]
      ring
    _ = -I * (-I * w) * (x : ℂ) := by ring

/-- The literal theta source Bezoutian is the centered-Xi Bezoutian wherever the divided
difference denominator is nonzero. -/
theorem sourceBezoutian_thetaCuspTiltSource_eq_xiCentBezoutian
    {w v : ℂ} (hne : w + conj v ≠ 0) :
    sourceBezoutian thetaCuspTiltSource w v =
      xiCentBezoutian w (conj v) := by
  exact sourceBezoutian_eq_xiCentBezoutian thetaCuspTiltSource
    bilateralLaplace_thetaCuspTiltSource_eq_xiCent hne

/-- Source-specialized Bezoutian criterion.  All construction premises have been discharged;
the remaining universal sign is exactly RH. -/
theorem riemannHypothesis_iff_thetaCuspTiltSource_sourceBezoutian_nonneg :
    RiemannHypothesis ↔
      ∀ (d : ℕ) (c w : Fin d → ℂ), (∀ j, 1 / 2 < (w j).re) →
        0 ≤ (∑ j, ∑ l, c j * conj (c l) *
          sourceBezoutian thetaCuspTiltSource (w j) (w l)).re := by
  exact riemannHypothesis_iff_sourceBezoutian_nonneg thetaCuspTiltSource
    bilateralLaplace_thetaCuspTiltSource_eq_xiCent

/-- **Literal theta-tilt frontier.**  Nonnegative neutral first variation of every one-sided
arithmetic theta correlation packet is exactly the Riemann hypothesis. -/
theorem riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg :
    RiemannHypothesis ↔
      ∀ (d : ℕ) (c w : Fin d → ℂ), (∀ j, 1 / 2 < (w j).re) → ∀ D : ℝ,
        HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0 → 0 ≤ D := by
  exact riemannHypothesis_iff_tiltFlux_nonneg thetaCuspTiltSource
    bilateralLaplace_thetaCuspTiltSource_eq_xiCent

end

end RHTower
