import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBalancedGammaPhaseOrderRigidity

/-!
# FZZ balanced external-Gamma Ward-delay rigidity

The complete balanced external-Gamma amplitude is pointwise recurrent, while its unwrapped phase
is globally order-rigid.  This file removes the remaining phase-unwrapping burden.  The local phase
derivative with respect to physical continuum momentum is branch-independent and has a unique
global minimum at the vacuum momentum.

The first two Gauss-digamma increments exactly cancel the two rational arctangent losses, as in the
imported non-strict minimum theorem.  Retaining the next Gauss atom leaves the explicit positive
margin

`8 y² / (5 * (25 + 4 y²))`.

Thus the local Ward delay equals its vacuum value exactly at zero radial momentum, equivalently at
linear replica-area passivity.  Requiring vacuum-delay saturation on every literal parity-Mellin
divisor mode is therefore equivalent to RH.  The still-open physical edge is source-dynamical:
derive that saturation from the integrated replica Ward law.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Strict form of balanced Gamma-phase slope rigidity.  The `n=2` Gauss atom is strictly positive
away from the radial wall after the first two atoms cancel both rational-shift losses. -/
theorem fzzHJBalancedExternalGammaPhaseSlope_zero_lt
    {y : ℝ} (hy : y ≠ 0) :
    fzzHJBalancedExternalGammaPhaseSlope 0 <
      fzzHJBalancedExternalGammaPhaseSlope y := by
  let term0 : ℕ → ℝ := fun n =>
    (gaussDigammaSeriesTerm ((1 / 2 : ℝ) : ℂ) n).re
  let termy : ℕ → ℝ := fun n =>
    (gaussDigammaSeriesTerm
      (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) n).re
  have hsum0 : Summable term0 := summable_re_gaussDigammaSeriesTerm _
  have hsumy : Summable termy := summable_re_gaussDigammaSeriesTerm _
  have hterm : ∀ n : ℕ, 0 ≤ termy n - term0 n := by
    intro n
    exact sub_nonneg.mpr (re_gaussDigammaSeriesTerm_real_le (by norm_num) y n)
  have hsumdiff : Summable (fun n => termy n - term0 n) := hsumy.sub hsum0
  have hpartial := hsumdiff.sum_le_tsum (Finset.range 3) (fun n _ => hterm n)
  have hfinite :
      ∑ n ∈ Finset.range 3, (termy n - term0 n) =
        (2 - 2 / (1 + 4 * y ^ (2 : ℕ))) +
          (2 / 3 - 6 / (9 + 4 * y ^ (2 : ℕ))) +
            8 * y ^ (2 : ℕ) / (5 * (25 + 4 * y ^ (2 : ℕ))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    dsimp [termy, term0]
    rw [re_gaussDigammaSeriesTerm_vertical, re_gaussDigammaSeriesTerm_vertical,
      re_gaussDigammaSeriesTerm_vertical]
    have hzero0 :
        (gaussDigammaSeriesTerm ((1 / 2 : ℝ) : ℂ) 0).re =
          1 / ((0 : ℝ) + 1) - ((1 / 2 : ℝ) + 0) /
            (((1 / 2 : ℝ) + 0) ^ (2 : ℕ) + (0 : ℝ) ^ (2 : ℕ)) := by
      simpa using re_gaussDigammaSeriesTerm_vertical (1 / 2) 0 0
    have hzero1 :
        (gaussDigammaSeriesTerm ((1 / 2 : ℝ) : ℂ) 1).re =
          1 / ((1 : ℝ) + 1) - ((1 / 2 : ℝ) + 1) /
            (((1 / 2 : ℝ) + 1) ^ (2 : ℕ) + (0 : ℝ) ^ (2 : ℕ)) := by
      simpa using re_gaussDigammaSeriesTerm_vertical (1 / 2) 0 1
    have hzero2 :
        (gaussDigammaSeriesTerm ((1 / 2 : ℝ) : ℂ) 2).re =
          1 / ((2 : ℝ) + 1) - ((1 / 2 : ℝ) + 2) /
            (((1 / 2 : ℝ) + 2) ^ (2 : ℕ) + (0 : ℝ) ^ (2 : ℕ)) := by
      simpa using re_gaussDigammaSeriesTerm_vertical (1 / 2) 0 2
    rw [hzero0, hzero1, hzero2]
    have hden1 : 0 < 1 + 4 * y ^ (2 : ℕ) := by positivity
    have hden9 : 0 < 9 + 4 * y ^ (2 : ℕ) := by positivity
    have hden25 : 0 < 25 + 4 * y ^ (2 : ℕ) := by positivity
    norm_num
    field_simp [hden1.ne', hden9.ne', hden25.ne']
    ring
  have hstrict : 0 < 8 * y ^ (2 : ℕ) / (5 * (25 + 4 * y ^ (2 : ℕ))) := by
    positivity
  have hdiff : ∑' n : ℕ, (termy n - term0 n) =
      (∑' n : ℕ, termy n) - ∑' n : ℕ, term0 n :=
    (hsumy.hasSum.sub hsum0.hasSum).tsum_eq
  rw [hfinite, hdiff] at hpartial
  have hyDigamma := re_digamma_vertical_eq (a := (1 / 2 : ℝ)) (by norm_num) y
  have hzeroDigamma := re_digamma_vertical_eq (a := (1 / 2 : ℝ)) (by norm_num) 0
  rw [fzzHJBalancedExternalGammaPhaseSlope,
    fzzHJBalancedExternalGammaPhaseSlope]
  rw [hyDigamma, hzeroDigamma]
  dsimp [termy, term0] at hpartial
  norm_num at hpartial ⊢
  linarith

/-- Branch-independent local derivative of the balanced external-Gamma phase with respect to
physical continuum momentum. -/
def fzzHJBalancedExternalGammaWardDelay (P : ℝ) : ℝ :=
  4 * Real.sqrt 2 *
    fzzHJBalancedExternalGammaPhaseSlope (Real.sqrt 2 * P)

/-- The local Ward delay is the exact physical-momentum derivative of the balanced phase. -/
theorem hasDerivAt_fzzHJBalancedExternalGammaMomentumPhase (P : ℝ) :
    HasDerivAt
      (fun Q : ℝ =>
        fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * Q))
      (fzzHJBalancedExternalGammaWardDelay P) P := by
  have hinner : HasDerivAt (fun Q : ℝ => Real.sqrt 2 * Q) (Real.sqrt 2) P := by
    simpa using (hasDerivAt_id P).const_mul (Real.sqrt 2)
  have hcomp :=
    (hasDerivAt_fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * P)).comp P hinner
  simpa [Function.comp_def, fzzHJBalancedExternalGammaWardDelay, mul_comm,
    mul_left_comm, mul_assoc] using hcomp

/-- Away from zero momentum, local balanced Gamma Ward delay strictly exceeds vacuum delay. -/
theorem fzzHJBalancedExternalGammaWardDelay_zero_lt
    {P : ℝ} (hP : P ≠ 0) :
    fzzHJBalancedExternalGammaWardDelay 0 <
      fzzHJBalancedExternalGammaWardDelay P := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have harg : Real.sqrt 2 * P ≠ 0 := mul_ne_zero hsqrt.ne' hP
  have hcoef : 0 < 4 * Real.sqrt 2 := mul_pos (by norm_num) hsqrt
  simpa [fzzHJBalancedExternalGammaWardDelay] using
    (mul_lt_mul_of_pos_left
      (fzzHJBalancedExternalGammaPhaseSlope_zero_lt harg) hcoef)

/-- Local balanced Gamma Ward delay saturates its vacuum floor only at zero momentum. -/
theorem fzzHJBalancedExternalGammaWardDelay_eq_vacuum_iff (P : ℝ) :
    fzzHJBalancedExternalGammaWardDelay P =
        fzzHJBalancedExternalGammaWardDelay 0 ↔
      P = 0 := by
  constructor
  · intro h
    by_contra hP
    exact (fzzHJBalancedExternalGammaWardDelay_zero_lt hP).ne' h
  · rintro rfl
    rfl

/-- Exact local, branch-independent Ward-delay bridge into FZZ linear replica-area passivity. -/
theorem fzzHJBalancedExternalGammaWardDelay_eq_vacuum_iff_passive (P : ℝ) :
    fzzHJBalancedExternalGammaWardDelay P =
        fzzHJBalancedExternalGammaWardDelay 0 ↔
      fzzLinearReplicaAreaNormalizedResponse 1 P ≤ 1 := by
  rw [fzzHJBalancedExternalGammaWardDelay_eq_vacuum_iff,
    fzzLinearReplicaAreaNormalizedResponse_le_one_iff (n := 1) (by norm_num)]

/-- Source-facing local FZZ premise: every literal parity-Mellin divisor mode saturates the vacuum
balanced-Gamma Ward delay. -/
def FZZBalancedExternalGammaWardDelayDivisorSaturated : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    fzzHJBalancedExternalGammaWardDelay
        (fzzCigarParityMellinTorusTwist rho).im =
      fzzHJBalancedExternalGammaWardDelay 0

/-- Vacuum Ward-delay saturation and linear replica-area passivity are the same divisor premise. -/
theorem fzzBalancedExternalGammaWardDelayDivisorSaturated_iff_passive :
    FZZBalancedExternalGammaWardDelayDivisorSaturated ↔
      FZZLinearReplicaAreaDivisorPassive := by
  constructor
  · intro h rho h0 h1 hmode
    exact (fzzHJBalancedExternalGammaWardDelay_eq_vacuum_iff_passive _).mp
      (h rho h0 h1 hmode)
  · intro h rho h0 h1 hmode
    exact (fzzHJBalancedExternalGammaWardDelay_eq_vacuum_iff_passive _).mpr
      (h rho h0 h1 hmode)

/-- Exact local Ward-delay FZZ-P endpoint.  The remaining burden is to derive vacuum saturation
from literal source dynamics, not to choose a phase branch or reconstruct phase history. -/
theorem fzzBalancedExternalGammaWardDelayDivisorSaturated_iff_riemannHypothesis :
    FZZBalancedExternalGammaWardDelayDivisorSaturated ↔ RiemannHypothesis :=
  fzzBalancedExternalGammaWardDelayDivisorSaturated_iff_passive.trans
    fzzLinearReplicaAreaDivisorPassive_iff_riemannHypothesis

end

end RHTower
