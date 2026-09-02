import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBalancedGammaPhaseRecurrenceNoGo
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum
import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth
import GaloisForLFunctions.RHTower.SeamDivisionSourceSplit
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseFirstTailBarrier

/-!
# FZZ balanced external-Gamma phase order rigidity

The complete balanced external-leg amplitude is recurrent and cannot detect replica-area passivity
pointwise.  Its unwrapped phase retains exactly the missing order information.  At physical level
`k = 4`, the first two terms of the Gauss digamma series exactly pay for the derivative losses of
the two rational-shift arctangent phases.  All remaining Gauss terms are nonnegative.  The slope is
therefore bounded below by its value at zero,

`ψ(1/2) + 8/3 = 8/3 - EulerGamma - 2 log 2 > 0`.

Consequently the balanced phase lift is strictly increasing, vanishes only at zero momentum, and
its zero-phase condition is equivalent to linear replica-area passivity.  This closes the
phase-to-passivity edge of the FZZ-P chain; the surviving source burden is to derive zero unwrapped
phase from the replica Ward dynamics.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Derivative of one quarter of the balanced external-Gamma phase lift. -/
def fzzHJBalancedExternalGammaPhaseSlope (y : ℝ) : ℝ :=
  (Complex.digamma ((1 / 2 : ℝ) + (y : ℂ) * Complex.I)).re
    + 2 / (1 + 4 * y ^ 2) + 6 / (9 + 4 * y ^ 2)

/-- The balanced phase slope is positive at the zero-momentum wall. -/
theorem fzzHJBalancedExternalGammaPhaseSlope_zero_pos :
    0 < fzzHJBalancedExternalGammaPhaseSlope 0 := by
  have hhalf := congrArg Complex.re GaloisForLFunctions.SeamSplit.digamma_half
  norm_num [Complex.log_ofReal_re] at hhalf
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 :=
    Complex.log_ofReal_re 2
  rw [hlogre] at hhalf
  have hgamma := RiemannGaussian.eulerMascheroniConstant_lt_29_over_50
  have hlog := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)
  rw [fzzHJBalancedExternalGammaPhaseSlope]
  norm_num
  rw [hhalf]
  linarith

/-- The first two Gauss-digamma atoms exactly cancel the two rational-shift slope losses, so the
balanced phase slope is globally minimized at zero. -/
theorem fzzHJBalancedExternalGammaPhaseSlope_zero_le (y : ℝ) :
    fzzHJBalancedExternalGammaPhaseSlope 0 ≤
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
  have hpartial := hsumdiff.sum_le_tsum (Finset.range 2) (fun n _ => hterm n)
  have hfinite :
      ∑ n ∈ Finset.range 2, (termy n - term0 n) =
        (2 - 2 / (1 + 4 * y ^ 2)) + (2 / 3 - 6 / (9 + 4 * y ^ 2)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    dsimp [termy, term0]
    rw [re_gaussDigammaSeriesTerm_vertical, re_gaussDigammaSeriesTerm_vertical]
    have hzero0 :
        (gaussDigammaSeriesTerm ((1 / 2 : ℝ) : ℂ) 0).re =
          1 / ((0 : ℝ) + 1) - ((1 / 2 : ℝ) + 0) /
            (((1 / 2 : ℝ) + 0) ^ 2 + (0 : ℝ) ^ 2) := by
      simpa using re_gaussDigammaSeriesTerm_vertical (1 / 2) 0 0
    have hzero1 :
        (gaussDigammaSeriesTerm ((1 / 2 : ℝ) : ℂ) 1).re =
          1 / ((1 : ℝ) + 1) - ((1 / 2 : ℝ) + 1) /
            (((1 / 2 : ℝ) + 1) ^ 2 + (0 : ℝ) ^ 2) := by
      simpa using re_gaussDigammaSeriesTerm_vertical (1 / 2) 0 1
    rw [hzero0, hzero1]
    have hden1 : 0 < 1 + 4 * y ^ 2 := by positivity
    have hden9 : 0 < 9 + 4 * y ^ 2 := by positivity
    norm_num
    field_simp [hden1.ne', hden9.ne']
    ring
  have hdiff : ∑' n : ℕ, (termy n - term0 n) =
      (∑' n : ℕ, termy n) - ∑' n : ℕ, term0 n :=
    (hsumy.hasSum.sub hsum0.hasSum).tsum_eq
  rw [hfinite, hdiff] at hpartial
  have hy := re_digamma_vertical_eq (a := (1 / 2 : ℝ)) (by norm_num) y
  have hzero := re_digamma_vertical_eq (a := (1 / 2 : ℝ)) (by norm_num) 0
  change fzzHJBalancedExternalGammaPhaseSlope 0 ≤
    fzzHJBalancedExternalGammaPhaseSlope y
  rw [fzzHJBalancedExternalGammaPhaseSlope, fzzHJBalancedExternalGammaPhaseSlope]
  rw [hy, hzero]
  dsimp [termy, term0] at hpartial
  norm_num at hpartial ⊢
  linarith

/-- Global strict positivity of the balanced external-Gamma phase slope. -/
theorem fzzHJBalancedExternalGammaPhaseSlope_pos (y : ℝ) :
    0 < fzzHJBalancedExternalGammaPhaseSlope y :=
  fzzHJBalancedExternalGammaPhaseSlope_zero_pos.trans_le
    (fzzHJBalancedExternalGammaPhaseSlope_zero_le y)

/-- Exact derivative of the balanced external-Gamma phase lift. -/
theorem hasDerivAt_fzzHJBalancedExternalGammaPhaseLift (y : ℝ) :
    HasDerivAt fzzHJBalancedExternalGammaPhaseLift
      (4 * fzzHJBalancedExternalGammaPhaseSlope y) y := by
  have hphase := hasDerivAt_gammaVerticalPhase
    (show (0 : ℝ) < 1 / 2 by norm_num) y
  have htwo : HasDerivAt (fun x : ℝ => Real.arctan (2 * x))
      (2 / (1 + 4 * y ^ 2)) y := by
    convert ((hasDerivAt_id y).const_mul 2).arctan using 1
    · funext x
      simp only [id_eq]
    · simp only [id_eq]
      ring
  have htwoThirds : HasDerivAt (fun x : ℝ => Real.arctan (2 * x / 3))
      (6 / (9 + 4 * y ^ 2)) y := by
    convert ((hasDerivAt_id y).const_mul (2 / 3)).arctan using 1
    · funext x
      simp only [id_eq]
      ring
    · field_simp
      simp only [id_eq]
      ring
  unfold fzzHJBalancedExternalGammaPhaseLift
  rw [fzzHJBalancedExternalGammaPhaseSlope]
  simpa only [Pi.add_apply] using
    ((hphase.add htwo).add htwoThirds).const_mul 4

/-- The unwrapped balanced external-Gamma phase is globally strictly increasing. -/
theorem fzzHJBalancedExternalGammaPhaseLift_strictMono :
    StrictMono fzzHJBalancedExternalGammaPhaseLift := by
  apply strictMono_of_deriv_pos
  intro y
  rw [(hasDerivAt_fzzHJBalancedExternalGammaPhaseLift y).deriv]
  exact mul_pos (by norm_num) (fzzHJBalancedExternalGammaPhaseSlope_pos y)

@[simp] theorem fzzHJBalancedExternalGammaPhaseLift_zero :
    fzzHJBalancedExternalGammaPhaseLift 0 = 0 := by
  simp [fzzHJBalancedExternalGammaPhaseLift, gammaVerticalPhase]

/-- The unwrapped balanced phase vanishes only at zero radial frequency. -/
theorem fzzHJBalancedExternalGammaPhaseLift_eq_zero_iff (y : ℝ) :
    fzzHJBalancedExternalGammaPhaseLift y = 0 ↔ y = 0 := by
  constructor
  · intro h
    apply fzzHJBalancedExternalGammaPhaseLift_strictMono.injective
    simpa using h
  · rintro rfl
    exact fzzHJBalancedExternalGammaPhaseLift_zero

/-- At physical level `k = 4`, zero balanced phase is exactly zero HJ continuum momentum. -/
theorem fzzHJBalancedExternalGammaPhaseLift_momentum_eq_zero_iff (P : ℝ) :
    fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * P) = 0 ↔ P = 0 := by
  rw [fzzHJBalancedExternalGammaPhaseLift_eq_zero_iff]
  exact mul_eq_zero_iff_left (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

/-- Exact phase-order bridge into FZZ linear replica-area passivity. -/
theorem fzzHJBalancedExternalGammaPhaseLift_eq_zero_iff_passive (P : ℝ) :
    fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * P) = 0 ↔
      fzzLinearReplicaAreaNormalizedResponse 1 P ≤ 1 := by
  rw [fzzHJBalancedExternalGammaPhaseLift_momentum_eq_zero_iff,
    fzzLinearReplicaAreaNormalizedResponse_le_one_iff (n := 1) (by norm_num)]

end

end RHTower
