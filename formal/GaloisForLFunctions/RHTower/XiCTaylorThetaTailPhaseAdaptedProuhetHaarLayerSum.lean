import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetHalfLine
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailHaarResidualRankTwo

/-!
# The phase-adapted packet as an exact signed reflected Haar-layer sum

The coefficient packet is attached here to the actual finite reflected Haar prefixes.  Weighting
the depth-`N+j` prefix by `P_j q^j` preserves its exact rank-two form: the first source is the same
weighted residual whose fixed-half-line transform is cancelled by the self-consistent endpoint,
and the second source is the universal half-exponential seam.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

def thetaSquareIndexDyadicReflectedHaarPrefixSource
    (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    ((2 : ℝ) ^ (k + 1) *
        thetaSquareIndexDyadicOddLayer k
          (p.1 - thetaSquareIndexDyadicReflectionShift k) *
        thetaSquareIndexDyadicOddLayer k
          (p.2 - thetaSquareIndexDyadicReflectionShift k) -
      (2 : ℝ) ^ k *
        thetaSquareIndexDyadicParityLayer k (-p.1) *
        thetaSquareIndexDyadicParityLayer k (-p.2))

def phaseAdaptedWeightedHaarResidualSource
    (P : ℝ[X]) (q : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  P.sum fun j c =>
    (c * q ^ j) * thetaSquareIndexDyadicHaarResidual (N + j) x

def phaseAdaptedWeightedReflectedHaarPrefixSource
    (P : ℝ[X]) (q : ℝ) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  P.sum fun j c =>
    (c * q ^ j) *
      thetaSquareIndexDyadicReflectedHaarPrefixSource (N + j) p

/-- A finite coefficient combination of reflected Haar prefixes remains one symmetric rank-two
source tensor. -/
theorem phaseAdaptedWeightedReflectedHaarPrefixSource_eq_rankTwo
    (P : ℝ[X]) (q : ℝ) (N : ℕ) (x y : ℝ) :
    phaseAdaptedWeightedReflectedHaarPrefixSource P q N (x, y) =
      (1 / 2 : ℝ) *
        (phaseAdaptedWeightedHaarResidualSource P q N x *
            Real.exp (-y / 2) +
          Real.exp (-x / 2) *
            phaseAdaptedWeightedHaarResidualSource P q N y) := by
  unfold phaseAdaptedWeightedReflectedHaarPrefixSource
    phaseAdaptedWeightedHaarResidualSource Polynomial.sum
  calc
    (∑ j ∈ P.support,
        (P.coeff j * q ^ j) *
          thetaSquareIndexDyadicReflectedHaarPrefixSource (N + j) (x, y)) =
      ∑ j ∈ P.support,
        (P.coeff j * q ^ j) *
          ((1 / 2 : ℝ) *
            (thetaSquareIndexDyadicHaarResidual (N + j) x *
                Real.exp (-y / 2) +
              Real.exp (-x / 2) *
                thetaSquareIndexDyadicHaarResidual (N + j) y)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [thetaSquareIndexDyadicReflectedHaarPrefixSource,
          thetaSquareIndexDyadicHaarLayer_reflected_sum_eq_rankTwoResidual]
    _ = ∑ j ∈ P.support, (1 / 2 : ℝ) *
        (((P.coeff j * q ^ j) *
            thetaSquareIndexDyadicHaarResidual (N + j) x) *
              Real.exp (-y / 2) +
          Real.exp (-x / 2) *
            ((P.coeff j * q ^ j) *
              thetaSquareIndexDyadicHaarResidual (N + j) y)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
    _ = (1 / 2 : ℝ) * ∑ j ∈ P.support,
        (((P.coeff j * q ^ j) *
            thetaSquareIndexDyadicHaarResidual (N + j) x) *
              Real.exp (-y / 2) +
          Real.exp (-x / 2) *
            ((P.coeff j * q ^ j) *
              thetaSquareIndexDyadicHaarResidual (N + j) y)) := by
        rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

/-- The one-variable source in the weighted Haar tensor is exactly the corrected phase-adapted
fixed-half-line source. -/
theorem phaseAdaptedWeightedHaarResidualSource_eq_source
    (P : ℝ[X]) (tau : ℝ) (N : ℕ) (x : ℝ)
    (hq : P.eval dyadicProuhetDecayCharacter = 1)
    (hr : P.eval dyadicProuhetGrowthCharacter = tau) :
    phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x =
      dyadicEvenRemoteAmplitude N *
          (∑ j ∈ P.support, P.coeff j *
            thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
        thetaCuspTailSecondDensity x +
        (((2 : ℝ) ^ N * tau + 1) / 4) * Real.exp (-x / 2) := by
  simpa only [phaseAdaptedWeightedHaarResidualSource, Polynomial.sum] using
    weighted_thetaSquareIndexDyadicHaarResidual_eq_phaseAdaptedSource
      P tau N x hq hr

/-- Canonical strip specialization: both endpoint normalizations required by the weighted Haar
sum hold for the phase-adapted packet. -/
theorem canonicalPhaseAdaptedWeightedHaarResidualSource_eq_source
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (tau : ℝ) (x : ℝ) :
    let u := spectralTranslationPhase (Real.log 2) z
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u
      dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau
    phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x =
      dyadicEvenRemoteAmplitude N *
          (∑ j ∈ P.support, P.coeff j *
            thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
        thetaCuspTailSecondDensity x +
        (((2 : ℝ) ^ N * tau + 1) / 4) * Real.exp (-x / 2) := by
  dsimp only
  let u := spectralTranslationPhase (Real.log 2) z
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u
    dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau
  have hBq := phaseAdaptedProuhetBase_eval_dyadicDecay_ne_zero m hzHalf
  have hBr := phaseAdaptedProuhetBase_eval_dyadicGrowth_ne_zero m hz0
  have hsep : dyadicProuhetGrowthCharacter -
      dyadicProuhetDecayCharacter ≠ 0 :=
    sub_ne_zero.mpr dyadicProuhetDecayCharacter_ne_growthCharacter.symm
  have hq : P.eval dyadicProuhetDecayCharacter = 1 := by
    exact phaseAdaptedTwoEndpointProuhetPolynomial_eval_left m u hBq
  have hr : P.eval dyadicProuhetGrowthCharacter = tau := by
    exact phaseAdaptedTwoEndpointProuhetPolynomial_eval_right m u hBr hsep
  exact phaseAdaptedWeightedHaarResidualSource_eq_source P tau N x hq hr

end

end RHTower
