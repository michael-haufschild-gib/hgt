import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthMixture
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthCompleteSpectralBound

/-!
# Exact fifth and sixth logarithmic jets of the complete theta source

The higher likelihood factor already has a source-coordinate cumulant ladder through order six.
This file identifies that ladder with the actual logarithmic derivatives of the complete theta
source.  Consequently the order-six reflected Hankel polynomial is expressed entirely in the
first Born--Witten atom and literal higher-source cumulants.
-/

namespace RHTower

noncomputable section

/-- Fifth logarithmic jet of the complete theta source in first-atom/source coordinates. -/
def thetaCuspFullLogJetFive (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogFifthDerivative 1 x +
    thetaCuspLikelihoodSourceLogPartitionJetFive x

/-- Sixth logarithmic jet of the complete theta source in first-atom/source coordinates. -/
def thetaCuspFullLogJetSix (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogSixthDerivative 1 x +
    thetaCuspLikelihoodSourceLogPartitionJetSix x

/-- Exact fifth logarithmic derivative of the actual complete theta source. -/
theorem iteratedDeriv_five_thetaCuspLogSource_eq_full_jets
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 5 thetaCuspLogSource x = thetaCuspFullLogJetFive x := by
  have heq : iteratedDeriv 4 thetaCuspLogSource =ᶠ[nhds x]
      (fun y : ℝ =>
        -thetaCuspBornWittenLogFourthDerivative 1 y +
          thetaCuspLikelihoodSourceLogPartitionJetFour y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [iteratedDeriv_four_thetaCuspLogSource_eq_factor hy,
      thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hy]
  have hfirst :=
    (hasDerivAt_thetaCuspBornWittenLogFourthDerivative
      (n := 1) (by norm_num) hx.le).neg
  have hhigher := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour
    (thetaCuspLikelihoodCoordinate_pos hx.le)
  rw [show 5 = 4 + 1 by norm_num, iteratedDeriv_succ]
  exact ((hfirst.add hhigher).congr_of_eventuallyEq heq).deriv

/-- Exact sixth logarithmic derivative of the actual complete theta source. -/
theorem iteratedDeriv_six_thetaCuspLogSource_eq_full_jets
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 6 thetaCuspLogSource x = thetaCuspFullLogJetSix x := by
  have heq : iteratedDeriv 5 thetaCuspLogSource =ᶠ[nhds x]
      thetaCuspFullLogJetFive := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_five_thetaCuspLogSource_eq_full_jets hy
  have hfirst :=
    (hasDerivAt_thetaCuspBornWittenLogFifthDerivative
      (n := 1) (by norm_num) hx.le).neg
  have hhigher := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive
    (thetaCuspLikelihoodCoordinate_pos hx.le)
  have hfull : HasDerivAt thetaCuspFullLogJetFive
      (thetaCuspFullLogJetSix x) x := by
    unfold thetaCuspFullLogJetFive thetaCuspFullLogJetSix
    exact hfirst.add hhigher
  rw [show 6 = 5 + 1 by norm_num, iteratedDeriv_succ]
  exact (hfull.congr_of_eventuallyEq heq).deriv

/-- Positive-coordinate form of the actual second logarithmic source jet. -/
def thetaCuspFullReflectedLogCurvature (x : ℝ) : ℝ :=
  thetaCuspBornWittenLogCurvature 1 x -
    thetaCuspLikelihoodSourceLogPartitionJetTwo x

/-- Positive-coordinate form of the actual fourth logarithmic source jet. -/
def thetaCuspFullReflectedLogFourthJet (x : ℝ) : ℝ :=
  thetaCuspBornWittenLogFourthDerivative 1 x -
    thetaCuspLikelihoodSourceLogPartitionJetFour x

/-- Positive-coordinate form of the actual sixth logarithmic source jet. -/
def thetaCuspFullReflectedLogSixthJet (x : ℝ) : ℝ :=
  thetaCuspBornWittenLogSixthDerivative 1 x -
    thetaCuspLikelihoodSourceLogPartitionJetSix x

/-- Literal order-six reflected Hankel source polynomial for the complete theta source. -/
def thetaCuspFullReflectionSixthCurvature (x : ℝ) : ℝ :=
  let A := thetaCuspFullReflectedLogCurvature x
  let B := thetaCuspFullReflectedLogFourthJet x
  let C := thetaCuspFullReflectedLogSixthJet x
  A * C - B ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * B + 24 * A ^ (4 : ℕ)

/-- The abstract logarithmic order-six Hankel polynomial is exactly the native source
curvature. -/
theorem thetaCuspLogSource_secondSixthHankel_eq_fullReflectionSixthCurvature
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 thetaCuspLogSource x *
          iteratedDeriv 6 thetaCuspLogSource x -
        iteratedDeriv 4 thetaCuspLogSource x ^ (2 : ℕ) +
        18 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) *
          iteratedDeriv 4 thetaCuspLogSource x +
        24 * iteratedDeriv 2 thetaCuspLogSource x ^ (4 : ℕ) =
      thetaCuspFullReflectionSixthCurvature x := by
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx,
    iteratedDeriv_four_thetaCuspLogSource_eq_factor hx,
    iteratedDeriv_six_thetaCuspLogSource_eq_full_jets hx,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx,
    ← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx]
  unfold thetaCuspFullLogJetSix thetaCuspFullReflectionSixthCurvature
    thetaCuspFullReflectedLogCurvature thetaCuspFullReflectedLogFourthJet
    thetaCuspFullReflectedLogSixthJet
  ring

end

end RHTower
