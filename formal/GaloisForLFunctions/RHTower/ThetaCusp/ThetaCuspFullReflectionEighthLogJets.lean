import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenEighthJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthLogJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSeventhEighthSourceJets

/-!
# Exact seventh and eighth logarithmic jets of the complete theta source

The first Born--Witten factor and higher-likelihood partition now both have literal jets through
order eight.  This module identifies their sum with the actual complete-source logarithmic
derivatives and records the normalized rank-three reflected-Hankel polynomial.  Its positivity
is precisely global D1; no sign is assumed here.
-/

namespace RHTower

noncomputable section

/-- Seventh logarithmic jet of the complete theta source in first-atom/source coordinates. -/
def thetaCuspFullLogJetSeven (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogSeventhDerivative 1 x +
    thetaCuspLikelihoodSourceLogPartitionJetSeven x

/-- Eighth logarithmic jet of the complete theta source in first-atom/source coordinates. -/
def thetaCuspFullLogJetEight (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogEighthDerivative 1 x +
    thetaCuspLikelihoodSourceLogPartitionJetEight x

/-- Exact seventh logarithmic derivative of the actual complete theta source. -/
theorem iteratedDeriv_seven_thetaCuspLogSource_eq_full_jets
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 7 thetaCuspLogSource x = thetaCuspFullLogJetSeven x := by
  have heq : iteratedDeriv 6 thetaCuspLogSource =ᶠ[nhds x]
      thetaCuspFullLogJetSix := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_six_thetaCuspLogSource_eq_full_jets hy
  have hfirst :=
    (hasDerivAt_thetaCuspBornWittenLogSixthDerivative
      (n := 1) (by norm_num) hx.le).neg
  have hhigher :=
    hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSix hx.le
  have hfull : HasDerivAt thetaCuspFullLogJetSix
      (thetaCuspFullLogJetSeven x) x := by
    unfold thetaCuspFullLogJetSix thetaCuspFullLogJetSeven
    exact hfirst.add hhigher
  rw [show 7 = 6 + 1 by norm_num, iteratedDeriv_succ]
  exact (hfull.congr_of_eventuallyEq heq).deriv

/-- Exact eighth logarithmic derivative of the actual complete theta source. -/
theorem iteratedDeriv_eight_thetaCuspLogSource_eq_full_jets
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 8 thetaCuspLogSource x = thetaCuspFullLogJetEight x := by
  have heq : iteratedDeriv 7 thetaCuspLogSource =ᶠ[nhds x]
      thetaCuspFullLogJetSeven := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_seven_thetaCuspLogSource_eq_full_jets hy
  have hfirst :=
    (hasDerivAt_thetaCuspBornWittenLogSeventhDerivative
      (n := 1) (by norm_num) hx.le).neg
  have hhigher :=
    hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSeven hx.le
  have hfull : HasDerivAt thetaCuspFullLogJetSeven
      (thetaCuspFullLogJetEight x) x := by
    unfold thetaCuspFullLogJetSeven thetaCuspFullLogJetEight
    exact hfirst.add hhigher
  rw [show 8 = 7 + 1 by norm_num, iteratedDeriv_succ]
  exact (hfull.congr_of_eventuallyEq heq).deriv

/-- Positive-coordinate form of negative eighth logarithmic source jet. -/
def thetaCuspFullReflectedLogEighthJet (x : ℝ) : ℝ :=
  thetaCuspBornWittenLogEighthDerivative 1 x -
    thetaCuspLikelihoodSourceLogPartitionJetEight x

/-- Normalized rank-three reflected-Hankel polynomial of the complete theta source. -/
def thetaCuspFullReflectionEighthHankelCurvature (x : ℝ) : ℝ :=
  let A := thetaCuspFullReflectedLogCurvature x
  let B := thetaCuspFullReflectedLogFourthJet x
  let C := thetaCuspFullReflectedLogSixthJet x
  let D := thetaCuspFullReflectedLogEighthJet x
  768 * A ^ (6 : ℕ) - 1344 * A ^ (4 : ℕ) * B + 304 * A ^ (2 : ℕ) * B ^ (2 : ℕ) -
    68 * B ^ (3 : ℕ) + 128 * A ^ (3 : ℕ) * C - 4 * A ^ (2 : ℕ) * D + B * D - C ^ (2 : ℕ)

/-- The exact even-log rank-three polynomial is the native complete-source curvature. -/
theorem thetaCuspLogSource_eighthHankel_eq_fullReflectionEighthCurvature
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 4 thetaCuspLogSource x *
          iteratedDeriv 8 thetaCuspLogSource x -
        iteratedDeriv 6 thetaCuspLogSource x ^ (2 : ℕ) +
      4 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 8 thetaCuspLogSource x +
      128 * iteratedDeriv 2 thetaCuspLogSource x ^ (3 : ℕ) *
        iteratedDeriv 6 thetaCuspLogSource x +
      68 * iteratedDeriv 4 thetaCuspLogSource x ^ (3 : ℕ) +
      304 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 4 thetaCuspLogSource x ^ (2 : ℕ) +
      1344 * iteratedDeriv 2 thetaCuspLogSource x ^ (4 : ℕ) *
        iteratedDeriv 4 thetaCuspLogSource x +
      768 * iteratedDeriv 2 thetaCuspLogSource x ^ (6 : ℕ) =
    thetaCuspFullReflectionEighthHankelCurvature x := by
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx,
    iteratedDeriv_four_thetaCuspLogSource_eq_factor hx,
    iteratedDeriv_six_thetaCuspLogSource_eq_full_jets hx,
    iteratedDeriv_eight_thetaCuspLogSource_eq_full_jets hx,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx,
    ← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx]
  unfold thetaCuspFullLogJetSix thetaCuspFullLogJetEight
    thetaCuspFullReflectionEighthHankelCurvature
    thetaCuspFullReflectedLogCurvature thetaCuspFullReflectedLogFourthJet
    thetaCuspFullReflectedLogSixthJet thetaCuspFullReflectedLogEighthJet
  ring

end

end RHTower
