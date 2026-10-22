import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthBellTransfer
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthLogJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthHankelSeam

/-!
# Exact real exponential Bell transfer through order eight

The complete theta source is globally positive, hence is the exponential of its logarithmic
source.  The order-six transfer is extended through the seventh and eighth Bell jets.  This
identifies the native signed `3 × 3` reflected Hankel determinant with the positive sixth power
of the exact normalized D1 curvature on the positive half-line.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- Seventh real exponential Bell jet of the complete theta logarithmic source. -/
def thetaCuspLogExponentialJetSeven (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x *
    (iteratedDeriv 1 thetaCuspLogSource x ^ (7 : ℕ) +
      21 * iteratedDeriv 1 thetaCuspLogSource x ^ (5 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x +
      105 * iteratedDeriv 1 thetaCuspLogSource x ^ (3 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) +
      105 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x ^ (3 : ℕ) +
      35 * iteratedDeriv 1 thetaCuspLogSource x ^ (4 : ℕ) *
        iteratedDeriv 3 thetaCuspLogSource x +
      210 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x +
      105 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 3 thetaCuspLogSource x +
      70 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x ^ (2 : ℕ) +
      35 * iteratedDeriv 1 thetaCuspLogSource x ^ (3 : ℕ) *
        iteratedDeriv 4 thetaCuspLogSource x +
      105 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 4 thetaCuspLogSource x +
      35 * iteratedDeriv 3 thetaCuspLogSource x *
        iteratedDeriv 4 thetaCuspLogSource x +
      21 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 5 thetaCuspLogSource x +
      21 * iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 5 thetaCuspLogSource x +
      7 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 6 thetaCuspLogSource x +
      iteratedDeriv 7 thetaCuspLogSource x)

/-- Eighth real exponential Bell jet of the complete theta logarithmic source. -/
def thetaCuspLogExponentialJetEight (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x *
    (iteratedDeriv 1 thetaCuspLogSource x ^ (8 : ℕ) +
      28 * iteratedDeriv 1 thetaCuspLogSource x ^ (6 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x +
      210 * iteratedDeriv 1 thetaCuspLogSource x ^ (4 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) +
      420 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x ^ (3 : ℕ) +
      105 * iteratedDeriv 2 thetaCuspLogSource x ^ (4 : ℕ) +
      56 * iteratedDeriv 1 thetaCuspLogSource x ^ (5 : ℕ) *
        iteratedDeriv 3 thetaCuspLogSource x +
      560 * iteratedDeriv 1 thetaCuspLogSource x ^ (3 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x +
      840 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 3 thetaCuspLogSource x +
      280 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 3 thetaCuspLogSource x ^ (2 : ℕ) +
      280 * iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x ^ (2 : ℕ) +
      70 * iteratedDeriv 1 thetaCuspLogSource x ^ (4 : ℕ) *
        iteratedDeriv 4 thetaCuspLogSource x +
      420 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 4 thetaCuspLogSource x +
      210 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 4 thetaCuspLogSource x +
      280 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x *
        iteratedDeriv 4 thetaCuspLogSource x +
      35 * iteratedDeriv 4 thetaCuspLogSource x ^ (2 : ℕ) +
      56 * iteratedDeriv 1 thetaCuspLogSource x ^ (3 : ℕ) *
        iteratedDeriv 5 thetaCuspLogSource x +
      168 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 5 thetaCuspLogSource x +
      56 * iteratedDeriv 3 thetaCuspLogSource x *
        iteratedDeriv 5 thetaCuspLogSource x +
      28 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 6 thetaCuspLogSource x +
      28 * iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 6 thetaCuspLogSource x +
      8 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 7 thetaCuspLogSource x +
      iteratedDeriv 8 thetaCuspLogSource x)

/-- The sixth exponential Bell jet differentiates to the seventh. -/
theorem hasDerivAt_thetaCuspLogExponentialJetSix (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetSix
      (thetaCuspLogExponentialJetSeven x) x := by
  have h0 := hasDerivAt_thetaCuspLogExponentialJetZero x
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  have h2 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x
  have h3 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x
  have h4 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 4 x
  have h5 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x
  have h6 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 6 x
  norm_num at h1 h2 h3 h4 h5 h6
  have hcoeff :=
    ((((((((((h1.pow 6).add (((h1.pow 4).mul h2).const_mul 15)).add
      (((h1.pow 2).mul (h2.pow 2)).const_mul 45)).add
      ((h2.pow 3).const_mul 15)).add
      (((h1.pow 3).mul h3).const_mul 20)).add
      (((h1.mul h2).mul h3).const_mul 60)).add
      ((h3.pow 2).const_mul 10)).add
      (((h1.pow 2).mul h4).const_mul 15)).add
      ((h2.mul h4).const_mul 15)).add
      ((h1.mul h5).const_mul 6)).add h6
  unfold thetaCuspLogExponentialJetSix thetaCuspLogExponentialJetSeven
  convert h0.mul hcoeff using 1 <;>
    first | rfl | ((try funext y); simp only [thetaCuspLogExponentialJetOne,
      iteratedDeriv_one, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)

/-- The seventh exponential Bell jet differentiates to the eighth. -/
theorem hasDerivAt_thetaCuspLogExponentialJetSeven (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetSeven
      (thetaCuspLogExponentialJetEight x) x := by
  have h0 := hasDerivAt_thetaCuspLogExponentialJetZero x
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  have h2 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x
  have h3 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x
  have h4 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 4 x
  have h5 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x
  have h6 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 6 x
  have h7 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 7 x
  norm_num at h1 h2 h3 h4 h5 h6 h7
  have hcoeff :=
    ((((((((((((((h1.pow 7).add (((h1.pow 5).mul h2).const_mul 21)).add
      (((h1.pow 3).mul (h2.pow 2)).const_mul 105)).add
      ((h1.mul (h2.pow 3)).const_mul 105)).add
      (((h1.pow 4).mul h3).const_mul 35)).add
      ((((h1.pow 2).mul h2).mul h3).const_mul 210)).add
      (((h2.pow 2).mul h3).const_mul 105)).add
      ((h1.mul (h3.pow 2)).const_mul 70)).add
      (((h1.pow 3).mul h4).const_mul 35)).add
      (((h1.mul h2).mul h4).const_mul 105)).add
      ((h3.mul h4).const_mul 35)).add
      (((h1.pow 2).mul h5).const_mul 21)).add
      ((h2.mul h5).const_mul 21)).add
      ((h1.mul h6).const_mul 7)).add h7
  unfold thetaCuspLogExponentialJetSeven thetaCuspLogExponentialJetEight
  convert h0.mul hcoeff using 1 <;>
    first | rfl | ((try funext y); simp only [thetaCuspLogExponentialJetOne,
      iteratedDeriv_one, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)

/-- The actual seventh complete-source derivative is its seventh exponential Bell jet. -/
theorem iteratedDeriv_seven_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 7 thetaCuspFullSource x = thetaCuspLogExponentialJetSeven x := by
  rw [show 7 = 6 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 6 thetaCuspFullSource = thetaCuspLogExponentialJetSix := by
    funext y
    exact iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet y
  rw [heq]
  exact (hasDerivAt_thetaCuspLogExponentialJetSix x).deriv

/-- The actual eighth complete-source derivative is its eighth exponential Bell jet. -/
theorem iteratedDeriv_eight_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 8 thetaCuspFullSource x = thetaCuspLogExponentialJetEight x := by
  rw [show 8 = 7 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 7 thetaCuspFullSource = thetaCuspLogExponentialJetSeven := by
    funext y
    exact iteratedDeriv_seven_thetaCuspFullSource_eq_logExponentialJet y
  rw [heq]
  exact (hasDerivAt_thetaCuspLogExponentialJetSeven x).deriv

/-- Raw rank-three reflected curvature is the positive source sixth power times its even-log
curvature polynomial. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_eq_logJets (x : ℝ) :
    thetaCuspFullSourceReflectionEighthHankelCurvature x =
      4 * thetaCuspFullSource x ^ (6 : ℕ) *
        (iteratedDeriv 4 thetaCuspLogSource x *
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
          768 * iteratedDeriv 2 thetaCuspLogSource x ^ (6 : ℕ)) := by
  have hsource : thetaCuspFullSource x = thetaCuspLogExponentialJetZero x := by
    rw [thetaCuspFullSource_eq_logExponentialJetZero]
  unfold thetaCuspFullSourceReflectionEighthHankelCurvature
  dsimp only
  rw [iteratedDeriv_zero, hsource,
    iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_three_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_five_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_seven_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_eight_thetaCuspFullSource_eq_logExponentialJet]
  unfold thetaCuspLogExponentialJetOne thetaCuspLogExponentialJetTwo
    thetaCuspLogExponentialJetThree thetaCuspLogExponentialJetFour
    thetaCuspLogExponentialJetFive thetaCuspLogExponentialJetSix
    thetaCuspLogExponentialJetSeven thetaCuspLogExponentialJetEight
  exact HilbertMetric.reflectedProduct_signedEvenHankelThreeDet_of_logJets
    (thetaCuspLogExponentialJetZero x)
    (iteratedDeriv 1 thetaCuspLogSource x)
    (iteratedDeriv 2 thetaCuspLogSource x)
    (iteratedDeriv 3 thetaCuspLogSource x)
    (iteratedDeriv 4 thetaCuspLogSource x)
    (iteratedDeriv 5 thetaCuspLogSource x)
    (iteratedDeriv 6 thetaCuspLogSource x)
    (iteratedDeriv 7 thetaCuspLogSource x)
    (iteratedDeriv 8 thetaCuspLogSource x)

/-- On the positive source half-line, raw rank-three curvature is exactly the positive source
sixth power times the native normalized D1 curvature. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFullSourceReflectionEighthHankelCurvature x =
      4 * thetaCuspFullSource x ^ (6 : ℕ) *
        thetaCuspFullReflectionEighthHankelCurvature x := by
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_eq_logJets,
    thetaCuspLogSource_eighthHankel_eq_fullReflectionEighthCurvature hx]

end

end RHTower
