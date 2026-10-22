import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthModularSeam
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGlobalReflectedRiccati

/-!
# Exact real exponential Bell transfer through order six

The complete theta source is globally positive, so it is the exponential of its logarithmic
source.  This file differentiates that identity through order six and feeds the exact Bell jets
to the reflected second--sixth Hankel identity.  The resulting connector is global and contains
no half-line or nonvanishing hypothesis.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-! ## Exact real exponential Bell transfer through order six -/

def thetaCuspLogExponentialJetZero (x : ℝ) : ℝ :=
  Real.exp (thetaCuspLogSource x)

def thetaCuspLogExponentialJetOne (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x * iteratedDeriv 1 thetaCuspLogSource x

def thetaCuspLogExponentialJetTwo (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x *
    (iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) +
      iteratedDeriv 2 thetaCuspLogSource x)

def thetaCuspLogExponentialJetThree (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x *
    (iteratedDeriv 1 thetaCuspLogSource x ^ (3 : ℕ) +
      3 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x +
      iteratedDeriv 3 thetaCuspLogSource x)

def thetaCuspLogExponentialJetFour (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x *
    (iteratedDeriv 1 thetaCuspLogSource x ^ (4 : ℕ) +
      6 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x +
      3 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) +
      4 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x +
      iteratedDeriv 4 thetaCuspLogSource x)

def thetaCuspLogExponentialJetFive (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x *
    (iteratedDeriv 1 thetaCuspLogSource x ^ (5 : ℕ) +
      10 * iteratedDeriv 1 thetaCuspLogSource x ^ (3 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x +
      15 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) +
      10 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 3 thetaCuspLogSource x +
      10 * iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x +
      5 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 4 thetaCuspLogSource x +
      iteratedDeriv 5 thetaCuspLogSource x)

def thetaCuspLogExponentialJetSix (x : ℝ) : ℝ :=
  thetaCuspLogExponentialJetZero x *
    (iteratedDeriv 1 thetaCuspLogSource x ^ (6 : ℕ) +
      15 * iteratedDeriv 1 thetaCuspLogSource x ^ (4 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x +
      45 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) +
      15 * iteratedDeriv 2 thetaCuspLogSource x ^ (3 : ℕ) +
      20 * iteratedDeriv 1 thetaCuspLogSource x ^ (3 : ℕ) *
        iteratedDeriv 3 thetaCuspLogSource x +
      60 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 3 thetaCuspLogSource x +
      10 * iteratedDeriv 3 thetaCuspLogSource x ^ (2 : ℕ) +
      15 * iteratedDeriv 1 thetaCuspLogSource x ^ (2 : ℕ) *
        iteratedDeriv 4 thetaCuspLogSource x +
      15 * iteratedDeriv 2 thetaCuspLogSource x *
        iteratedDeriv 4 thetaCuspLogSource x +
      6 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 5 thetaCuspLogSource x +
      iteratedDeriv 6 thetaCuspLogSource x)

theorem hasDerivAt_thetaCuspLogExponentialJetZero (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetZero
      (thetaCuspLogExponentialJetOne x) x := by
  have h := (hasDerivAt_iteratedDeriv_thetaCuspLogSource 0 x).exp
  norm_num at h
  unfold thetaCuspLogExponentialJetOne thetaCuspLogExponentialJetZero
  simpa only [iteratedDeriv_one] using h

theorem hasDerivAt_thetaCuspLogExponentialJetOne (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetOne
      (thetaCuspLogExponentialJetTwo x) x := by
  have h0 := hasDerivAt_thetaCuspLogExponentialJetZero x
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  norm_num at h1
  unfold thetaCuspLogExponentialJetOne thetaCuspLogExponentialJetTwo
  convert h0.mul h1 using 1 <;>
    first | rfl | ((try funext y); simp only [thetaCuspLogExponentialJetOne,
      iteratedDeriv_one, Pi.mul_apply] <;> ring)

theorem hasDerivAt_thetaCuspLogExponentialJetTwo (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetTwo
      (thetaCuspLogExponentialJetThree x) x := by
  have h0 := hasDerivAt_thetaCuspLogExponentialJetZero x
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  have h2 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x
  norm_num at h1 h2
  have hcoeff := (h1.pow 2).add h2
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetThree
  convert h0.mul hcoeff using 1 <;>
    first | rfl | ((try funext y); simp only [thetaCuspLogExponentialJetOne,
      iteratedDeriv_one, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] <;> ring)

theorem hasDerivAt_thetaCuspLogExponentialJetThree (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetThree
      (thetaCuspLogExponentialJetFour x) x := by
  have h0 := hasDerivAt_thetaCuspLogExponentialJetZero x
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  have h2 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x
  have h3 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x
  norm_num at h1 h2 h3
  have hcoeff := ((h1.pow 3).add ((h1.mul h2).const_mul 3)).add h3
  unfold thetaCuspLogExponentialJetThree thetaCuspLogExponentialJetFour
  convert h0.mul hcoeff using 1 <;>
    first | rfl | ((try funext y); simp only [thetaCuspLogExponentialJetOne,
      iteratedDeriv_one, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)

theorem hasDerivAt_thetaCuspLogExponentialJetFour (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetFour
      (thetaCuspLogExponentialJetFive x) x := by
  have h0 := hasDerivAt_thetaCuspLogExponentialJetZero x
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  have h2 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x
  have h3 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x
  have h4 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 4 x
  norm_num at h1 h2 h3 h4
  have hcoeff :=
    ((((h1.pow 4).add (((h1.pow 2).mul h2).const_mul 6)).add
      ((h2.pow 2).const_mul 3)).add ((h1.mul h3).const_mul 4)).add h4
  unfold thetaCuspLogExponentialJetFour thetaCuspLogExponentialJetFive
  convert h0.mul hcoeff using 1 <;>
    first | rfl | ((try funext y); simp only [thetaCuspLogExponentialJetOne,
      iteratedDeriv_one, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)

theorem hasDerivAt_thetaCuspLogExponentialJetFive (x : ℝ) :
    HasDerivAt thetaCuspLogExponentialJetFive
      (thetaCuspLogExponentialJetSix x) x := by
  have h0 := hasDerivAt_thetaCuspLogExponentialJetZero x
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  have h2 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x
  have h3 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x
  have h4 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 4 x
  have h5 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x
  norm_num at h1 h2 h3 h4 h5
  have hcoeff :=
    ((((((h1.pow 5).add (((h1.pow 3).mul h2).const_mul 10)).add
      ((h1.mul (h2.pow 2)).const_mul 15)).add
      (((h1.pow 2).mul h3).const_mul 10)).add
      ((h2.mul h3).const_mul 10)).add ((h1.mul h4).const_mul 5)).add h5
  unfold thetaCuspLogExponentialJetFive thetaCuspLogExponentialJetSix
  convert h0.mul hcoeff using 1 <;>
    first | rfl | ((try funext y); simp only [thetaCuspLogExponentialJetOne,
      iteratedDeriv_one, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)

theorem thetaCuspFullSource_eq_logExponentialJetZero :
    thetaCuspFullSource = thetaCuspLogExponentialJetZero := by
  funext x
  rw [thetaCuspLogExponentialJetZero, thetaCuspLogSource,
    Real.exp_log (thetaCuspFullSource_pos_all x)]

theorem iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 1 thetaCuspFullSource x = thetaCuspLogExponentialJetOne x := by
  rw [iteratedDeriv_one, thetaCuspFullSource_eq_logExponentialJetZero]
  exact (hasDerivAt_thetaCuspLogExponentialJetZero x).deriv

theorem iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 2 thetaCuspFullSource x = thetaCuspLogExponentialJetTwo x := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 1 thetaCuspFullSource = thetaCuspLogExponentialJetOne := by
    funext y
    exact iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet y
  rw [heq]
  exact (hasDerivAt_thetaCuspLogExponentialJetOne x).deriv

theorem iteratedDeriv_three_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 3 thetaCuspFullSource x = thetaCuspLogExponentialJetThree x := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 2 thetaCuspFullSource = thetaCuspLogExponentialJetTwo := by
    funext y
    exact iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet y
  rw [heq]
  exact (hasDerivAt_thetaCuspLogExponentialJetTwo x).deriv

theorem iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 4 thetaCuspFullSource x = thetaCuspLogExponentialJetFour x := by
  rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 3 thetaCuspFullSource = thetaCuspLogExponentialJetThree := by
    funext y
    exact iteratedDeriv_three_thetaCuspFullSource_eq_logExponentialJet y
  rw [heq]
  exact (hasDerivAt_thetaCuspLogExponentialJetThree x).deriv

theorem iteratedDeriv_five_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 5 thetaCuspFullSource x = thetaCuspLogExponentialJetFive x := by
  rw [show 5 = 4 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 4 thetaCuspFullSource = thetaCuspLogExponentialJetFour := by
    funext y
    exact iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet y
  rw [heq]
  exact (hasDerivAt_thetaCuspLogExponentialJetFour x).deriv

theorem iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet (x : ℝ) :
    iteratedDeriv 6 thetaCuspFullSource x = thetaCuspLogExponentialJetSix x := by
  rw [show 6 = 5 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 5 thetaCuspFullSource = thetaCuspLogExponentialJetFive := by
    funext y
    exact iteratedDeriv_five_thetaCuspFullSource_eq_logExponentialJet y
  rw [heq]
  exact (hasDerivAt_thetaCuspLogExponentialJetFive x).deriv

/-- Raw reflected curvature is the positive source fourth power times its log-jet polynomial. -/
theorem thetaCuspFullSourceReflectionSecondSixthCurvature_eq_logJets (x : ℝ) :
    thetaCuspFullSourceReflectionSecondSixthCurvature x =
      4 * thetaCuspFullSource x ^ (4 : ℕ) *
        (iteratedDeriv 2 thetaCuspLogSource x *
            iteratedDeriv 6 thetaCuspLogSource x -
          iteratedDeriv 4 thetaCuspLogSource x ^ (2 : ℕ) +
          18 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) *
            iteratedDeriv 4 thetaCuspLogSource x +
          24 * iteratedDeriv 2 thetaCuspLogSource x ^ (4 : ℕ)) := by
  have hsource : thetaCuspFullSource x = thetaCuspLogExponentialJetZero x := by
    rw [thetaCuspFullSource_eq_logExponentialJetZero]
  rw [thetaCuspFullSourceReflectionSecondSixthCurvature]
  dsimp only
  rw [iteratedDeriv_zero, hsource,
    iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_three_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_five_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet]
  unfold thetaCuspLogExponentialJetOne thetaCuspLogExponentialJetTwo
    thetaCuspLogExponentialJetThree thetaCuspLogExponentialJetFour
    thetaCuspLogExponentialJetFive thetaCuspLogExponentialJetSix
  exact HilbertMetric.reflectedProduct_second_sixthHankel_of_logJets
    (thetaCuspLogExponentialJetZero x)
    (iteratedDeriv 1 thetaCuspLogSource x)
    (iteratedDeriv 2 thetaCuspLogSource x)
    (iteratedDeriv 3 thetaCuspLogSource x)
    (iteratedDeriv 4 thetaCuspLogSource x)
    (iteratedDeriv 5 thetaCuspLogSource x)
    (iteratedDeriv 6 thetaCuspLogSource x)

end

end RHTower
