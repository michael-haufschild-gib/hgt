import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomFourthPerturbation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspKernelLogConcavity

/-!
# Strict negativity of the fourth logarithmic theta-source derivative

The exact raw-jet identity transports the three-atom plus infinite-tail
numerator bound to the fourth derivative of the logarithm of the actual
complete theta source. Modular reflection extends the half-line proof
to every real point, including the modular centre.
-/

namespace RHTower

private theorem fullDerivative_zero (x : ℝ) :
    thetaCuspFullDerivative 0 x = thetaCuspFullSource x := by
  rw [← iteratedDeriv_thetaCuspFullSource]
  rfl

private theorem fullDerivative_zero_pos (x : ℝ) : 0 < thetaCuspFullDerivative 0 x := by
  rw [fullDerivative_zero]
  exact thetaCuspFullSource_pos_all x

private noncomputable def fullLogJetTwo (x : ℝ) : ℝ :=
  thetaCuspFullDerivative 2 x / thetaCuspFullDerivative 0 x -
    (thetaCuspFullDerivative 1 x / thetaCuspFullDerivative 0 x)^2

private noncomputable def fullLogJetThree (x : ℝ) : ℝ :=
  thetaCuspFullDerivative 3 x / thetaCuspFullDerivative 0 x -
    3*(thetaCuspFullDerivative 2 x * thetaCuspFullDerivative 1 x) /
      (thetaCuspFullDerivative 0 x)^2 +
    2*(thetaCuspFullDerivative 1 x)^3 / (thetaCuspFullDerivative 0 x)^3

private theorem hasDerivAt_fullLogOne (x : ℝ) :
    HasDerivAt (fun y => thetaCuspFullDerivative 1 y / thetaCuspFullDerivative 0 y)
      (fullLogJetTwo x) x := by
  have h0 := hasDerivAt_thetaCuspFullDerivative 0 x
  have h1 := hasDerivAt_thetaCuspFullDerivative 1 x
  have hn := (fullDerivative_zero_pos x).ne'
  convert! h1.div h0 hn using 1
  unfold fullLogJetTwo
  field_simp

private theorem hasDerivAt_fullLogTwo (x : ℝ) :
    HasDerivAt fullLogJetTwo (fullLogJetThree x) x := by
  have h0 := hasDerivAt_thetaCuspFullDerivative 0 x
  have h1 := hasDerivAt_thetaCuspFullDerivative 1 x
  have h2 := hasDerivAt_thetaCuspFullDerivative 2 x
  have hn := (fullDerivative_zero_pos x).ne'
  convert! (h2.div h0 hn).sub ((h1.div h0 hn).pow 2) using 1
  unfold fullLogJetThree
  norm_num only [Pi.div_apply, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, pow_one]
  field_simp
  ring

private theorem hasDerivAt_fullLogThree (x : ℝ) :
    HasDerivAt fullLogJetThree
      (HilbertMetric.logarithmicFourthJet
        (thetaCuspFullDerivative 0 x) (thetaCuspFullDerivative 1 x)
        (thetaCuspFullDerivative 2 x) (thetaCuspFullDerivative 3 x)
        (thetaCuspFullDerivative 4 x)) x := by
  have h0 := hasDerivAt_thetaCuspFullDerivative 0 x
  have h1 := hasDerivAt_thetaCuspFullDerivative 1 x
  have h2 := hasDerivAt_thetaCuspFullDerivative 2 x
  have h3 := hasDerivAt_thetaCuspFullDerivative 3 x
  have hn := (fullDerivative_zero_pos x).ne'
  have h := ((h3.div h0 hn).sub (((h2.mul h1).const_mul 3).div
    (h0.pow 2) (pow_ne_zero 2 hn))).add (((h1.pow 3).const_mul 2).div
    (h0.pow 3) (pow_ne_zero 3 hn))
  convert! h using 1
  unfold HilbertMetric.logarithmicFourthJet
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

/-- Exact fourth logarithmic derivative in the literal full-source derivative jets. -/
theorem iteratedDeriv_four_thetaCuspLogSource_eq_rawJet (x : ℝ) :
    iteratedDeriv 4 thetaCuspLogSource x =
      HilbertMetric.logarithmicFourthJet
        (thetaCuspFullDerivative 0 x) (thetaCuspFullDerivative 1 x)
        (thetaCuspFullDerivative 2 x) (thetaCuspFullDerivative 3 x)
        (thetaCuspFullDerivative 4 x) := by
  have h1 : iteratedDeriv 1 thetaCuspLogSource =
      fun y => thetaCuspFullDerivative 1 y / thetaCuspFullDerivative 0 y := by
    funext y
    rw [iteratedDeriv_one, fullDerivative_zero]
    simpa only [iteratedDeriv_thetaCuspFullSource] using (hasDerivAt_thetaCuspLogSource y).deriv
  have h2 : iteratedDeriv 2 thetaCuspLogSource = fullLogJetTwo := by
    rw [show 2 = 1+1 from rfl, iteratedDeriv_succ, h1]
    funext y
    exact (hasDerivAt_fullLogOne y).deriv
  have h3 : iteratedDeriv 3 thetaCuspLogSource = fullLogJetThree := by
    rw [show 3 = 2+1 from rfl, iteratedDeriv_succ, h2]
    funext y
    exact (hasDerivAt_fullLogTwo y).deriv
  rw [show 4 = 3+1 from rfl, iteratedDeriv_succ, h3]
  exact (hasDerivAt_fullLogThree x).deriv

theorem iteratedDeriv_four_thetaCuspLogSource_neg_nonneg {x : ℝ} (hx : 0 ≤ x) :
    iteratedDeriv 4 thetaCuspLogSource x < 0 := by
  rw [iteratedDeriv_four_thetaCuspLogSource_eq_rawJet,
    ← ThetaCuspThreeAtomFourth.fourthNumerator_logJet
      (fun j => thetaCuspFullDerivative j x) (fullDerivative_zero_pos x).ne']
  exact div_neg_of_neg_of_pos
    (ThetaCuspThreeAtomFourth.fullDerivative_fourthNumerator_neg hx)
    (pow_pos (fullDerivative_zero_pos x) 4)

/-- The complete theta source has strictly negative fourth logarithmic derivative everywhere. -/
theorem iteratedDeriv_four_thetaCuspLogSource_neg_all (x : ℝ) :
    iteratedDeriv 4 thetaCuspLogSource x < 0 := by
  by_cases hx : 0 ≤ x
  · exact iteratedDeriv_four_thetaCuspLogSource_neg_nonneg hx
  · have hneg := iteratedDeriv_four_thetaCuspLogSource_neg_nonneg
      (x := -x) (by linarith)
    have heven : (fun y => thetaCuspLogSource (-y)) = thetaCuspLogSource := by
      funext y
      unfold thetaCuspLogSource
      rw [thetaCuspFullSource_neg]
    have h := congrFun (congrArg (iteratedDeriv 4) heven) x
    rw [iteratedDeriv_comp_neg] at h
    norm_num [smul_eq_mul] at h
    linarith

end RHTower
