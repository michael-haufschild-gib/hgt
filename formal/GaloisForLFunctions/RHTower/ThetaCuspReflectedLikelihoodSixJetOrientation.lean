import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthSourceOrientation

/-!
# Six negative reflected likelihood jets

The likelihood corpus proves source-coordinate orientations through order six, but the C5 route
uses displacement jets of the two-ended reflected likelihood action.  This module performs the
missing chain-rule transport.

The fourth and sixth reflected jets are negative sums of positive source jets.  The fifth is a
difference of fifth source jets; strict positivity of the sixth source jet makes the fifth source
jet strictly increasing and fixes that difference's sign.  Consequently reflected likelihood
action jets one through six are all strictly negative throughout the open same-half-line chamber.

Combined with `HilbertMetric.FifthRootAtomLikelihoodRiccatiNoGo`, this is also a sharp method
boundary: even these six literal signs, the component Riccati margins, and atom domination do not
force global fifth-root curvature.  A surviving C5 proof needs nonlocal action--jet coupling.
-/

open Set

namespace RHTower

noncomputable section

/-- Fourth displacement jet of the reflected likelihood action. -/
def thetaCuspReflectedLikelihoodCumulantJetFour (u t : ℝ) : ℝ :=
  -thetaCuspLikelihoodSourceLogPartitionJetFour (u + t) -
    thetaCuspLikelihoodSourceLogPartitionJetFour (u - t)

/-- Fifth displacement jet of the reflected likelihood action. -/
def thetaCuspReflectedLikelihoodCumulantJetFive (u t : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceLogPartitionJetFive (u - t) -
    thetaCuspLikelihoodSourceLogPartitionJetFive (u + t)

/-- Sixth displacement jet of the reflected likelihood action. -/
def thetaCuspReflectedLikelihoodCumulantJetSix (u t : ℝ) : ℝ :=
  -thetaCuspLikelihoodSourceLogPartitionJetSix (u + t) -
    thetaCuspLikelihoodSourceLogPartitionJetSix (u - t)

theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetThree
    {u t : ℝ} (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspReflectedLikelihoodCumulantJetThree u)
      (thetaCuspReflectedLikelihoodCumulantJetFour u t) t := by
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hminus).comp t
    ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hplus).comp t
    ((hasDerivAt_const t u).add (hasDerivAt_id t))
  unfold thetaCuspReflectedLikelihoodCumulantJetThree
    thetaCuspReflectedLikelihoodCumulantJetFour
  have hraw := hm.sub hp
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num
  ring

theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetFour
    {u t : ℝ} (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspReflectedLikelihoodCumulantJetFour u)
      (thetaCuspReflectedLikelihoodCumulantJetFive u t) t := by
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hplus).comp t
    ((hasDerivAt_const t u).add (hasDerivAt_id t))
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hminus).comp t
    ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  unfold thetaCuspReflectedLikelihoodCumulantJetFour
    thetaCuspReflectedLikelihoodCumulantJetFive
  have hraw := hp.neg.sub hm
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num
  ring

theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetFive
    {u t : ℝ} (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspReflectedLikelihoodCumulantJetFive u)
      (thetaCuspReflectedLikelihoodCumulantJetSix u t) t := by
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive hminus).comp t
    ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive hplus).comp t
    ((hasDerivAt_const t u).add (hasDerivAt_id t))
  unfold thetaCuspReflectedLikelihoodCumulantJetFive
    thetaCuspReflectedLikelihoodCumulantJetSix
  have hraw := hm.sub hp
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num
  ring

/-- Fifth source likelihood jet is strictly increasing on the nonnegative source half-line. -/
theorem strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetFive :
    StrictMonoOn thetaCuspLikelihoodSourceLogPartitionJetFive (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive
      (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv]
    exact thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx.le

theorem thetaCuspReflectedLikelihoodCumulantJetFour_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantJetFour u t < 0 := by
  have hp := thetaCuspLikelihoodSourceLogPartitionJetFour_pos
    (show 0 ≤ u + t by linarith)
  have hm := thetaCuspLikelihoodSourceLogPartitionJetFour_pos
    (show 0 ≤ u - t by linarith)
  unfold thetaCuspReflectedLikelihoodCumulantJetFour
  linarith

theorem thetaCuspReflectedLikelihoodCumulantJetFive_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantJetFive u t < 0 := by
  unfold thetaCuspReflectedLikelihoodCumulantJetFive
  exact sub_neg.mpr
    (strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetFive
      (by simp; linarith) (by simp; linarith) (by linarith))

theorem thetaCuspReflectedLikelihoodCumulantJetSix_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantJetSix u t < 0 := by
  have hp := thetaCuspLikelihoodSourceLogPartitionJetSix_pos
    (show 0 ≤ u + t by linarith)
  have hm := thetaCuspLikelihoodSourceLogPartitionJetSix_pos
    (show 0 ≤ u - t by linarith)
  unfold thetaCuspReflectedLikelihoodCumulantJetSix
  linarith

/-- Literal completed-theta likelihood action has six consecutive strictly negative displacement
jets throughout the open same-half-line chamber. -/
theorem thetaCuspReflectedLikelihoodCumulantJets_one_to_six_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantJetOne u t < 0 ∧
    thetaCuspReflectedLikelihoodCumulantJetTwo u t < 0 ∧
    thetaCuspReflectedLikelihoodCumulantJetThree u t < 0 ∧
    thetaCuspReflectedLikelihoodCumulantJetFour u t < 0 ∧
    thetaCuspReflectedLikelihoodCumulantJetFive u t < 0 ∧
    thetaCuspReflectedLikelihoodCumulantJetSix u t < 0 := by
  exact ⟨thetaCuspReflectedLikelihoodCumulantJetOne_neg ht htu,
    thetaCuspReflectedLikelihoodCumulantJetTwo_neg ht htu,
    thetaCuspReflectedLikelihoodCumulantJetThree_neg ht htu,
    thetaCuspReflectedLikelihoodCumulantJetFour_neg ht htu,
    thetaCuspReflectedLikelihoodCumulantJetFive_neg ht htu,
    thetaCuspReflectedLikelihoodCumulantJetSix_neg ht htu⟩

end

end RHTower
