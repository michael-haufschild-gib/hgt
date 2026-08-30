import GaloisForLFunctions.HTGeometry.LikelihoodHomotopyFirstFaceSeam
import GaloisForLFunctions.HTGeometry.SmoothTruncation
import GaloisForLFunctions.HTGeometry.SmoothDerivativeChain
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopyFirstFaceObstruction
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthLogJets
import Mathlib.Analysis.Calculus.Taylor

/-!
# Fixed Bose-shifted first-face seam no-go

Conjecture K proposed the literal fixed lowest-mode Bose cone as the remaining source input in

`shifted four-face cone -> M''' > 0 -> convex likelihood lift -> direct-J ->
rank-four/Ptolemy -> CLG/TTF or Weil positivity -> RH`.

The first face has the wrong seam orientation.  A smooth potential splitting identifies its
first six seam jets with zero and its seventh jet with `3360` times the strictly positive source
obstruction proved in `ThetaCuspLikelihoodHomotopyFirstFaceObstruction`.  Taylor's theorem then
makes the literal first face positive immediately right of every scale-six seam.  Since the cone
requires that face to be nonpositive, Conjecture K is false.

Positive survivor: the exact seventh-order seam law.  Any replacement assembly must either reverse
this first-face orientation or use a sign architecture not requiring all four fixed Bose faces to
be nonpositive.
-/

open scoped BigOperators ContDiff
open Filter Topology Set

namespace RHTower

noncomputable section

open GaloisForLFunctions

private theorem contDiff_top_thetaCuspSourceTerm (n : ℕ) :
    ContDiff ℝ ∞ (fun x => thetaCuspSourceTerm x n) := by
  let f : ℕ → ℝ → ℝ := fun m =>
    thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) n
  have hf : ∀ m x, HasDerivAt (f m) (f (m + 1) x) x := by
    intro m x
    simpa [f, thetaCuspLogDerivativePolynomial] using
      hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspLogDerivativePolynomial m) n x
  have hs := GaloisForLFunctions.HTGeometry.contDiff_top_of_hasDerivAt_chain hf 0
  simpa [f, thetaCuspLogDerivativePolynomial,
    thetaCuspSourceTerm_eq_polynomialAtom] using hs

private theorem contDiffOn_top_thetaCuspFirstAtomLog :
    ContDiffOn ℝ ∞ thetaCuspFirstAtomLog (Ioi 0) := by
  intro x hx
  have hs : ContDiffAt ℝ ∞ (fun y => thetaCuspSourceTerm y 1) x :=
    (contDiff_top_thetaCuspSourceTerm 1).contDiffAt
  have hp := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  unfold thetaCuspFirstAtomLog
  exact (hs.log hp.ne').contDiffWithinAt

private theorem iteratedDeriv_one_likelihood
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 thetaCuspLikelihoodSourceLogPartition x =
      thetaCuspLikelihoodSourceLogPartitionJetOne x := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartition
    (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv

private theorem iteratedDeriv_two_likelihood
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 thetaCuspLikelihoodSourceLogPartition x =
      thetaCuspLikelihoodSourceLogPartitionJetTwo x := by
  have heq : iteratedDeriv 1 thetaCuspLikelihoodSourceLogPartition =ᶠ[nhds x]
      thetaCuspLikelihoodSourceLogPartitionJetOne := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_one_likelihood hy
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ]
  exact ((hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
    (thetaCuspLikelihoodCoordinate_pos hx.le)).congr_of_eventuallyEq heq).deriv

private theorem iteratedDeriv_three_likelihood
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 thetaCuspLikelihoodSourceLogPartition x =
      thetaCuspLikelihoodSourceLogPartitionJetThree x := by
  have heq : iteratedDeriv 2 thetaCuspLikelihoodSourceLogPartition =ᶠ[nhds x]
      thetaCuspLikelihoodSourceLogPartitionJetTwo := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_two_likelihood hy
  rw [show (3 : ℕ) = 2 + 1 by omega, iteratedDeriv_succ]
  exact ((hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
    (thetaCuspLikelihoodCoordinate_pos hx.le)).congr_of_eventuallyEq heq).deriv

private theorem iteratedDeriv_four_likelihood
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 4 thetaCuspLikelihoodSourceLogPartition x =
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  have heq : iteratedDeriv 3 thetaCuspLikelihoodSourceLogPartition =ᶠ[nhds x]
      thetaCuspLikelihoodSourceLogPartitionJetThree := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_three_likelihood hy
  rw [show (4 : ℕ) = 3 + 1 by omega, iteratedDeriv_succ]
  exact ((hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
    (thetaCuspLikelihoodCoordinate_pos hx.le)).congr_of_eventuallyEq heq).deriv

private theorem iteratedDeriv_five_likelihood
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 5 thetaCuspLikelihoodSourceLogPartition x =
      thetaCuspLikelihoodSourceLogPartitionJetFive x := by
  have heq : iteratedDeriv 4 thetaCuspLikelihoodSourceLogPartition =ᶠ[nhds x]
      thetaCuspLikelihoodSourceLogPartitionJetFour := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_four_likelihood hy
  rw [show (5 : ℕ) = 4 + 1 by omega, iteratedDeriv_succ]
  exact ((hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour
    (thetaCuspLikelihoodCoordinate_pos hx.le)).congr_of_eventuallyEq heq).deriv

private theorem thetaCuspLogSource_eq_atom_add_likelihood
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogSource x = thetaCuspFirstAtomLog x +
      thetaCuspLikelihoodSourceLogPartition x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  have hpart := thetaCuspLikelihoodPartition_pos hB
  unfold thetaCuspLogSource thetaCuspFirstAtomLog
    thetaCuspLikelihoodSourceLogPartition
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
    Real.log_mul hfirst.ne' hpart.ne']

/-- Smooth potential representation of the literal first-face seam germ, together with its exact
seventh-order source obstruction. -/
theorem exists_thetaCuspC5FirstFacePotentialRepresentation
    {u : ℝ} (hu : 0 < u) :
    ∃ f g : ℝ → ℝ, ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
      (∀ k < 7,
        iteratedDeriv k (HTGeometry.c5FirstShiftedFacePotentialGerm f g u) 0 = 0) ∧
      iteratedDeriv 7 (HTGeometry.c5FirstShiftedFacePotentialGerm f g u) 0 =
        3360 * thetaCuspC5FirstFaceSeamObstruction u ∧
      g = thetaCuspLogSource - f ∧
      g =ᶠ[nhds u] thetaCuspLikelihoodSourceLogPartition := by
  obtain ⟨f, hf, hfeq⟩ := HTGeometry.exists_contDiff_eventuallyEq
    isOpen_Ioi hu contDiffOn_top_thetaCuspFirstAtomLog
  let g : ℝ → ℝ := thetaCuspLogSource - f
  have hg : ContDiff ℝ ∞ g := by
    dsimp only [g]
    exact contDiff_thetaCuspLogSource.sub hf
  have hgeq : g =ᶠ[nhds u] thetaCuspLikelihoodSourceLogPartition := by
    filter_upwards [hfeq, Ioi_mem_nhds hu] with x hfx hx
    dsimp only [g]
    change thetaCuspLogSource x - f x = thetaCuspLikelihoodSourceLogPartition x
    rw [hfx, thetaCuspLogSource_eq_atom_add_likelihood hx]
    ring
  have hgj (n : ℕ) : iteratedDeriv n g u =
      iteratedDeriv n thetaCuspLikelihoodSourceLogPartition u :=
    (HTGeometry.eventuallyEq_iteratedDeriv_real hgeq n).eq_of_nhds
  have hg2 : iteratedDeriv 2 g u = thetaCuspLikelihoodSourceLogPartitionJetTwo u :=
    (hgj 2).trans (iteratedDeriv_two_likelihood hu)
  have hg3 : iteratedDeriv 3 g u = thetaCuspLikelihoodSourceLogPartitionJetThree u :=
    (hgj 3).trans (iteratedDeriv_three_likelihood hu)
  have hg4 : iteratedDeriv 4 g u = thetaCuspLikelihoodSourceLogPartitionJetFour u :=
    (hgj 4).trans (iteratedDeriv_four_likelihood hu)
  have hg5 : iteratedDeriv 5 g u = thetaCuspLikelihoodSourceLogPartitionJetFive u :=
    (hgj 5).trans (iteratedDeriv_five_likelihood hu)
  have hsplit (n : ℕ) : iteratedDeriv n g u =
      iteratedDeriv n thetaCuspLogSource u - iteratedDeriv n f u := by
    dsimp only [g]
    exact iteratedDeriv_sub
      (contDiff_thetaCuspLogSource.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hf2 : iteratedDeriv 2 f u = -thetaCuspBornWittenLogCurvature 1 u := by
    have hfull := iteratedDeriv_two_thetaCuspLogSource_eq_factor hu
    have hlike :=
      thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hu
    rw [← hlike] at hfull
    linarith [hsplit 2, hg2]
  have hf3 : iteratedDeriv 3 f u = -thetaCuspBornWittenLogThirdDerivative 1 u := by
    have hfull := iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hu
    have hlike :=
      thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hu
    rw [← hlike] at hfull
    unfold thetaCuspFirstAtomLogJetThree at hfull
    linarith [hsplit 3, hg3]
  have hf4 : iteratedDeriv 4 f u = -thetaCuspBornWittenLogFourthDerivative 1 u := by
    have hfull := iteratedDeriv_four_thetaCuspLogSource_eq_factor hu
    have hlike :=
      thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hu
    rw [← hlike] at hfull
    linarith [hsplit 4, hg4]
  have hf5 : iteratedDeriv 5 f u = -thetaCuspBornWittenLogFifthDerivative 1 u := by
    have hfull := iteratedDeriv_five_thetaCuspLogSource_eq_full_jets hu
    unfold thetaCuspFullLogJetFive at hfull
    linarith [hsplit 5, hg5]
  have hclass := HTGeometry.c5FirstShiftedFacePotentialGerm_seamJetClassification
    f g u hf hg
  refine ⟨f, g, hf, hg, hclass.1, ?_, rfl, hgeq⟩
  rw [hclass.2, hf2, hf3, hf4, hf5, hg2, hg3, hg4, hg5]
  unfold thetaCuspC5FirstFaceSeamObstruction
  ring

/-- The smooth potential seam model is locally the literal first fixed-Bose face. -/
theorem eventuallyEq_thetaCuspC5FirstFacePotential_actual
    {u : ℝ} (hu : 0 < u) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hfg : g = thetaCuspLogSource - f)
    (hgeq : g =ᶠ[nhds u] thetaCuspLikelihoodSourceLogPartition) :
    HTGeometry.c5FirstShiftedFacePotentialGerm f g u =ᶠ[nhdsWithin 0 (Ioi 0)]
      fun t => (thetaCuspC5LikelihoodHomotopyData u t).boseShiftedTransportOne 0 := by
  have hgeq1 : iteratedDeriv 1 g =ᶠ[nhds u]
      thetaCuspLikelihoodSourceLogPartitionJetOne := by
    exact (HTGeometry.eventuallyEq_iteratedDeriv_real hgeq 1).trans (by
      filter_upwards [Ioi_mem_nhds hu] with x hx
      exact iteratedDeriv_one_likelihood hx)
  have hgeq2 : iteratedDeriv 2 g =ᶠ[nhds u]
      thetaCuspLikelihoodSourceLogPartitionJetTwo := by
    exact (HTGeometry.eventuallyEq_iteratedDeriv_real hgeq 2).trans (by
      filter_upwards [Ioi_mem_nhds hu] with x hx
      exact iteratedDeriv_two_likelihood hx)
  have hplusT : Tendsto (fun t : ℝ => u + t) (nhds 0) (nhds u) := by
    simpa using
      ((continuousAt_id : ContinuousAt (id : ℝ → ℝ) 0).const_add u).tendsto
  have hminusT : Tendsto (fun t : ℝ => u - t) (nhds 0) (nhds u) := by
    simpa [sub_eq_add_neg] using
      ((continuousAt_id : ContinuousAt (id : ℝ → ℝ) 0).neg.const_add u).tendsto
  have hplus0 := hplusT.eventually hgeq
  have hminus0 := hminusT.eventually hgeq
  have hplus1 := hplusT.eventually hgeq1
  have hminus1 := hminusT.eventually hgeq1
  have hplus2 := hplusT.eventually hgeq2
  have hminus2 := hminusT.eventually hgeq2
  have hcenter0 := hgeq.eq_of_nhds
  have hcenter1 := hgeq1.eq_of_nhds
  have htu : {t : ℝ | t < u} ∈ nhdsWithin 0 (Ioi 0) :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hu)
  filter_upwards [hplus0.filter_mono inf_le_left, hminus0.filter_mono inf_le_left,
    hplus1.filter_mono inf_le_left, hminus1.filter_mono inf_le_left,
    hplus2.filter_mono inf_le_left, hminus2.filter_mono inf_le_left,
    self_mem_nhdsWithin, htu] with t hgp0 hgm0 hgp1 hgm1 hgp2 hgm2 ht htU
  have ht0 : 0 < t := ht
  have hsplit (n : ℕ) (x : ℝ) : iteratedDeriv n g x =
      iteratedDeriv n thetaCuspLogSource x - iteratedDeriv n f x := by
    rw [hfg]
    exact iteratedDeriv_sub
      (contDiff_thetaCuspLogSource.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hf1p : iteratedDeriv 1 f (u + t) =
      iteratedDeriv 1 thetaCuspLogSource (u + t) -
        thetaCuspLikelihoodSourceLogPartitionJetOne (u + t) := by
    linarith [hsplit 1 (u + t)]
  have hf1m : iteratedDeriv 1 f (u - t) =
      iteratedDeriv 1 thetaCuspLogSource (u - t) -
        thetaCuspLikelihoodSourceLogPartitionJetOne (u - t) := by
    linarith [hsplit 1 (u - t)]
  have hf1c : iteratedDeriv 1 f u = iteratedDeriv 1 thetaCuspLogSource u -
      thetaCuspLikelihoodSourceLogPartitionJetOne u := by
    linarith [hsplit 1 u]
  have hf2p : iteratedDeriv 2 f (u + t) =
      iteratedDeriv 2 thetaCuspLogSource (u + t) -
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) := by
    linarith [hsplit 2 (u + t)]
  have hf2m : iteratedDeriv 2 f (u - t) =
      iteratedDeriv 2 thetaCuspLogSource (u - t) -
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) := by
    linarith [hsplit 2 (u - t)]
  have haBridge := thetaCuspReflectedLogJetOne_eq_completed ht0 htU
  have hbBridge := thetaCuspReflectedLogJetTwo_eq_completed ht0 htU
  have hsBridge := thetaCuspReflectedLogCenterJetOne_eq_completed ht0 htU
  have hmBridge := thetaCuspReflectedLogCenterMixedJetOne_eq_completed ht0 htU
  have ha : iteratedDeriv 1 f (u - t) - iteratedDeriv 1 f (u + t) =
      thetaCuspSingleAtomReflectedActionJetOne
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) (2 * Real.sinh (2 * t)) := by
    rw [hf1m, hf1p]
    unfold thetaCuspCompletedReflectedCumulantJetOne
      thetaCuspReflectedLikelihoodCumulantJetOne at haBridge
    unfold thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope at haBridge
    linarith
  have hb : -iteratedDeriv 2 f (u + t) - iteratedDeriv 2 f (u - t) =
      thetaCuspSingleAtomReflectedActionJetTwo
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) := by
    rw [hf2p, hf2m]
    unfold thetaCuspCompletedReflectedCumulantJetTwo
      thetaCuspReflectedLikelihoodCumulantJetTwo at hbBridge
    unfold thetaCuspReflectedLogJetTwo thetaCuspLogCurvature at hbBridge
    linarith
  have hs : 2 * iteratedDeriv 1 f u - iteratedDeriv 1 f (u + t) -
      iteratedDeriv 1 f (u - t) =
      c5SingleAtomScaleActionJetOne
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) := by
    rw [hf1c, hf1p, hf1m]
    unfold c5CompletedScaleActionJetOne c5LikelihoodScaleActionJetOne
      thetaCuspReflectedLogCenterJetOne thetaCuspLogDecaySlope at hsBridge
    linarith
  have hm : iteratedDeriv 2 f (u - t) - iteratedDeriv 2 f (u + t) =
      c5SingleAtomScaleMixedJetOne
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) (2 * Real.sinh (2 * t)) := by
    rw [hf2m, hf2p]
    unfold c5CompletedScaleMixedJetOne c5LikelihoodScaleMixedJetOne
      thetaCuspReflectedLogCenterMixedJetOne thetaCuspLogCurvature at hmBridge
    linarith
  unfold HTGeometry.c5FirstShiftedFacePotentialGerm HTGeometry.c5FirstShiftedFaceGerm
    C5LikelihoodAffineData.boseShiftedTransportOne
    C5LikelihoodAffineData.boseShiftedTransportZero
    C5LikelihoodAffineData.velocityCenter C5LikelihoodAffineData.velocityCenterOne
    C5LikelihoodAffineData.jetOne C5LikelihoodAffineData.jetTwo
    C5LikelihoodAffineData.scaleAction C5LikelihoodAffineData.scaleMixedOne
    C5LikelihoodAffineData.affine thetaCuspC5LikelihoodHomotopyData
    thetaCuspReflectedLikelihoodCumulantAction
    thetaCuspReflectedLikelihoodCumulantJetOne
    thetaCuspReflectedLikelihoodCumulantJetTwo
    c5LikelihoodScaleActionJetOne c5LikelihoodScaleMixedJetOne
  dsimp only
  rw [ha, hb, hs, hm, hgp0, hgm0, hgp1, hgm1, hgp2, hgm2,
    hcenter0, hcenter1]
  ring

private def firstFaceTaylorShift
    (f : ℝ → ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    iteratedDeriv k f x * r ^ k / (k.factorial : ℝ)

private theorem taylorWithinEval_add_eq_firstFaceTaylorShift
    {f : ℝ → ℝ} {x r : ℝ}
    (hf : ContDiffAt ℝ 7 f x) (hr : 0 < r) (j : ℕ) (hj : j ≤ 6) :
    taylorWithinEval f j (uIcc x (x + r)) x (x + r) =
      firstFaceTaylorShift f j r x := by
  have hle : x ≤ x + r := by linarith
  rw [uIcc_of_le hle]
  induction j with
  | zero => simp [firstFaceTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih (by omega)]
      simp only [firstFaceTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) f (Icc x (x + r)) x =
          iteratedDeriv (j + 1) f x := by
        have hj7 : ((j + 1 : ℕ) : WithTop ℕ∞) ≤ (7 : WithTop ℕ∞) := by
          exact_mod_cast (show j + 1 ≤ 7 by omega)
        exact iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by linarith)) (hf.of_le hj7)
          (left_mem_Icc.mpr hle)
      rw [hderiv, Nat.factorial_succ]
      push_cast
      ring

private theorem firstFacePotential_taylor_six_zero
    {f g : ℝ → ℝ} {u t : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (ht : 0 < t)
    (hzero : ∀ k < 7,
      iteratedDeriv k (HTGeometry.c5FirstShiftedFacePotentialGerm f g u) 0 = 0) :
    taylorWithinEval (HTGeometry.c5FirstShiftedFacePotentialGerm f g u) 6
      (uIcc 0 t) 0 t = 0 := by
  let P := HTGeometry.c5FirstShiftedFacePotentialGerm f g u
  have hPtop : ContDiff ℝ ∞ P := by
    simpa only [P] using HTGeometry.contDiff_c5FirstShiftedFacePotentialGerm f g u hf hg
  have hP7 : ContDiffAt ℝ 7 P 0 :=
    hPtop.contDiffAt.of_le (by
      change (↑(7 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hTaylor := taylorWithinEval_add_eq_firstFaceTaylorShift
    (f := P) (x := 0) (r := t) hP7 ht 6 (by norm_num)
  simpa only [zero_add, P] using hTaylor.trans (by
    unfold firstFaceTaylorShift
    apply Finset.sum_eq_zero
    intro k hk
    rw [hzero k (Finset.mem_range.mp hk)]
    simp)

/-- The actual lowest-mode first shifted Bose face is positive immediately right of every
positive seam centre whose first-atom structural scale is at least six. -/
theorem eventually_thetaCuspC5LikelihoodHomotopy_boseShiftedTransportOne_zero_pos
    {u : ℝ} (hu : 0 < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < (thetaCuspC5LikelihoodHomotopyData u t).boseShiftedTransportOne 0 := by
  obtain ⟨f, g, hf, hg, hzero, hseven, hfg, hgeq⟩ :=
    exists_thetaCuspC5FirstFacePotentialRepresentation hu
  let P := HTGeometry.c5FirstShiftedFacePotentialGerm f g u
  have hPtop : ContDiff ℝ ∞ P := by
    simpa only [P] using HTGeometry.contDiff_c5FirstShiftedFacePotentialGerm f g u hf hg
  have hP7 : ContinuousAt (iteratedDeriv 7 P) 0 :=
    (HTGeometry.contDiff_top_iteratedDeriv_real P hPtop 7).continuous.continuousAt
  have hPseven : iteratedDeriv 7 P 0 =
      3360 * thetaCuspC5FirstFaceSeamObstruction u := by
    simpa only [P] using hseven
  have hPsevenPos : 0 < iteratedDeriv 7 P 0 := by
    rw [hPseven]
    exact mul_pos (by norm_num)
      (thetaCuspC5FirstFaceSeamObstruction_pos hu.le hscale)
  have hderivEvent : {x : ℝ | 0 < iteratedDeriv 7 P x} ∈ nhds 0 :=
    hP7.eventually (Ioi_mem_nhds hPsevenPos)
  rcases Metric.mem_nhds_iff.mp hderivEvent with ⟨εd, hεd, hballD⟩
  have hactual := eventuallyEq_thetaCuspC5FirstFacePotential_actual hu hf hfg hgeq
  rcases Metric.mem_nhdsWithin_iff.mp hactual with ⟨εa, hεa, hballA⟩
  let δ := min (min εd εa) u
  have hδ : 0 < δ := lt_min (lt_min hεd hεa) hu
  have hδu : δ ≤ u := min_le_right _ _
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  have htd : t < εd := htδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hta : t < εa := htδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hTaylor : taylorWithinEval P 6 (uIcc 0 t) 0 t = 0 := by
    simpa only [P] using firstFacePotential_taylor_six_zero hf hg ht hzero
  have hPOn : ContDiffOn ℝ 7 P (uIcc 0 t) :=
    (hPtop.of_le (by
      change (↑(7 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := P) (x := t) (x₀ := 0) (n := 6) (ne_of_lt ht) hPOn
  rw [uIoo_of_le ht.le] at hx
  have hxball : x ∈ Metric.ball 0 εd := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact hx.2.trans htd
  have hxpos : 0 < iteratedDeriv 7 P x := hballD hxball
  have hPpos : 0 < P t := by
    rw [hTaylor, sub_zero, sub_zero] at hrem
    rw [hrem]
    exact div_pos (mul_pos hxpos (pow_pos ht 7)) (by positivity)
  have htballA : t ∈ Metric.ball 0 εa := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact hta
  have heq := hballA ⟨htballA, ht⟩
  change P t = (thetaCuspC5LikelihoodHomotopyData u t).boseShiftedTransportOne 0 at heq
  rw [← heq]
  exact hPpos

/-- No scale-six positive centre can support the fixed Bose shifted cone on every admissible
right displacement at the first-atom endpoint. -/
theorem not_forall_thetaCuspC5LikelihoodHomotopy_boseShiftedTransportCone_zero
    {u : ℝ} (hu : 0 < u)
    (hscale : 6 < thetaCuspSingleAtomReflectionScale 1 u) :
    ¬ ∀ t : ℝ, 0 < t → t ≤ u →
      6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t) →
      (thetaCuspC5LikelihoodHomotopyData u t).BoseShiftedTransportCone 0 := by
  rcases eventually_thetaCuspC5LikelihoodHomotopy_boseShiftedTransportOne_zero_pos
    hu hscale.le with ⟨δ, hδ, hδu, hpos⟩
  have hscaleCont : ContinuousAt
      (fun t : ℝ => thetaCuspSingleAtomReflectionScale 1 (u - t)) 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    fun_prop
  have hscaleEvent :
      {t : ℝ | 6 < thetaCuspSingleAtomReflectionScale 1 (u - t)} ∈ nhds 0 :=
    hscaleCont.eventually (Ioi_mem_nhds (by simpa using hscale))
  rcases Metric.mem_nhds_iff.mp hscaleEvent with ⟨ε, hε, hball⟩
  intro hcone
  let η := min δ ε
  let t := η / 2
  have hη : 0 < η := lt_min hδ hε
  have ht : 0 < t := by dsimp only [t]; linarith
  have htη : t < η := by dsimp only [t]; linarith
  have htδ : t < δ := htη.trans_le (min_le_left _ _)
  have htε : t < ε := htη.trans_le (min_le_right _ _)
  have htu : t ≤ u := (htδ.trans_le hδu).le
  have htball : t ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact htε
  have hscaleT : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t) :=
    (hball htball).le
  have hface :
      (thetaCuspC5LikelihoodHomotopyData u t).boseShiftedTransportOne 0 ≤ 0 :=
    (hcone t ht htu hscaleT).2.1
  exact (not_lt_of_ge hface) (hpos t ht htδ)

/-- **Conjecture K route kill.** The literal fixed lowest-mode Bose shifted cone is not valid
throughout its claimed physical structural tail. -/
theorem thetaCuspC5LikelihoodHomotopy_conjectureK_false :
    ¬ ∀ (u t l : ℝ), 0 < t → t ≤ u →
      6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t) →
      0 ≤ l → l ≤ 1 →
      (thetaCuspC5LikelihoodHomotopyData u t).BoseShiftedTransportCone l := by
  have hexp : (3 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    norm_num at h ⊢
    exact h
  have hscale : 6 < thetaCuspSingleAtomReflectionScale 1 1 := by
    unfold thetaCuspSingleAtomReflectionScale
    norm_num
    calc
      6 < (3 : ℝ) * 3 := by norm_num
      _ < Real.pi * 3 := mul_lt_mul_of_pos_right Real.pi_gt_three (by norm_num)
      _ < Real.pi * Real.exp 2 := mul_lt_mul_of_pos_left hexp Real.pi_pos
  intro hK
  exact not_forall_thetaCuspC5LikelihoodHomotopy_boseShiftedTransportCone_zero
    (u := 1) (by norm_num) hscale (by
      intro t ht htu hscaleT
      exact hK 1 t 0 ht htu hscaleT (by norm_num) (by norm_num))

end

end RHTower
