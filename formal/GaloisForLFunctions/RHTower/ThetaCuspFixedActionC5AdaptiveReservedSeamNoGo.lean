import GaloisForLFunctions.HTGeometry.AdaptiveReservedC5SeamDefect
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodLiftReduction
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHighSourceJets
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSeventhEighthSourceJets
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionFourthTuran
import Mathlib.Analysis.Calculus.Taylor

/-!
# Adaptive-reserved fixed-action C5 seam no-go

Proof chain under test:

`far-tail direct-J orientation → compact assembly → fixed-action seam → rank-four wall →
CLG/TTF or Weil polarization positivity → RH`.

The adaptive support-gap reserve cannot close the fixed-action seam gate.  Its division-free
margin vanishes through order four, while its fifth seam jet is
`600 * κ^(2 : ℕ) * (F₃ + 2*A*F₂)`.  Existing strict likelihood cooling makes the final factor negative.
Consequently the literal completed adaptive-reserved compensation margin is negative throughout
a punctured right neighbourhood of every positive seam centre.

The positive survivor is the exact defect classification: any viable replacement must preserve
the full third-channel seam cancellation instead of substituting the strict adaptive lower bound.
-/

open scoped BigOperators ContDiff
open Set Filter Topology

namespace RHTower

noncomputable section

private theorem contDiffAt_succ_real_of_eventually_hasDerivAt
    {f g : ℝ → ℝ} {u : ℝ} {n : ℕ}
    (hfg : ∀ᶠ x in nhds u, HasDerivAt f (g x) x)
    (hg : ContDiffAt ℝ n g u) :
    ContDiffAt ℝ (n + 1) f u := by
  rw [contDiffAt_succ_iff_hasFDerivAt]
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨fun x => L (g x), ?_, ?_⟩
  · refine ⟨{x | HasDerivAt f (g x) x}, hfg, fun x hx => ?_⟩
    rw [hasFDerivAt_iff_hasDerivAt]
    simpa [L] using hx
  · have hL : ContDiffAt ℝ n L (g u) :=
      (L.contDiff : ContDiff ℝ n L).contDiffAt
    exact hL.comp u hg

private theorem contDiffAt_five_thetaCuspLikelihoodSourceLogPartitionJetTwo
    {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ 5 thetaCuspLikelihoodSourceLogPartitionJetTwo u := by
  have h7 : ContDiffAt ℝ 0 thetaCuspLikelihoodSourceLogPartitionJetSeven u := by
    rw [contDiffAt_zero]
    refine ⟨Ioi 0, Ioi_mem_nhds hu, ?_⟩
    intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSeven hx.le).continuousAt.continuousWithinAt
  have h6 : ContDiffAt ℝ 1 thetaCuspLikelihoodSourceLogPartitionJetSix u := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt
    · filter_upwards [Ioi_mem_nhds hu] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSix hx.le
    · exact h7
  have h5 : ContDiffAt ℝ 2 thetaCuspLikelihoodSourceLogPartitionJetFive u := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt
    · filter_upwards [Ioi_mem_nhds hu] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive
        (thetaCuspLikelihoodCoordinate_pos hx.le)
    · exact h6
  have h4 : ContDiffAt ℝ 3 thetaCuspLikelihoodSourceLogPartitionJetFour u := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt
    · filter_upwards [Ioi_mem_nhds hu] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour
        (thetaCuspLikelihoodCoordinate_pos hx.le)
    · exact h5
  have h3 : ContDiffAt ℝ 4 thetaCuspLikelihoodSourceLogPartitionJetThree u := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt
    · filter_upwards [Ioi_mem_nhds hu] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
        (thetaCuspLikelihoodCoordinate_pos hx.le)
    · exact h4
  apply contDiffAt_succ_real_of_eventually_hasDerivAt
  · filter_upwards [Ioi_mem_nhds hu] with x hx
    exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx.le)
  · exact h3

private def thetaCuspC5AdaptiveReservedRadius (u t : ℝ) : ℝ :=
  Real.exp (thetaCuspReflectedLogAction u t) - 1

private def thetaCuspC5AtomJetThree (u t : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectedActionJetThree
    (thetaCuspSingleAtomReflectionScale 1 u)
    (thetaCuspSingleAtomReflectionDefect t)
    (2 * Real.sinh (2 * t))

private def thetaCuspC5AtomScaleMixedJetTwo (u t : ℝ) : ℝ :=
  c5SingleAtomScaleMixedJetTwo
    (thetaCuspSingleAtomReflectionScale 1 u)
    (thetaCuspSingleAtomReflectionDefect t)

/-- Division-free adaptive-reserved margin using intrinsic completed-source jets. -/
def thetaCuspC5AdaptiveReservedClearedSeamGerm (u t : ℝ) : ℝ :=
  HTGeometry.c5AdaptiveReservedClearedExpression
    (thetaCuspC5AdaptiveReservedRadius u)
    (thetaCuspReflectedLogJetOne u)
    (thetaCuspReflectedLogJetTwo u)
    (thetaCuspReflectedLogCenterJetOne u)
    (thetaCuspReflectedLogCenterMixedJetOne u)
    (thetaCuspC5AtomJetThree u)
    (thetaCuspC5AtomScaleMixedJetTwo u)
    (c5LikelihoodAdaptiveMasterCurvature u) t

private theorem contDiffAt_five_c5LikelihoodAdaptiveMasterCurvature
    {u t : ℝ} (hp : 0 < u + t) (hm : 0 < u - t) :
    ContDiffAt ℝ 5 (c5LikelihoodAdaptiveMasterCurvature u) t := by
  have hFp := contDiffAt_five_thetaCuspLikelihoodSourceLogPartitionJetTwo hp
  have hFm := contDiffAt_five_thetaCuspLikelihoodSourceLogPartitionJetTwo hm
  have hargp : ContDiffAt ℝ 5 (fun x : ℝ => u + x) t :=
    contDiffAt_const.add contDiffAt_id
  have hargm : ContDiffAt ℝ 5 (fun x : ℝ => u - x) t :=
    contDiffAt_const.sub contDiffAt_id
  have hplus : ContDiffAt ℝ 5
      (fun x => thetaCuspLikelihoodSourceLogPartitionJetTwo (u + x)) t :=
    hFp.comp t hargp
  have hminus : ContDiffAt ℝ 5
      (fun x => thetaCuspLikelihoodSourceLogPartitionJetTwo (u - x)) t :=
    hFm.comp t hargm
  unfold c5LikelihoodAdaptiveMasterCurvature
    thetaCuspSingleAtomReflectionScale
  fun_prop

private theorem contDiffAt_top_thetaCuspC5AtomJetThree
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ContDiffAt ℝ ∞ (thetaCuspC5AtomJetThree u) t := by
  have hsinh : ContDiffAt ℝ ∞ (fun x : ℝ => Real.sinh (2 * x)) t := by
    fun_prop
  have hden : thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0 :=
    (thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
      (n := 1) (by norm_num) ht htu).ne'
  unfold thetaCuspC5AtomJetThree thetaCuspSingleAtomReflectedActionJetThree
    thetaCuspSingleAtomReflectionSlope thetaCuspSingleAtomReflectionFactor
    thetaCuspSingleAtomReflectionDefect
  fun_prop (disch := aesop)

private theorem contDiffAt_top_thetaCuspC5AtomScaleMixedJetTwo
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ContDiffAt ℝ ∞ (thetaCuspC5AtomScaleMixedJetTwo u) t := by
  have hden : thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0 :=
    (thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
      (n := 1) (by norm_num) ht htu).ne'
  unfold thetaCuspC5AtomScaleMixedJetTwo c5SingleAtomScaleMixedJetTwo
    thetaCuspSingleAtomReflectionFactor thetaCuspSingleAtomReflectionDefect
  fun_prop (disch := aesop)

private theorem contDiffAt_top_thetaCuspC5AdaptiveRadius (u t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspC5AdaptiveReservedRadius u) t := by
  have hargp : ContDiffAt ℝ ∞ (fun x : ℝ => u + x) t :=
    contDiffAt_const.add contDiffAt_id
  have hargm : ContDiffAt ℝ ∞ (fun x : ℝ => u - x) t :=
    contDiffAt_const.sub contDiffAt_id
  have hp : ContDiffAt ℝ ∞
      (fun x => thetaCuspLogSource (u + x)) t :=
    contDiff_thetaCuspLogSource.contDiffAt.comp t hargp
  have hm : ContDiffAt ℝ ∞
      (fun x => thetaCuspLogSource (u - x)) t :=
    contDiff_thetaCuspLogSource.contDiffAt.comp t hargm
  unfold thetaCuspC5AdaptiveReservedRadius thetaCuspReflectedLogAction
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogJetOne (u t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogJetOne u) t := by
  unfold thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope
  have h1 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 1
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogJetTwo (u t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogJetTwo u) t := by
  unfold thetaCuspReflectedLogJetTwo thetaCuspLogCurvature
  have h2 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 2
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogCenterJetOne (u t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogCenterJetOne u) t := by
  unfold thetaCuspReflectedLogCenterJetOne thetaCuspLogDecaySlope
  have h1 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 1
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogCenterMixedJetOne (u t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogCenterMixedJetOne u) t := by
  unfold thetaCuspReflectedLogCenterMixedJetOne thetaCuspLogCurvature
  have h2 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 2
  fun_prop

private theorem hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogCenterJetOne u)
      (thetaCuspReflectedLogCenterMixedJetOne u t) t := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (u + t)).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogDecaySlope (u - t)).comp t
    ((hasDerivAt_id t).const_sub u)
  convert (hp.add hm).sub_const (2 * thetaCuspLogDecaySlope u) using 1
  all_goals first | rfl | (simp [thetaCuspReflectedLogCenterMixedJetOne]; ring)

private theorem hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogCenterMixedJetOne u)
      (thetaCuspLogCurvatureJet (u + t) +
        thetaCuspLogCurvatureJet (u - t)) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvature (u + t)).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvature (u - t)).comp t
    ((hasDerivAt_id t).const_sub u)
  convert hp.sub hm using 1
  all_goals first | rfl | simp

private theorem iteratedDeriv_one_thetaCuspReflectedLogCenterJetOne
    (u t : ℝ) :
    iteratedDeriv 1 (thetaCuspReflectedLogCenterJetOne u) t =
      thetaCuspReflectedLogCenterMixedJetOne u t := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement u t).deriv

private theorem iteratedDeriv_two_thetaCuspReflectedLogCenterJetOne
    (u t : ℝ) :
    iteratedDeriv 2 (thetaCuspReflectedLogCenterJetOne u) t =
      thetaCuspLogCurvatureJet (u + t) +
        thetaCuspLogCurvatureJet (u - t) := by
  have hfun : iteratedDeriv 1 (thetaCuspReflectedLogCenterJetOne u) =
      thetaCuspReflectedLogCenterMixedJetOne u := by
    funext x
    exact iteratedDeriv_one_thetaCuspReflectedLogCenterJetOne u x
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, hfun,
    (hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement u t).deriv]

private theorem iteratedDeriv_one_thetaCuspReflectedLogCenterMixedJetOne
    (u t : ℝ) :
    iteratedDeriv 1 (thetaCuspReflectedLogCenterMixedJetOne u) t =
      thetaCuspLogCurvatureJet (u + t) +
        thetaCuspLogCurvatureJet (u - t) := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement u t).deriv

private theorem iteratedDeriv_one_thetaCuspReflectedLogJetOne
    (u t : ℝ) :
    iteratedDeriv 1 (thetaCuspReflectedLogJetOne u) t =
      thetaCuspReflectedLogJetTwo u t := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspReflectedLogJetOne u t).deriv

private theorem c5SingleAtomScaleMixedJetTwo_zero_eq_profile
    {A : ℝ} (hA : 3 < A) :
    c5SingleAtomScaleMixedJetTwo A 0 =
      2 * ((2 * (A - 3 / 2) + 3) *
        (4 - 6 / (A - 3 / 2) ^ (2 : ℕ) - 18 / (A - 3 / 2) ^ (3 : ℕ))) := by
  let q := A - 3 / 2
  have hq : q ≠ 0 := ne_of_gt (by dsimp only [q]; linarith)
  have hAq : A = q + 3 / 2 := by dsimp only [q]; ring
  rw [show c5SingleAtomScaleMixedJetTwo A 0 =
      4 * (4 * A + c5SingleAtomScaleLambdaJetOne A) by
    simp [c5SingleAtomScaleMixedJetTwo,
      thetaCuspSingleAtomReflectionFactor]]
  rw [hAq]
  unfold c5SingleAtomScaleLambdaJetOne
  ring_nf
  field_simp [hq]
  ring

private theorem thetaCuspC5AtomScaleMixedJetTwo_zero_eq
    {u : ℝ} (hu : 0 ≤ u) :
    thetaCuspC5AtomScaleMixedJetTwo u 0 =
      -2 * thetaCuspFirstAtomLogJetThree u := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  have hA : 3 < A := three_lt_thetaCuspSingleAtomReflectionScale
    (n := 1) (by norm_num) hu
  unfold thetaCuspC5AtomScaleMixedJetTwo
  change c5SingleAtomScaleMixedJetTwo A
    (thetaCuspSingleAtomReflectionDefect 0) =
      -2 * thetaCuspFirstAtomLogJetThree u
  rw [show thetaCuspSingleAtomReflectionDefect 0 = 0 by
    simp [thetaCuspSingleAtomReflectionDefect]]
  rw [c5SingleAtomScaleMixedJetTwo_zero_eq_profile hA]
  unfold thetaCuspFirstAtomLogJetThree
    thetaCuspBornWittenLogThirdDerivative
  rw [thetaCuspBornWittenWeight_eq]
  have hscale : thetaCuspMorseScale 1 u = A := by
    dsimp only [A]
    unfold thetaCuspMorseScale thetaCuspSingleAtomReflectionScale
    norm_num
    rw [pow_two, ← Real.exp_add]
    congr 2
    ring
  rw [hscale]
  ring

private theorem iteratedDeriv_one_thetaCuspC5AdaptiveReservedRadius
    (u t : ℝ) :
    iteratedDeriv 1 (thetaCuspC5AdaptiveReservedRadius u) t =
      Real.exp (thetaCuspReflectedLogAction u t) *
        thetaCuspReflectedLogJetOne u t := by
  rw [iteratedDeriv_one]
  exact (((Real.hasDerivAt_exp _).comp t
    (hasDerivAt_thetaCuspReflectedLogAction u t)).sub_const 1).deriv

private theorem thetaCuspC5AdaptiveReservedRadius_jets (u : ℝ) :
    iteratedDeriv 0 (thetaCuspC5AdaptiveReservedRadius u) 0 = 0 ∧
      iteratedDeriv 1 (thetaCuspC5AdaptiveReservedRadius u) 0 = 0 ∧
      iteratedDeriv 2 (thetaCuspC5AdaptiveReservedRadius u) 0 =
        thetaCuspReflectedLogJetTwo u 0 := by
  constructor
  · change Real.exp (thetaCuspReflectedLogAction u 0) - 1 = 0
    rw [show thetaCuspReflectedLogAction u 0 = 0 by
      unfold thetaCuspReflectedLogAction
      ring, Real.exp_zero]
    ring
  constructor
  · rw [iteratedDeriv_one_thetaCuspC5AdaptiveReservedRadius]
    rw [show thetaCuspReflectedLogAction u 0 = 0 by
      unfold thetaCuspReflectedLogAction
      ring, Real.exp_zero,
      show thetaCuspReflectedLogJetOne u 0 = 0 by
        unfold thetaCuspReflectedLogJetOne
        ring]
    ring
  · have hfun : iteratedDeriv 1 (thetaCuspC5AdaptiveReservedRadius u) =
        fun t => Real.exp (thetaCuspReflectedLogAction u t) *
          thetaCuspReflectedLogJetOne u t := by
      funext t
      exact iteratedDeriv_one_thetaCuspC5AdaptiveReservedRadius u t
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, hfun]
    have h := (((Real.hasDerivAt_exp _).comp 0
      (hasDerivAt_thetaCuspReflectedLogAction u 0)).mul
        (hasDerivAt_thetaCuspReflectedLogJetOne u 0)).deriv
    change deriv ((Real.exp ∘ thetaCuspReflectedLogAction u) *
      thetaCuspReflectedLogJetOne u) 0 = thetaCuspReflectedLogJetTwo u 0
    rw [h]
    change Real.exp (thetaCuspReflectedLogAction u 0) *
      thetaCuspReflectedLogJetOne u 0 * thetaCuspReflectedLogJetOne u 0 +
        Real.exp (thetaCuspReflectedLogAction u 0) *
          thetaCuspReflectedLogJetTwo u 0 =
      thetaCuspReflectedLogJetTwo u 0
    rw [show thetaCuspReflectedLogAction u 0 = 0 by
      unfold thetaCuspReflectedLogAction
      ring, Real.exp_zero,
      show thetaCuspReflectedLogJetOne u 0 = 0 by
        unfold thetaCuspReflectedLogJetOne
        ring]
    ring

private theorem thetaCuspC5AdaptiveReservedSource_jets
    {u : ℝ} (hu : 0 < u) :
    let κ := thetaCuspReflectedLogJetTwo u 0
    let N := thetaCuspC5AtomScaleMixedJetTwo u 0
    iteratedDeriv 0 (thetaCuspReflectedLogJetOne u) 0 = 0 ∧
    iteratedDeriv 1 (thetaCuspReflectedLogJetOne u) 0 = κ ∧
    iteratedDeriv 0 (thetaCuspReflectedLogJetTwo u) 0 = κ ∧
    iteratedDeriv 0 (thetaCuspReflectedLogCenterJetOne u) 0 = 0 ∧
    iteratedDeriv 1 (thetaCuspReflectedLogCenterJetOne u) 0 = 0 ∧
    iteratedDeriv 2 (thetaCuspReflectedLogCenterJetOne u) 0 =
      N - 2 * thetaCuspLikelihoodSourceLogPartitionJetThree u ∧
    iteratedDeriv 0 (thetaCuspReflectedLogCenterMixedJetOne u) 0 = 0 ∧
    iteratedDeriv 1 (thetaCuspReflectedLogCenterMixedJetOne u) 0 =
      N - 2 * thetaCuspLikelihoodSourceLogPartitionJetThree u := by
  dsimp only
  have hdecomp :
      2 * thetaCuspLogCurvatureJet u =
        thetaCuspC5AtomScaleMixedJetTwo u 0 -
          2 * thetaCuspLikelihoodSourceLogPartitionJetThree u := by
    have hfull := iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hu
    have hlike :=
      thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hu
    have hatom := thetaCuspC5AtomScaleMixedJetTwo_zero_eq hu.le
    unfold thetaCuspLogCurvatureJet
    rw [hfull, hlike, hatom]
    ring
  constructor
  · simp [iteratedDeriv_zero, thetaCuspReflectedLogJetOne]
  constructor
  · exact iteratedDeriv_one_thetaCuspReflectedLogJetOne u 0
  constructor
  · rfl
  constructor
  · simp [iteratedDeriv_zero, thetaCuspReflectedLogCenterJetOne]
    ring
  constructor
  · rw [iteratedDeriv_one_thetaCuspReflectedLogCenterJetOne]
    simp [thetaCuspReflectedLogCenterMixedJetOne]
  constructor
  · rw [iteratedDeriv_two_thetaCuspReflectedLogCenterJetOne]
    simpa [two_mul] using hdecomp
  constructor
  · simp [iteratedDeriv_zero, thetaCuspReflectedLogCenterMixedJetOne]
  · rw [iteratedDeriv_one_thetaCuspReflectedLogCenterMixedJetOne]
    simpa [two_mul] using hdecomp

private theorem thetaCuspC5AdaptiveMasterCurvature_zero (u : ℝ) :
    iteratedDeriv 0 (c5LikelihoodAdaptiveMasterCurvature u) 0 =
      4 * thetaCuspSingleAtomReflectionScale 1 u *
        thetaCuspLikelihoodSourceLogPartitionJetTwo u := by
  simp [iteratedDeriv_zero, c5LikelihoodAdaptiveMasterCurvature]
  ring

/-- Exact seam classification: four zero jets followed by the uncancelled cooling defect. -/
theorem thetaCuspC5AdaptiveReservedClearedSeamGerm_seamJetClassification
    {u : ℝ} (hu : 0 < u) :
    let κ := thetaCuspReflectedLogJetTwo u 0
    (∀ k < 5,
      iteratedDeriv k (thetaCuspC5AdaptiveReservedClearedSeamGerm u) 0 = 0) ∧
      iteratedDeriv 5 (thetaCuspC5AdaptiveReservedClearedSeamGerm u) 0 =
        600 * κ ^ (2 : ℕ) *
          (thetaCuspLikelihoodSourceLogPartitionJetThree u +
            2 * thetaCuspSingleAtomReflectionScale 1 u *
              thetaCuspLikelihoodSourceLogPartitionJetTwo u) := by
  dsimp only
  rcases thetaCuspC5AdaptiveReservedRadius_jets u with
    ⟨hr0, hr1, hr2⟩
  rcases thetaCuspC5AdaptiveReservedSource_jets hu with
    ⟨ha0, ha1, hb0, hs0, hs1, hs2, hm0, hm1⟩
  have hn₀0 : iteratedDeriv 0 (thetaCuspC5AtomScaleMixedJetTwo u) 0 =
      thetaCuspC5AtomScaleMixedJetTwo u 0 := rfl
  have hZ0 := thetaCuspC5AdaptiveMasterCurvature_zero u
  exact HTGeometry.c5AdaptiveReservedClearedExpression_seamJetClassification
    (thetaCuspC5AdaptiveReservedRadius u)
    (thetaCuspReflectedLogJetOne u)
    (thetaCuspReflectedLogJetTwo u)
    (thetaCuspReflectedLogCenterJetOne u)
    (thetaCuspReflectedLogCenterMixedJetOne u)
    (thetaCuspC5AtomJetThree u)
    (thetaCuspC5AtomScaleMixedJetTwo u)
    (c5LikelihoodAdaptiveMasterCurvature u)
    (contDiffAt_top_thetaCuspC5AdaptiveRadius u 0)
    (contDiffAt_top_thetaCuspReflectedLogJetOne u 0)
    (contDiffAt_top_thetaCuspReflectedLogJetTwo u 0)
    (contDiffAt_top_thetaCuspReflectedLogCenterJetOne u 0)
    (contDiffAt_top_thetaCuspReflectedLogCenterMixedJetOne u 0)
    (contDiffAt_top_thetaCuspC5AtomJetThree (u := u) (t := 0) (by norm_num) hu.le)
    (contDiffAt_top_thetaCuspC5AtomScaleMixedJetTwo
      (u := u) (t := 0) (by norm_num) hu.le)
    (contDiffAt_five_c5LikelihoodAdaptiveMasterCurvature
      (u := u) (t := 0) (by simpa using hu) (by simpa using hu))
    (thetaCuspReflectedLogJetTwo u 0)
    (thetaCuspSingleAtomReflectionScale 1 u)
    (thetaCuspLikelihoodSourceLogPartitionJetTwo u)
    (thetaCuspLikelihoodSourceLogPartitionJetThree u)
    (thetaCuspC5AtomScaleMixedJetTwo u 0)
    hr0 hr1 hr2 ha0 ha1 hb0 hs0 hs1 hs2 hm0 hm1 hn₀0 hZ0

/-- Every cleared adaptive-reserve seam jet below order five vanishes. -/
theorem iteratedDeriv_lt_five_thetaCuspC5AdaptiveReservedClearedSeamGerm
    {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : k < 5) :
    iteratedDeriv k (thetaCuspC5AdaptiveReservedClearedSeamGerm u) 0 = 0 :=
  (thetaCuspC5AdaptiveReservedClearedSeamGerm_seamJetClassification hu).1 k hk

/-- Exact first nonzero seam jet of the source-specialized cleared margin. -/
theorem iteratedDeriv_five_thetaCuspC5AdaptiveReservedClearedSeamGerm
    {u : ℝ} (hu : 0 < u) :
    let κ := thetaCuspReflectedLogJetTwo u 0
    iteratedDeriv 5 (thetaCuspC5AdaptiveReservedClearedSeamGerm u) 0 =
      600 * κ ^ (2 : ℕ) *
        (thetaCuspLikelihoodSourceLogPartitionJetThree u +
          2 * thetaCuspSingleAtomReflectionScale 1 u *
            thetaCuspLikelihoodSourceLogPartitionJetTwo u) :=
  (thetaCuspC5AdaptiveReservedClearedSeamGerm_seamJetClassification hu).2

private theorem contDiffAt_five_thetaCuspC5AdaptiveReservedClearedSeamGerm
    {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) (htu : t < u) :
    ContDiffAt ℝ 5 (thetaCuspC5AdaptiveReservedClearedSeamGerm u) t := by
  have hr := contDiffAt_top_thetaCuspC5AdaptiveRadius u t
  have ha := contDiffAt_top_thetaCuspReflectedLogJetOne u t
  have hb := contDiffAt_top_thetaCuspReflectedLogJetTwo u t
  have hs := contDiffAt_top_thetaCuspReflectedLogCenterJetOne u t
  have hm := contDiffAt_top_thetaCuspReflectedLogCenterMixedJetOne u t
  have hc₀ := contDiffAt_top_thetaCuspC5AtomJetThree
    (u := u) (t := t) ht htu.le
  have hn₀ := contDiffAt_top_thetaCuspC5AtomScaleMixedJetTwo
    (u := u) (t := t) ht htu.le
  have hZ := contDiffAt_five_c5LikelihoodAdaptiveMasterCurvature
    (u := u) (t := t) (by linarith) (by linarith)
  have hr5 : ContDiffAt ℝ 5 (thetaCuspC5AdaptiveReservedRadius u) t :=
    hr.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))
  have ha5 : ContDiffAt ℝ 5 (thetaCuspReflectedLogJetOne u) t :=
    ha.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))
  have hb5 : ContDiffAt ℝ 5 (thetaCuspReflectedLogJetTwo u) t :=
    hb.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))
  have hs5 : ContDiffAt ℝ 5 (thetaCuspReflectedLogCenterJetOne u) t :=
    hs.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))
  have hm5 : ContDiffAt ℝ 5 (thetaCuspReflectedLogCenterMixedJetOne u) t :=
    hm.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))
  have hc₀5 : ContDiffAt ℝ 5 (thetaCuspC5AtomJetThree u) t :=
    hc₀.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))
  have hn₀5 : ContDiffAt ℝ 5 (thetaCuspC5AtomScaleMixedJetTwo u) t :=
    hn₀.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))
  unfold thetaCuspC5AdaptiveReservedClearedSeamGerm
    HTGeometry.c5AdaptiveReservedClearedExpression
  dsimp only
  fun_prop

private theorem continuousAt_iteratedDeriv_of_contDiffAt_real
    {f : ℝ → ℝ} {x : ℝ} {i : ℕ}
    (h : ContDiffAt ℝ i f x) :
    ContinuousAt (iteratedDeriv i f) x := by
  have hF : ContinuousAt (iteratedFDeriv ℝ i f) x :=
    h.continuousAt_iteratedFDeriv le_rfl
  have happ : Continuous
      (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝ) ℝ =>
        T (fun _ => 1)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => ℝ) ℝ
      (fun _ => 1)).continuous
  have hc : ContinuousAt
      (fun y => (iteratedFDeriv ℝ i f y) (fun _ => 1)) x :=
    happ.continuousAt.comp hF
  have hfun : iteratedDeriv i f =
      fun y => (iteratedFDeriv ℝ i f y) (fun _ => 1) := by
    funext y
    rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hfun]
  exact hc

/-- Strict likelihood cooling forces the exact fifth seam jet to be negative. -/
theorem iteratedDeriv_five_thetaCuspC5AdaptiveReservedClearedSeamGerm_neg
    {u : ℝ} (hu : 0 < u) :
    iteratedDeriv 5 (thetaCuspC5AdaptiveReservedClearedSeamGerm u) 0 < 0 := by
  rw [iteratedDeriv_five_thetaCuspC5AdaptiveReservedClearedSeamGerm hu]
  have hκ : 0 < thetaCuspReflectedLogJetTwo u 0 := by
    rw [thetaCuspReflectedLogJetTwo_zero]
    exact mul_pos (by norm_num) (thetaCuspLogCurvature_pos u)
  have hcool :=
    two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
      hu.le
  have hdefect :
      thetaCuspLikelihoodSourceLogPartitionJetThree u +
          2 * thetaCuspSingleAtomReflectionScale 1 u *
            thetaCuspLikelihoodSourceLogPartitionJetTwo u < 0 := by
    linarith
  exact mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) (sq_pos_of_pos hκ)) hdefect

private def c5AdaptiveIteratedTaylorShift
    (f : ℝ → ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    iteratedDeriv k f x * r ^ k / (k.factorial : ℝ)

private theorem taylorWithinEval_add_eq_c5AdaptiveIteratedTaylorShift
    {f : ℝ → ℝ} {x r : ℝ}
    (hf : ContDiffAt ℝ 5 f x) (hr : 0 < r) (j : ℕ) (hj : j ≤ 4) :
    taylorWithinEval f j (uIcc x (x + r)) x (x + r) =
      c5AdaptiveIteratedTaylorShift f j r x := by
  have hle : x ≤ x + r := by linarith
  rw [uIcc_of_le hle]
  induction j with
  | zero =>
      simp [c5AdaptiveIteratedTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih (by omega)]
      simp only [c5AdaptiveIteratedTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) f (Icc x (x + r)) x =
          iteratedDeriv (j + 1) f x := by
        have hj5 : ((j + 1 : ℕ) : WithTop ℕ∞) ≤ (5 : WithTop ℕ∞) := by
          exact_mod_cast (show j + 1 ≤ 5 by omega)
        have hf' : ContDiffAt ℝ (j + 1) f x := hf.of_le hj5
        exact iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by linarith))
          hf'
          (left_mem_Icc.mpr hle)
      rw [hderiv, Nat.factorial_succ]
      push_cast
      ring

private theorem thetaCuspC5AdaptiveReservedClearedSeamGerm_taylor_four_zero
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (htu : t < u) :
    taylorWithinEval (thetaCuspC5AdaptiveReservedClearedSeamGerm u) 4
      (uIcc 0 t) 0 t = 0 := by
  have hTaylor := taylorWithinEval_add_eq_c5AdaptiveIteratedTaylorShift
    (f := thetaCuspC5AdaptiveReservedClearedSeamGerm u)
    (x := 0) (r := t)
    (contDiffAt_five_thetaCuspC5AdaptiveReservedClearedSeamGerm
      hu (by norm_num) (by linarith)) ht 4 (by norm_num)
  simpa only [zero_add] using hTaylor.trans (by
    unfold c5AdaptiveIteratedTaylorShift
    apply Finset.sum_eq_zero
    intro k hk
    rw [iteratedDeriv_lt_five_thetaCuspC5AdaptiveReservedClearedSeamGerm
      hu (Finset.mem_range.mp hk)]
    simp)

/-- The cleared adaptive-reserved germ is negative immediately right of every positive seam. -/
theorem eventually_thetaCuspC5AdaptiveReservedClearedSeamGerm_neg
    {u : ℝ} (hu : 0 < u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      thetaCuspC5AdaptiveReservedClearedSeamGerm u t < 0 := by
  let f := thetaCuspC5AdaptiveReservedClearedSeamGerm u
  have hf0 : ContDiffAt ℝ 5 f 0 := by
    simpa only [f] using
      contDiffAt_five_thetaCuspC5AdaptiveReservedClearedSeamGerm
        hu (by norm_num) hu
  have hf5 : ContinuousAt (iteratedDeriv 5 f) 0 :=
    continuousAt_iteratedDeriv_of_contDiffAt_real hf0
  have hneg0 : iteratedDeriv 5 f 0 < 0 := by
    simpa only [f] using
      iteratedDeriv_five_thetaCuspC5AdaptiveReservedClearedSeamGerm_neg hu
  have hevent : {x : ℝ | iteratedDeriv 5 f x < 0} ∈ nhds 0 :=
    hf5.eventually (Iio_mem_nhds hneg0)
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  let δ := min ε u
  have hδ : 0 < δ := lt_min hε hu
  have hδu : δ ≤ u := min_le_right _ _
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  have htu : t < u := lt_of_lt_of_le htδ hδu
  have hfOn : ContDiffOn ℝ 5 f (uIcc 0 t) := by
    rw [uIcc_of_le ht.le]
    intro x hx
    exact (contDiffAt_five_thetaCuspC5AdaptiveReservedClearedSeamGerm
      hu hx.1 (lt_of_le_of_lt hx.2 htu)).contDiffWithinAt
  have hTaylor : taylorWithinEval f 4 (uIcc 0 t) 0 t = 0 := by
    simpa only [f] using
      thetaCuspC5AdaptiveReservedClearedSeamGerm_taylor_four_zero hu ht htu
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x := t) (x₀ := 0) (n := 4) (ne_of_lt ht) hfOn
  rw [uIoo_of_le ht.le] at hx
  have hxball : x ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact hx.2.trans (htδ.trans_le (min_le_left _ _))
  have hxneg : iteratedDeriv 5 f x < 0 := hball hxball
  rw [hTaylor, sub_zero, sub_zero] at hrem
  change f t < 0
  rw [hrem]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hxneg (pow_pos ht 5))
    (by positivity)

/-- Away from the seam, the cleared germ is the positive radius times the literal completed
adaptive-reserved compensation margin. -/
theorem thetaCuspC5AdaptiveReservedClearedSeamGerm_eq_completedMargin
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspC5AdaptiveReservedClearedSeamGerm u t =
      (Real.exp (thetaCuspCompletedReflectedCumulantAction u t) - 1) *
        c5CompletedAdaptiveReservedCompensationMargin u t := by
  have hr : Real.exp (thetaCuspCompletedReflectedCumulantAction u t) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr
        (thetaCuspCompletedReflectedCumulantAction_pos ht htu.le))
  unfold thetaCuspC5AdaptiveReservedClearedSeamGerm
    HTGeometry.c5AdaptiveReservedClearedExpression
    thetaCuspC5AdaptiveReservedRadius
    c5CompletedAdaptiveReservedCompensationMargin
    c5CompletedLowerJetCompensationMargin
    c5CompletedVelocityCenterNumerator
    c5CompletedVelocitySlopeLowerJetNumerator
  rw [thetaCuspReflectedLogAction_eq_completed ht.le htu.le,
    thetaCuspReflectedLogJetOne_eq_completed ht htu,
    thetaCuspReflectedLogJetTwo_eq_completed ht htu,
    thetaCuspReflectedLogCenterJetOne_eq_completed ht htu,
    thetaCuspReflectedLogCenterMixedJetOne_eq_completed ht htu]
  unfold thetaCuspC5AtomJetThree
    thetaCuspC5AtomScaleMixedJetTwo
  dsimp only
  field_simp [hr]
  ring

/-- The literal completed adaptive-reserved margin is negative near every positive seam centre. -/
theorem eventually_c5CompletedAdaptiveReservedCompensationMargin_neg
    {u : ℝ} (hu : 0 < u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      c5CompletedAdaptiveReservedCompensationMargin u t < 0 := by
  rcases eventually_thetaCuspC5AdaptiveReservedClearedSeamGerm_neg hu with
    ⟨δ, hδ, hδu, hlocal⟩
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  have htu : t < u := lt_of_lt_of_le htδ hδu
  have hG := hlocal t ht htδ
  rw [thetaCuspC5AdaptiveReservedClearedSeamGerm_eq_completedMargin ht htu] at hG
  have hrpos : 0 < Real.exp (thetaCuspCompletedReflectedCumulantAction u t) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr
      (thetaCuspCompletedReflectedCumulantAction_pos ht htu.le)
  have hG' : c5CompletedAdaptiveReservedCompensationMargin u t *
      (Real.exp (thetaCuspCompletedReflectedCumulantAction u t) - 1) < 0 := by
    simpa only [mul_comm] using hG
  exact neg_of_mul_neg_left hG' hrpos.le

/-- No positive seam centre admits universal nonnegativity of the adaptive-reserved margin. -/
theorem not_forall_c5CompletedAdaptiveReservedCompensationMargin_nonneg
    {u : ℝ} (hu : 0 < u) :
    ¬ ∀ t : ℝ, 0 < t → t < u →
      0 ≤ c5CompletedAdaptiveReservedCompensationMargin u t := by
  rcases eventually_c5CompletedAdaptiveReservedCompensationMargin_neg hu with
    ⟨δ, hδ, hδu, hlocal⟩
  intro hnonneg
  let t := δ / 2
  have ht : 0 < t := by dsimp only [t]; linarith
  have htδ : t < δ := by dsimp only [t]; linarith
  have htu : t < u := lt_of_lt_of_le htδ hδu
  exact (not_lt_of_ge (hnonneg t ht htu)) (hlocal t ht htδ)

end

end RHTower
