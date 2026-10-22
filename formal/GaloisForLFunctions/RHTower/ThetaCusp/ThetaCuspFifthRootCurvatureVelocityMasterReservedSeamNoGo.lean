import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureVelocityFirstAtomCurvatureSeamNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSeventhEighthSourceJets
import Mathlib.Analysis.Calculus.Taylor

/-!
# Theta C5 center velocity: master-reserved seam no-go

Proof chain under test:

`global master-reserved-core nonnegativity → strict modular-center velocity → center C5 →
fixed-action transport → CLG/TTF or Weil polarization positivity → RH`.

The master reserve replaces the literal third likelihood jet by six units of likelihood curvature.
This module proves that replacement cannot close the center-velocity gate.  The exact second-channel
cubic cancellation survives, but strict support-gap cooling introduces a negative fourth-order seam
defect.  A smooth proxy equal to the master core on the positive physical ray vanishes through order
three and has fourth seam jet

`120 * k * (G₃ + 6 * G₂) < 0`.

Taylor transfer therefore makes the master core strictly negative immediately right of the seam and
kills its global-nonnegativity branch.  The sharp positive survivor is structural: a viable C5-VP1
argument must retain the full third likelihood channel exactly; every uniform six-curvature reserve
breaks the seam cancellation one order later.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

def c5VelocityCoolingDefectExpression
    (r g₂ g₃ : ℝ → ℝ) (t : ℝ) : ℝ :=
  10 * r t * t ^ (2 : ℕ) * (g₃ t + 6 * g₂ t)

theorem c5VelocityCoolingDefectExpression_seamJetClassification
    (r g₂ g₃ : ℝ → ℝ)
    (hr : ContDiffAt ℝ 4 r 0)
    (hg₂ : ContDiffAt ℝ 4 g₂ 0)
    (hg₃ : ContDiffAt ℝ 4 g₃ 0)
    (k G₂ G₃ : ℝ)
    (hr0 : iteratedDeriv 0 r 0 = 0)
    (hr1 : iteratedDeriv 1 r 0 = 0)
    (hr2 : iteratedDeriv 2 r 0 = k)
    (hg₂0 : iteratedDeriv 0 g₂ 0 = G₂)
    (hg₃0 : iteratedDeriv 0 g₃ 0 = G₃) :
    (∀ j < 4,
      iteratedDeriv j (c5VelocityCoolingDefectExpression r g₂ g₃) 0 = 0) ∧
      iteratedDeriv 4 (c5VelocityCoolingDefectExpression r g₂ g₃) 0 =
        120 * k * (G₃ + 6 * G₂) := by
  let x : ℝ → ℝ := id
  let x2 : ℝ → ℝ := fun t => x t * x t
  let h : ℝ → ℝ := fun t => g₃ t + 6 * g₂ t
  let rx2 : ℝ → ℝ := fun t => r t * x2 t
  let defect : ℝ → ℝ := fun t => 10 * (rx2 t * h t)
  have hxTop : ContDiffAt ℝ ∞ x 0 := by
    simpa only [x] using
      (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) 0)
  have hx2Top : ContDiffAt ℝ ∞ x2 0 := by
    simpa only [x2] using hxTop.mul hxTop
  have hx : ContDiffAt ℝ 4 x 0 := hxTop.of_le
    (by exact WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))
  have hx2 : ContDiffAt ℝ 4 x2 0 := hx2Top.of_le
    (by exact WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))
  have hh : ContDiffAt ℝ 4 h 0 := by
    dsimp only [h]
    fun_prop
  have hrx2 : ContDiffAt ℝ 4 rx2 0 := by
    simpa only [rx2] using hr.mul hx2
  have hmul (f g : ℝ → ℝ) (hf : ContDiffAt ℝ 4 f 0)
      (hg : ContDiffAt ℝ 4 g 0) (j : ℕ) (hj : j ≤ 4) :
      iteratedDeriv j (fun t => f t * g t) 0 =
        realScalarJetConvolution
          (fun i => iteratedDeriv i f 0)
          (fun i => iteratedDeriv i g 0) j := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.of_le (by exact_mod_cast hj)) (hg.of_le (by exact_mod_cast hj))
  have hmulTop (f g : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
      (hg : ContDiffAt ℝ ∞ g 0) (j : ℕ) :
      iteratedDeriv j (fun t => f t * g t) 0 =
        realScalarJetConvolution
          (fun i => iteratedDeriv i f 0)
          (fun i => iteratedDeriv i g 0) j := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
  have hxj (j : ℕ) : iteratedDeriv j x 0 = realScalarJetId j := by
    rcases j with _ | _ | j <;> simp [x, realScalarJetId, iteratedDeriv_id]
  have hx2j (j : ℕ) : iteratedDeriv j x2 0 =
      realScalarJetConvolution realScalarJetId realScalarJetId j := by
    rw [show iteratedDeriv j x2 0 =
      iteratedDeriv j (fun t => x t * x t) 0 by rfl,
      hmulTop x x hxTop hxTop j]
    simp only [hxj]
  have hrx2j (j : ℕ) (hj : j ≤ 4) : iteratedDeriv j rx2 0 =
      realScalarJetConvolution
        (fun i => iteratedDeriv i r 0)
        (realScalarJetConvolution realScalarJetId realScalarJetId) j := by
    rw [show iteratedDeriv j rx2 0 =
      iteratedDeriv j (fun t => r t * x2 t) 0 by rfl,
      hmul r x2 hr hx2 j hj]
    simp only [hx2j]
  have hh0 : iteratedDeriv 0 h 0 = G₃ + 6 * G₂ := by
    change g₂ 0 = G₂ at hg₂0
    change g₃ 0 = G₃ at hg₃0
    simp [h, iteratedDeriv_zero, hg₂0, hg₃0]
  have hdefectj (j : ℕ) (hj : j ≤ 4) : iteratedDeriv j defect 0 =
      10 * realScalarJetConvolution
        (fun i => iteratedDeriv i rx2 0)
        (fun i => iteratedDeriv i h 0) j := by
    dsimp only [defect]
    rw [iteratedDeriv_const_mul 10
      ((hrx2.mul hh).of_le (by exact_mod_cast hj)),
      hmul rx2 h hrx2 hh j hj]
  have hrx20 : iteratedDeriv 0 rx2 0 = 0 := by
    rw [hrx2j 0 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0]
  have hrx21 : iteratedDeriv 1 rx2 0 = 0 := by
    rw [hrx2j 1 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0, hr1]
  have hrx22 : iteratedDeriv 2 rx2 0 = 0 := by
    rw [hrx2j 2 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0, hr1, hr2]
  have hrx23 : iteratedDeriv 3 rx2 0 = 0 := by
    rw [hrx2j 3 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0, hr1, hr2]
  have hrx24 : iteratedDeriv 4 rx2 0 = 12 * k := by
    rw [hrx2j 4 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0, hr1, hr2]
    ring
  have h0 : iteratedDeriv 0 defect 0 = 0 := by
    rw [hdefectj 0 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hrx20]
  have h1 : iteratedDeriv 1 defect 0 = 0 := by
    rw [hdefectj 1 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hrx20, hrx21]
  have h2 : iteratedDeriv 2 defect 0 = 0 := by
    rw [hdefectj 2 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hrx20, hrx21, hrx22]
  have h3 : iteratedDeriv 3 defect 0 = 0 := by
    rw [hdefectj 3 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hrx20, hrx21, hrx22, hrx23]
  have h4 : iteratedDeriv 4 defect 0 = 120 * k * (G₃ + 6 * G₂) := by
    rw [hdefectj 4 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hrx20, hrx21, hrx22, hrx23,
      hrx24, hh0]
    ring
  have hsame : defect = c5VelocityCoolingDefectExpression r g₂ g₃ := by
    funext t
    dsimp only [defect, rx2, h, x2, x]
    unfold c5VelocityCoolingDefectExpression
    simp only [id_eq]
    ring
  rw [← hsame]
  exact ⟨fun j hj => by interval_cases j <;> assumption, h4⟩

end

end HTGeometry

open Set Filter Topology

namespace RHTower

noncomputable section

open HTGeometry

private def thetaCuspC5MasterSeamRadius (t : ℝ) : ℝ :=
  Real.exp (thetaCuspReflectedLogAction 0 t) - 1

/-- Literal center action core, extended smoothly across the seam. -/
def thetaCuspCenterFifthRootVelocityLiteralActionCore (t : ℝ) : ℝ :=
  HTGeometry.c5VelocityFirstAtomCurvatureExpression
    thetaCuspC5MasterSeamRadius
    (thetaCuspReflectedLogJetOne 0)
    (thetaCuspReflectedLogJetTwo 0)
    (thetaCuspReflectedLogJetThree 0) t

private theorem contDiffAt_top_thetaCuspC5MasterSeamRadius (t : ℝ) :
    ContDiffAt ℝ ∞ thetaCuspC5MasterSeamRadius t := by
  have hargp : ContDiffAt ℝ ∞ (fun x : ℝ => 0 + x) t :=
    contDiffAt_const.add contDiffAt_id
  have hargm : ContDiffAt ℝ ∞ (fun x : ℝ => 0 - x) t :=
    contDiffAt_const.sub contDiffAt_id
  have hp : ContDiffAt ℝ ∞
      (fun x => thetaCuspLogSource (0 + x)) t :=
    contDiff_thetaCuspLogSource.contDiffAt.comp t hargp
  have hm : ContDiffAt ℝ ∞
      (fun x => thetaCuspLogSource (0 - x)) t :=
    contDiff_thetaCuspLogSource.contDiffAt.comp t hargm
  unfold thetaCuspC5MasterSeamRadius thetaCuspReflectedLogAction
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogJetOne_zero (t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogJetOne 0) t := by
  unfold thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope
  have h1 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 1
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogJetTwo_zero (t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogJetTwo 0) t := by
  unfold thetaCuspReflectedLogJetTwo thetaCuspLogCurvature
  have h2 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 2
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogJetThree_zero (t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogJetThree 0) t := by
  unfold thetaCuspReflectedLogJetThree thetaCuspLogCurvatureJet
  have h3 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 3
  fun_prop

private theorem contDiffAt_top_thetaCuspCenterFifthRootVelocityLiteralActionCore
    (t : ℝ) :
    ContDiffAt ℝ ∞ thetaCuspCenterFifthRootVelocityLiteralActionCore t := by
  have hr := contDiffAt_top_thetaCuspC5MasterSeamRadius t
  have ha := contDiffAt_top_thetaCuspReflectedLogJetOne_zero t
  have hb := contDiffAt_top_thetaCuspReflectedLogJetTwo_zero t
  have hc := contDiffAt_top_thetaCuspReflectedLogJetThree_zero t
  unfold thetaCuspCenterFifthRootVelocityLiteralActionCore
    HTGeometry.c5VelocityFirstAtomCurvatureExpression
  fun_prop

private theorem thetaCuspC5MasterSeamRadius_jets :
    iteratedDeriv 0 thetaCuspC5MasterSeamRadius 0 = 0 ∧
      iteratedDeriv 1 thetaCuspC5MasterSeamRadius 0 = 0 ∧
      iteratedDeriv 2 thetaCuspC5MasterSeamRadius 0 =
        thetaCuspReflectedLogJetTwo 0 0 := by
  constructor
  · change Real.exp (thetaCuspReflectedLogAction 0 0) - 1 = 0
    rw [show thetaCuspReflectedLogAction 0 0 = 0 by
      unfold thetaCuspReflectedLogAction
      ring, Real.exp_zero]
    ring
  constructor
  · rw [iteratedDeriv_one]
    exact ((((Real.hasDerivAt_exp _).comp 0
      (hasDerivAt_thetaCuspReflectedLogAction 0 0)).sub_const 1).deriv.trans (by
        change Real.exp (thetaCuspReflectedLogAction 0 0) *
            thetaCuspReflectedLogJetOne 0 0 = 0
        rw [show thetaCuspReflectedLogJetOne 0 0 = 0 by
          unfold thetaCuspReflectedLogJetOne
          ring]
        ring))
  · have hfun : iteratedDeriv 1 thetaCuspC5MasterSeamRadius =
        fun t => Real.exp (thetaCuspReflectedLogAction 0 t) *
          thetaCuspReflectedLogJetOne 0 t := by
      funext t
      rw [iteratedDeriv_one]
      exact (((Real.hasDerivAt_exp _).comp t
        (hasDerivAt_thetaCuspReflectedLogAction 0 t)).sub_const 1).deriv
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, hfun]
    have h := (((Real.hasDerivAt_exp _).comp 0
      (hasDerivAt_thetaCuspReflectedLogAction 0 0)).mul
        (hasDerivAt_thetaCuspReflectedLogJetOne 0 0)).deriv
    change deriv ((Real.exp ∘ thetaCuspReflectedLogAction 0) *
      thetaCuspReflectedLogJetOne 0) 0 = thetaCuspReflectedLogJetTwo 0 0
    rw [h]
    change Real.exp (thetaCuspReflectedLogAction 0 0) *
      thetaCuspReflectedLogJetOne 0 0 * thetaCuspReflectedLogJetOne 0 0 +
        Real.exp (thetaCuspReflectedLogAction 0 0) *
          thetaCuspReflectedLogJetTwo 0 0 = thetaCuspReflectedLogJetTwo 0 0
    rw [show thetaCuspReflectedLogAction 0 0 = 0 by
      unfold thetaCuspReflectedLogAction
      ring, Real.exp_zero,
      show thetaCuspReflectedLogJetOne 0 0 = 0 by
        unfold thetaCuspReflectedLogJetOne
        ring]
    ring

theorem thetaCuspCenterFifthRootVelocityLiteralActionCore_odd
    (t : ℝ) :
    thetaCuspCenterFifthRootVelocityLiteralActionCore (-t) =
      -thetaCuspCenterFifthRootVelocityLiteralActionCore t := by
  have hr : thetaCuspC5MasterSeamRadius (-t) =
      thetaCuspC5MasterSeamRadius t := by
    unfold thetaCuspC5MasterSeamRadius thetaCuspReflectedLogAction
    congr 2
    ring
  have ha : thetaCuspReflectedLogJetOne 0 (-t) =
      -thetaCuspReflectedLogJetOne 0 t := by
    unfold thetaCuspReflectedLogJetOne
    ring
  have hb : thetaCuspReflectedLogJetTwo 0 (-t) =
      thetaCuspReflectedLogJetTwo 0 t := by
    unfold thetaCuspReflectedLogJetTwo
    ring
  have hc : thetaCuspReflectedLogJetThree 0 (-t) =
      -thetaCuspReflectedLogJetThree 0 t := by
    unfold thetaCuspReflectedLogJetThree
    ring
  unfold thetaCuspCenterFifthRootVelocityLiteralActionCore
    HTGeometry.c5VelocityFirstAtomCurvatureExpression
  rw [hr, ha, hb, hc]
  ring

private theorem iteratedDeriv_four_zero_of_odd
    (f : ℝ → ℝ) (hodd : ∀ t, f (-t) = -f t) :
    iteratedDeriv 4 f 0 = 0 := by
  have hfun : (fun t => f (-t)) = -f := by
    funext t
    exact hodd t
  have h := congrFun (congrArg (iteratedDeriv 4) hfun) 0
  rw [iteratedDeriv_comp_neg, iteratedDeriv_neg] at h
  norm_num at h
  linarith

theorem thetaCuspCenterFifthRootVelocityLiteralActionCore_seamJetClassification :
    (∀ j < 5,
      iteratedDeriv j thetaCuspCenterFifthRootVelocityLiteralActionCore 0 = 0) := by
  rcases thetaCuspC5MasterSeamRadius_jets with ⟨hr0, hr1, hr2⟩
  have ha0 : iteratedDeriv 0 (thetaCuspReflectedLogJetOne 0) 0 = 0 := by
    simp [iteratedDeriv_zero, thetaCuspReflectedLogJetOne]
  have ha1 : iteratedDeriv 1 (thetaCuspReflectedLogJetOne 0) 0 =
      thetaCuspReflectedLogJetTwo 0 0 := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_thetaCuspReflectedLogJetOne 0 0).deriv
  have hb0 : iteratedDeriv 0 (thetaCuspReflectedLogJetTwo 0) 0 =
      thetaCuspReflectedLogJetTwo 0 0 := rfl
  have hlow :=
    HTGeometry.c5VelocityFirstAtomCurvatureExpression_seamJetClassification
      thetaCuspC5MasterSeamRadius
      (thetaCuspReflectedLogJetOne 0)
      (thetaCuspReflectedLogJetTwo 0)
      (thetaCuspReflectedLogJetThree 0)
      (contDiffAt_top_thetaCuspC5MasterSeamRadius 0)
      (contDiffAt_top_thetaCuspReflectedLogJetOne_zero 0)
      (contDiffAt_top_thetaCuspReflectedLogJetTwo_zero 0)
      (contDiffAt_top_thetaCuspReflectedLogJetThree_zero 0)
      (thetaCuspReflectedLogJetTwo 0 0)
      (thetaCuspReflectedLogJetTwo 0 0)
      hr0 hr1 hr2 ha0 ha1 hb0
  change (∀ j < 3,
      iteratedDeriv j thetaCuspCenterFifthRootVelocityLiteralActionCore 0 = 0) ∧
    iteratedDeriv 3 thetaCuspCenterFifthRootVelocityLiteralActionCore 0 =
      15 * thetaCuspReflectedLogJetTwo 0 0 *
        (thetaCuspReflectedLogJetTwo 0 0 -
          thetaCuspReflectedLogJetTwo 0 0) at hlow
  have hfour : iteratedDeriv 4
      thetaCuspCenterFifthRootVelocityLiteralActionCore 0 = 0 :=
    iteratedDeriv_four_zero_of_odd
      thetaCuspCenterFifthRootVelocityLiteralActionCore
      thetaCuspCenterFifthRootVelocityLiteralActionCore_odd
  intro j hj
  interval_cases j
  · exact hlow.1 0 (by norm_num)
  · exact hlow.1 1 (by norm_num)
  · exact hlow.1 2 (by norm_num)
  · simpa only [sub_self, mul_zero] using hlow.2
  · exact hfour

private theorem contDiffAt_succ_real_of_eventually_hasDerivAt_masterSeam
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

private theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSix_of_coordinate_pos
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetSix
      (thetaCuspLikelihoodSourceLogPartitionJetSeven x) x := by
  have hA := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  have hm := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x hcoord
  have hv := (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x hcoord
  have hk3 := (hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp x hcoord
  have hk4 := (hasDerivAt_thetaCuspLikelihoodFourthCumulant hB).comp x hcoord
  have hk5 := (hasDerivAt_thetaCuspLikelihoodFifthCumulant hB).comp x hcoord
  have hk6 := (hasDerivAt_thetaCuspLikelihoodSixthCumulant hB).comp x hcoord
  have h0 := ((hA.pow 6).mul hk6).const_mul 64
  have h1 := h0.sub (((hA.pow 5).mul hk5).const_mul 960)
  have h2 := h1.add (((hA.pow 4).mul hk4).const_mul 4160)
  have h3 := h2.sub (((hA.pow 3).mul hk3).const_mul 5760)
  have h4 := h3.add (((hA.pow 2).mul hv).const_mul 1984)
  have hraw := h4.sub ((hA.mul hm).const_mul 64)
  unfold thetaCuspLikelihoodSourceLogPartitionJetSix
    thetaCuspLikelihoodSourceLogPartitionJetSeven
  convert hraw using 1
  any_goals rfl
  · funext y
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Function.comp_apply, Pi.pow_apply]
    ring

private theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSeven_of_coordinate_pos
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetSeven
      (thetaCuspLikelihoodSourceLogPartitionJetEight x) x := by
  have hA := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  have hm := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x hcoord
  have hv := (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x hcoord
  have hk3 := (hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp x hcoord
  have hk4 := (hasDerivAt_thetaCuspLikelihoodFourthCumulant hB).comp x hcoord
  have hk5 := (hasDerivAt_thetaCuspLikelihoodFifthCumulant hB).comp x hcoord
  have hk6 := (hasDerivAt_thetaCuspLikelihoodSixthCumulant hB).comp x hcoord
  have hk7 := (hasDerivAt_thetaCuspLikelihoodSeventhCumulant hB).comp x hcoord
  have h0 := ((hA.pow 7).mul hk7).const_mul (-128)
  have h1 := h0.add (((hA.pow 6).mul hk6).const_mul 2688)
  have h2 := h1.sub (((hA.pow 5).mul hk5).const_mul 17920)
  have h3 := h2.add (((hA.pow 4).mul hk4).const_mul 44800)
  have h4 := h3.sub (((hA.pow 3).mul hk3).const_mul 38528)
  have h5 := h4.add (((hA.pow 2).mul hv).const_mul 8064)
  have hraw := h5.sub ((hA.mul hm).const_mul 128)
  unfold thetaCuspLikelihoodSourceLogPartitionJetSeven
    thetaCuspLikelihoodSourceLogPartitionJetEight
  convert hraw using 1
  any_goals rfl
  · funext y
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Function.comp_apply, Pi.pow_apply]
    ring

private theorem thetaCuspLikelihoodHighJets_contDiffAt_four
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ 4 thetaCuspLikelihoodSourceLogPartitionJetTwo t ∧
      ContDiffAt ℝ 4 thetaCuspLikelihoodSourceLogPartitionJetThree t := by
  have hB : 0 < thetaCuspLikelihoodCoordinate t :=
    thetaCuspLikelihoodCoordinate_pos ht
  have hcoord : ContinuousAt thetaCuspLikelihoodCoordinate t :=
    (hasDerivAt_thetaCuspLikelihoodCoordinate t).continuousAt
  have hevent : {x : ℝ | 0 < thetaCuspLikelihoodCoordinate x} ∈ nhds t :=
    hcoord.eventually (Ioi_mem_nhds hB)
  have h7 : ContDiffAt ℝ 0 thetaCuspLikelihoodSourceLogPartitionJetSeven t := by
    rw [contDiffAt_zero]
    refine ⟨{x : ℝ | 0 < thetaCuspLikelihoodCoordinate x}, hevent, ?_⟩
    intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSeven_of_coordinate_pos
      hx).continuousAt.continuousWithinAt
  have h6 : ContDiffAt ℝ 1 thetaCuspLikelihoodSourceLogPartitionJetSix t := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt_masterSeam
    · filter_upwards [hevent] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSix_of_coordinate_pos hx
    · exact h7
  have h5 : ContDiffAt ℝ 2 thetaCuspLikelihoodSourceLogPartitionJetFive t := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt_masterSeam
    · filter_upwards [hevent] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive hx
    · exact h6
  have h4 : ContDiffAt ℝ 3 thetaCuspLikelihoodSourceLogPartitionJetFour t := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt_masterSeam
    · filter_upwards [hevent] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hx
    · exact h5
  have h3 : ContDiffAt ℝ 4 thetaCuspLikelihoodSourceLogPartitionJetThree t := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt_masterSeam
    · filter_upwards [hevent] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hx
    · exact h4
  have h2 : ContDiffAt ℝ 5 thetaCuspLikelihoodSourceLogPartitionJetTwo t := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt_masterSeam
    · filter_upwards [hevent] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hx
    · exact h3
  exact ⟨h2.of_le (by norm_num), h3⟩

/-- Strict-cooling defect introduced by replacing the literal third likelihood jet by six
curvature units. -/
def thetaCuspCenterFifthRootVelocityCoolingDefect (t : ℝ) : ℝ :=
  HTGeometry.c5VelocityCoolingDefectExpression
    thetaCuspC5MasterSeamRadius
    thetaCuspLikelihoodSourceLogPartitionJetTwo
    thetaCuspLikelihoodSourceLogPartitionJetThree t

/-- Smooth seam proxy equal to the master-reserved core on the positive physical ray. -/
def thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy (t : ℝ) : ℝ :=
  thetaCuspCenterFifthRootVelocityLiteralActionCore t +
    thetaCuspCenterFifthRootVelocityCoolingDefect t

theorem thetaCuspCenterFifthRootVelocityLiteralActionCore_eq_actionCore
    (t : ℝ) :
    thetaCuspCenterFifthRootVelocityLiteralActionCore t =
      thetaCuspReflectedActionFifthRootVelocityCore
        (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) t
        (thetaCuspReflectedLogJetOne 0 t)
        (thetaCuspReflectedLogJetTwo 0 t)
        (thetaCuspReflectedLogJetThree 0 t) := by
  unfold thetaCuspCenterFifthRootVelocityLiteralActionCore
    HTGeometry.c5VelocityFirstAtomCurvatureExpression
    thetaCuspC5MasterSeamRadius
    thetaCuspReflectedActionFifthRootVelocityCore
  rfl

/-- Exact positive-ray extension identity for the master-reserved core. -/
theorem thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_eq_masterReservedCore
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy t =
      thetaCuspCenterFifthRootVelocityMasterReservedCore t := by
  rw [show thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy t =
      thetaCuspCenterFifthRootVelocityLiteralActionCore t +
        10 * (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) * t ^ (2 : ℕ) *
          (thetaCuspLikelihoodSourceLogPartitionJetThree t +
            6 * thetaCuspLikelihoodSourceLogPartitionJetTwo t) by
    unfold thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
      thetaCuspCenterFifthRootVelocityCoolingDefect
      HTGeometry.c5VelocityCoolingDefectExpression
      thetaCuspC5MasterSeamRadius
    rfl]
  rw [thetaCuspCenterFifthRootVelocityLiteralActionCore_eq_actionCore,
    thetaCuspReflectedActionFifthRootVelocityCore_zero_eq_lowerJet_sub_thirdLikelihood ht]
  unfold thetaCuspCenterFifthRootVelocityMasterReservedCore
  ring

private theorem contDiffAt_four_thetaCuspCenterFifthRootVelocityCoolingDefect
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ 4 thetaCuspCenterFifthRootVelocityCoolingDefect t := by
  rcases thetaCuspLikelihoodHighJets_contDiffAt_four ht with ⟨hg2, hg3⟩
  have hr := (contDiffAt_top_thetaCuspC5MasterSeamRadius t).of_le
    (by exact WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))
  unfold thetaCuspCenterFifthRootVelocityCoolingDefect
    HTGeometry.c5VelocityCoolingDefectExpression
  fun_prop

theorem thetaCuspCenterFifthRootVelocityCoolingDefect_seamJetClassification :
    let k := thetaCuspReflectedLogJetTwo 0 0
    let G₂ := thetaCuspLikelihoodSourceLogPartitionJetTwo 0
    let G₃ := thetaCuspLikelihoodSourceLogPartitionJetThree 0
    (∀ j < 4,
      iteratedDeriv j thetaCuspCenterFifthRootVelocityCoolingDefect 0 = 0) ∧
      iteratedDeriv 4 thetaCuspCenterFifthRootVelocityCoolingDefect 0 =
        120 * k * (G₃ + 6 * G₂) := by
  dsimp only
  rcases thetaCuspC5MasterSeamRadius_jets with ⟨hr0, hr1, hr2⟩
  rcases thetaCuspLikelihoodHighJets_contDiffAt_four (show 0 ≤ (0 : ℝ) by norm_num) with
    ⟨hg2, hg3⟩
  have hr := (contDiffAt_top_thetaCuspC5MasterSeamRadius 0).of_le
    (by exact WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))
  have h := HTGeometry.c5VelocityCoolingDefectExpression_seamJetClassification
    thetaCuspC5MasterSeamRadius
    thetaCuspLikelihoodSourceLogPartitionJetTwo
    thetaCuspLikelihoodSourceLogPartitionJetThree
    hr hg2 hg3
    (thetaCuspReflectedLogJetTwo 0 0)
    (thetaCuspLikelihoodSourceLogPartitionJetTwo 0)
    (thetaCuspLikelihoodSourceLogPartitionJetThree 0)
    hr0 hr1 hr2 rfl rfl
  change (∀ j < 4,
      iteratedDeriv j thetaCuspCenterFifthRootVelocityCoolingDefect 0 = 0) ∧
    iteratedDeriv 4 thetaCuspCenterFifthRootVelocityCoolingDefect 0 =
      120 * thetaCuspReflectedLogJetTwo 0 0 *
        (thetaCuspLikelihoodSourceLogPartitionJetThree 0 +
          6 * thetaCuspLikelihoodSourceLogPartitionJetTwo 0) at h
  exact h

theorem thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_seamJetClassification :
    let k := thetaCuspReflectedLogJetTwo 0 0
    let G₂ := thetaCuspLikelihoodSourceLogPartitionJetTwo 0
    let G₃ := thetaCuspLikelihoodSourceLogPartitionJetThree 0
    (∀ j < 4,
      iteratedDeriv j thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy 0 = 0) ∧
      iteratedDeriv 4 thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy 0 =
        120 * k * (G₃ + 6 * G₂) := by
  dsimp only
  have hlit := thetaCuspCenterFifthRootVelocityLiteralActionCore_seamJetClassification
  have hdef := thetaCuspCenterFifthRootVelocityCoolingDefect_seamJetClassification
  have hlit4 : ContDiffAt ℝ 4 thetaCuspCenterFifthRootVelocityLiteralActionCore 0 :=
    (contDiffAt_top_thetaCuspCenterFifthRootVelocityLiteralActionCore 0).of_le
      (by exact WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))
  have hdef4 := contDiffAt_four_thetaCuspCenterFifthRootVelocityCoolingDefect
    (show 0 ≤ (0 : ℝ) by norm_num)
  have hadd (j : ℕ) (hj : j ≤ 4) :
      iteratedDeriv j thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy 0 =
        iteratedDeriv j thetaCuspCenterFifthRootVelocityLiteralActionCore 0 +
          iteratedDeriv j thetaCuspCenterFifthRootVelocityCoolingDefect 0 := by
    unfold thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
    exact iteratedDeriv_add
      (hlit4.of_le (by exact_mod_cast hj))
      (hdef4.of_le (by exact_mod_cast hj))
  constructor
  · intro j hj
    rw [hadd j (by omega), hlit j (by omega), hdef.1 j hj]
    ring
  · rw [hadd 4 (by norm_num), hlit 4 (by norm_num), hdef.2]
    ring

theorem iteratedDeriv_four_thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_neg :
    iteratedDeriv 4 thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy 0 < 0 := by
  rw [thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_seamJetClassification.2]
  have hk : 0 < thetaCuspReflectedLogJetTwo 0 0 := by
    rw [thetaCuspReflectedLogJetTwo_zero]
    exact mul_pos (by norm_num) (thetaCuspLogCurvature_pos 0)
  have hcool := six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
    (show 0 ≤ (0 : ℝ) by norm_num)
  have hsum : thetaCuspLikelihoodSourceLogPartitionJetThree 0 +
      6 * thetaCuspLikelihoodSourceLogPartitionJetTwo 0 < 0 := by
    linarith
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hk) hsum

private theorem contDiffAt_four_thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ 4 thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy t := by
  have hlit :=
    (contDiffAt_top_thetaCuspCenterFifthRootVelocityLiteralActionCore t).of_le
      (by exact WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))
  have hdef :=
    contDiffAt_four_thetaCuspCenterFifthRootVelocityCoolingDefect ht
  unfold thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
  exact hlit.add hdef

private theorem continuousAt_iteratedDeriv_four_of_contDiffAt_four
    {f : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ 4 f x) :
    ContinuousAt (iteratedDeriv 4 f) x := by
  have hF : ContinuousAt (iteratedFDeriv ℝ 4 f) x :=
    h.continuousAt_iteratedFDeriv le_rfl
  have happ : Continuous
      (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => ℝ) ℝ =>
        T (fun _ => 1)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => ℝ) ℝ
      (fun _ => 1)).continuous
  have hc : ContinuousAt
      (fun y => (iteratedFDeriv ℝ 4 f y) (fun _ => 1)) x :=
    happ.continuousAt.comp hF
  have hfun : iteratedDeriv 4 f =
      fun y => (iteratedFDeriv ℝ 4 f y) (fun _ => 1) := by
    funext y
    rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hfun]
  exact hc

private def c5MasterReservedIteratedTaylorShift
    (f : ℝ → ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    iteratedDeriv k f x * r ^ k / (k.factorial : ℝ)

private theorem taylorWithinEval_add_eq_c5MasterReservedIteratedTaylorShift
    {f : ℝ → ℝ} {x r : ℝ}
    (hf : ContDiffAt ℝ 4 f x) (hr : 0 < r) (j : ℕ) (hj : j ≤ 3) :
    taylorWithinEval f j (uIcc x (x + r)) x (x + r) =
      c5MasterReservedIteratedTaylorShift f j r x := by
  have hle : x ≤ x + r := by linarith
  rw [uIcc_of_le hle]
  induction j with
  | zero =>
      simp [c5MasterReservedIteratedTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih (by omega)]
      simp only [c5MasterReservedIteratedTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) f (Icc x (x + r)) x =
          iteratedDeriv (j + 1) f x := by
        have hj4 : ((j + 1 : ℕ) : WithTop ℕ∞) ≤ (4 : WithTop ℕ∞) := by
          exact_mod_cast (show j + 1 ≤ 4 by omega)
        have hf' : ContDiffAt ℝ (j + 1) f x := hf.of_le hj4
        exact iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by linarith)) hf' (left_mem_Icc.mpr hle)
      rw [hderiv, Nat.factorial_succ]
      push_cast
      ring

private theorem thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_taylor_three_zero
    {t : ℝ} (ht : 0 < t) :
    taylorWithinEval thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy 3
      (uIcc 0 t) 0 t = 0 := by
  have hTaylor :=
    taylorWithinEval_add_eq_c5MasterReservedIteratedTaylorShift
      (f := thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy)
      (x := 0) (r := t)
      (contDiffAt_four_thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
        (show 0 ≤ (0 : ℝ) by norm_num)) ht 3 (by norm_num)
  simpa only [zero_add] using hTaylor.trans (by
    unfold c5MasterReservedIteratedTaylorShift
    apply Finset.sum_eq_zero
    intro k hk
    rw [thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_seamJetClassification.1
      k (Finset.mem_range.mp hk)]
    simp)

/-- The full master-reserved sufficient core is negative immediately right of the seam. -/
theorem eventually_thetaCuspCenterFifthRootVelocityMasterReservedCore_neg :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      thetaCuspCenterFifthRootVelocityMasterReservedCore t < 0 := by
  let f := thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
  have hf0 : ContDiffAt ℝ 4 f 0 := by
    simpa only [f] using
      contDiffAt_four_thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
        (show 0 ≤ (0 : ℝ) by norm_num)
  have hf4 : ContinuousAt (iteratedDeriv 4 f) 0 :=
    continuousAt_iteratedDeriv_four_of_contDiffAt_four hf0
  have hneg0 : iteratedDeriv 4 f 0 < 0 := by
    simpa only [f] using
      iteratedDeriv_four_thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_neg
  have hevent : {x : ℝ | iteratedDeriv 4 f x < 0} ∈ nhds 0 :=
    hf4.eventually (Iio_mem_nhds hneg0)
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro t ht htε
  have hfOn : ContDiffOn ℝ 4 f (uIcc 0 t) := by
    rw [uIcc_of_le ht.le]
    intro x hx
    exact (contDiffAt_four_thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy
      hx.1).contDiffWithinAt
  have hTaylor : taylorWithinEval f 3 (uIcc 0 t) 0 t = 0 := by
    simpa only [f] using
      thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_taylor_three_zero ht
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x := t) (x₀ := 0) (n := 3) (ne_of_lt ht) hfOn
  rw [uIoo_of_le ht.le] at hx
  have hxball : x ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact hx.2.trans htε
  have hxneg : iteratedDeriv 4 f x < 0 := hball hxball
  rw [hTaylor, sub_zero, sub_zero] at hrem
  rw [← thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_eq_masterReservedCore ht]
  change f t < 0
  rw [hrem]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hxneg (pow_pos ht 4))
    (by positivity)

/-- The master-reserved global-nonnegativity route to strict center C5 velocity is impossible. -/
theorem not_forall_thetaCuspCenterFifthRootVelocityMasterReservedCore_nonneg :
    ¬ ∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspCenterFifthRootVelocityMasterReservedCore t := by
  rcases eventually_thetaCuspCenterFifthRootVelocityMasterReservedCore_neg with
    ⟨δ, hδ, hlocal⟩
  intro hnonneg
  let t := δ / 2
  have ht : 0 < t := by dsimp only [t]; linarith
  have htδ : t < δ := by dsimp only [t]; linarith
  exact (not_lt_of_ge (hnonneg t ht)) (hlocal t ht htδ)

end

end RHTower
