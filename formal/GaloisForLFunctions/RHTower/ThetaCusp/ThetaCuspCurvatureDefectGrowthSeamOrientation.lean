import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthGlobalPropagation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureLogConvex
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspExactCompletedC5SeamOrientation
/-! Global source growth supplies the seventh-order defect comparison.
Together with the literal defect slope and curvature velocity gap, it gives
a positive-remainder decomposition of the exact completed C5 seam orientation
at every positive center. Finite-displacement compensation remains separate. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section

theorem centerCurvature_gt_eighteen : 18 < thetaCuspLogCurvature 0 := by
  have hX := thetaCuspSelfDualModularScale_sq_lt_twenty
  have hp : centerRawJet (thetaCuspSelfDualModularScale^2) 2+
      18*centerRawJet (thetaCuspSelfDualModularScale^2) 0 < 0 := by
    unfold centerRawJet
    simp only [centerMassJet,Nat.reduceAdd]
    nlinarith [sq_nonneg (thetaCuspSelfDualModularScale^2-20)]
  have hH := thetaCuspModularODEState_H_re_pos 0
  have hmul := mul_neg_of_pos_of_neg hH hp
  have h0 := thetaSource_centerRawJet 0 (by omega)
  have h2 := thetaSource_centerRawJet 1 (by omega)
  norm_num only [Nat.reduceMul,iteratedDeriv_zero] at h0 h2
  have hf : iteratedDeriv 2 thetaCuspFullSource 0+18*thetaCuspFullSource 0 < 0 := by
    rw [h0,h2]
    nlinarith only [hmul]
  have h1 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 1 by norm_num)
  rw [iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet] at hf
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetZero at hf
  rw [h1,thetaCuspLogSource,Real.exp_log (thetaCuspFullSource_pos_all 0)] at hf
  have hpos := thetaCuspFullSource_pos_all 0
  unfold thetaCuspLogCurvature
  nlinarith only [hf,hpos]

theorem sourceCurvature_strictMonoOn : StrictMonoOn thetaCuspLogCurvature (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x _
    exact (hasDerivAt_thetaCuspLogCurvature x).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(hasDerivAt_thetaCuspLogCurvature x).deriv]
    exact thetaCuspLogCurvatureJet_pos_of_pos hx0

theorem sourceCurvature_gt_eighteen {x : ℝ} (hx : 0 ≤ x) :
    18 < thetaCuspLogCurvature x := by
  exact centerCurvature_gt_eighteen.trans_le
    (sourceCurvature_strictMonoOn.monotoneOn
      (show (0:ℝ) ∈ Ici 0 by change (0:ℝ) ≤ 0; exact le_rfl) hx hx)

theorem factorLogSlope_neg {q : ℝ} (hq : 0 < q) : factorLogSlope q < 0 := by
  have he : factorLogSlope q=-(4*q^2+30*q+45)/(q*(q+3)) := by
    unfold factorLogSlope
    field_simp
    ring
  rw [he]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) (by positivity)

theorem factorSeamReserve_pos {q : ℝ} (hq : (8/5:ℝ) ≤ q) :
    0 < 328+6*factorLogSlope q-factorCurvature q := by
  have hq0 : 0 < q := by linarith
  have hq3 : 0 < q+3 := by linarith
  have hy : 0 ≤ q-8/5 := by linarith
  have he : (328+6*factorLogSlope q-factorCurvature q)*(q^2*(q+3)^2)=
      (328+6*factorLogSlope (8/5+(q-8/5))-factorCurvature (8/5+(q-8/5)))*
        ((8/5+(q-8/5))^2*(8/5+(q-8/5)+3)^2) := by
    rw [show (8/5:ℝ)+(q-8/5)=q by ring]
  have hnum : 0 < (328+6*factorLogSlope q-factorCurvature q)*(q^2*(q+3)^2) := by
    rw [he]
    generalize q-8/5=y at *
    unfold factorCurvature factorLogSlope
    field_simp
    ring_nf
    positivity
  exact (mul_pos_iff_of_pos_right (by positivity : 0 < q^2*(q+3)^2)).mp hnum

theorem hasDerivAt_sourceDefectFactor_coordinate {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => sourceDefectFactor (thetaCuspLikelihoodCoordinate t))
      (sourceDefectFactor (thetaCuspLikelihoodCoordinate x)*
        factorLogSlope (thetaCuspLikelihoodCoordinate x)) x := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  have hd := (((((hasDerivAt_id q).add_const (3/2:ℝ)).pow 2).const_mul 864).mul
    ((hasDerivAt_id q).add_const 3)).div ((hasDerivAt_id q).pow 5) (pow_ne_zero _ hq.ne')
  convert! hd.comp x (hasDerivAt_thetaCuspLikelihoodCoordinate x) using 1
  dsimp only [q,Pi.pow_apply,Pi.mul_apply,id_eq]
  rw [thetaCuspC5FarTail_scale_eq_coordinate_add]
  unfold sourceDefectFactor factorLogSlope
  have hq3 : thetaCuspLikelihoodCoordinate x+3 ≠ 0 := by positivity
  field_simp [hq.ne',hq3]
  ring

theorem sourceDefect_slope_lower {x : ℝ} (hx : 0 < x) :
    factorLogSlope (thetaCuspLikelihoodCoordinate x)*
      (iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x) <
        iteratedDeriv 6 thetaCuspLogSource x-4*iteratedDeriv 4 thetaCuspLogSource x := by
  have hH := (hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).sub
    ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x).const_mul 4)
  have hR := (hasDerivAt_sourceDefectRatio hx.le).differentiableAt.hasDerivAt
  have hF := hasDerivAt_sourceDefectFactor_coordinate hx.le
  have he : (fun t => iteratedDeriv 5 thetaCuspLogSource t-4*iteratedDeriv 3 thetaCuspLogSource t)
      =ᶠ[nhds x] (fun t => sourceDefectFactor (thetaCuspLikelihoodCoordinate t)*(1-sourceDefectRatio t)) := by
    filter_upwards [eventually_gt_nhds hx] with t ht
    exact source_defect_eq ht
  have hid := hH.unique ((hF.mul ((hasDerivAt_const x (1:ℝ)).sub hR)).congr_of_eventuallyEq he)
  norm_num only [Nat.reduceAdd,zero_sub,Pi.sub_apply] at hid
  have hneg := mul_neg_of_pos_of_neg
    (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx.le)) (sourceDefectRatio_deriv_neg hx.le)
  rw [source_defect_eq hx]
  nlinarith only [hid,hneg]

theorem sourceDefect_curvature_upper {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x <
      factorCurvature (thetaCuspLikelihoodCoordinate x)*
        (iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x) := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx.le
  have hneg : -128*(thetaCuspLikelihoodCoordinate x+3/2)^3/
      ((thetaCuspLikelihoodCoordinate x)^2*(thetaCuspLikelihoodCoordinate x+3))*
        sourceGrowth (thetaCuspLikelihoodCoordinate x) < 0 := by
    have hf : 0 < 128*(thetaCuspLikelihoodCoordinate x+3/2)^3/
        ((thetaCuspLikelihoodCoordinate x)^2*(thetaCuspLikelihoodCoordinate x+3)) := by positivity
    have hm := mul_pos hf (sourceGrowth_coordinate_pos hx)
    simpa only [neg_mul,neg_div] using (neg_neg_of_pos hm)
  linarith only [source_growth_eq hx,hneg]

theorem sourceSeamReserve_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < 18*thetaCuspLogCurvature x+4+6*factorLogSlope (thetaCuspLikelihoodCoordinate x)-
      factorCurvature (thetaCuspLikelihoodCoordinate x) := by
  have hq := sourceCoordinate_actual_lower hx
  have hpi := Real.pi_gt_d2
  have hr := factorSeamReserve_pos (q := thetaCuspLikelihoodCoordinate x) (by linarith)
  linarith only [hr,sourceCurvature_gt_eighteen hx]

theorem exactCompletedSeamOrientation_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspC5ExactCompletedSeamOrientation x := by
  let c := thetaCuspLogCurvature x
  let v := thetaCuspLogCurvatureJet x
  let b := curvatureDefect x
  let H := iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x
  let Hp := iteratedDeriv 6 thetaCuspLogSource x-4*iteratedDeriv 4 thetaCuspLogSource x
  let Hpp := iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x
  let f := factorLogSlope (thetaCuspLikelihoodCoordinate x)
  let β := factorCurvature (thetaCuspLikelihoodCoordinate x)
  have hc : 0 < c := thetaCuspLogCurvature_pos x
  have hv : 0 < v := thetaCuspLogCurvatureJet_pos_of_pos hx
  have hb : 0 < b := curvatureDefect_pos hx.le
  have hH : 0 < H := source_defect_pos hx
  have hHp : 0 < Hp-f*H := sub_pos.mpr (sourceDefect_slope_lower hx)
  have hHpp : 0 < β*H-Hpp := sub_pos.mpr (sourceDefect_curvature_upper hx)
  have hf : f < 0 := factorLogSlope_neg (thetaCuspLikelihoodCoordinate_pos hx.le)
  have hv2 : v-2*c < 0 := by
    have h := ThetaCurvature.velocityGap_pos hx.le
    dsimp only [v,c]
    linarith only [h]
  have hr : 0 < 18*c+4+6*f-β := sourceSeamReserve_pos hx.le
  have hcross : 0 < 3*c*f*H*(v-2*c) := mul_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hf) hH) hv2
  have he : thetaCuspC5ExactCompletedSeamOrientation x =
      v*(72*c^3+36*c^2*b+12*c*b+4*b^2)+H*(2*c*b)+
        3*c*v*(Hp-f*H)+c^2*(β*H-Hpp)+3*c*f*H*(v-2*c)+
          c^2*H*(18*c+4+6*f-β) := by
    dsimp only [c,v,b,H,Hp,Hpp,f,β,thetaCuspC5ExactCompletedSeamOrientation,
      curvatureDefect,thetaCuspLogCurvature,thetaCuspLogCurvatureJet,thetaCuspLogCurvatureJetTwo]
    ring
  rw [he]
  positivity

theorem exactSeamNormalizedSixthInvariant_strictMonoOn :
    StrictMonoOn thetaCuspC5ExactSeamNormalizedSixthInvariant (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x _
    exact (hasDerivAt_thetaCuspC5ExactSeamNormalizedSixthInvariant x).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact (thetaCuspC5ExactCompletedSeamOrientation_pos_iff_normalizedSixth_deriv_pos x).mp
      (exactCompletedSeamOrientation_pos hx0)

theorem exists_local_completedCompensation_pos {u : ℝ} (hu : 0 < u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < c5CompletedCompensationMargin u t :=
  eventually_c5CompletedCompensationMargin_pos_of_exactSeamOrientation hu
    (exactCompletedSeamOrientation_pos hu)

theorem exists_local_fixedActionC5Jacobian_pos {u : ℝ} (hu : 0 < u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < thetaCuspReflectedActionC5FixedActionJacobian u t :=
  eventually_thetaCuspReflectedActionC5FixedActionJacobian_pos_of_exactSeamOrientation hu
    (exactCompletedSeamOrientation_pos hu)

end
end RHTower.ThetaCuspDefect
