import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthCenterModularJets
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthTransferFlow

/-!
# Actual center transfer and local positive source growth

Differentiation on the nonnegative half-line transports the exact modular
log-jet sign to positive growth slope and negative complete transfer at
q(0). The source growth is strictly positive on some right neighborhood
of zero. Global propagation remains a separate open problem.
-/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section

theorem sourceCenter_growthSlope_pos :
    0 < growthSlope (thetaCuspLikelihoodCoordinate 0)
      (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate 0)) := by
  let β : ℝ → ℝ := fun x => factorCurvature (thetaCuspLikelihoodCoordinate x)
  let F : ℝ → ℝ := fun x => -128*(thetaCuspLikelihoodCoordinate x+3/2)^3/
    ((thetaCuspLikelihoodCoordinate x)^2*(thetaCuspLikelihoodCoordinate x+3))
  let L : ℝ → ℝ := fun x => (iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x)-
    β x*(iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x)
  let R : ℝ → ℝ := fun x => F x*sourceGrowth (thetaCuspLikelihoodCoordinate x)
  have hq0 := thetaCuspLikelihoodCoordinate_pos (show (0:ℝ) ≤ 0 from le_rfl)
  have hq := hasDerivAt_thetaCuspLikelihoodCoordinate 0
  have hqd := hq.differentiableAt
  have hq3 : thetaCuspLikelihoodCoordinate 0+3 ≠ 0 := by positivity
  have hβ : DifferentiableAt ℝ β 0 := by
    dsimp only [β]
    unfold factorCurvature factorLogSlope
    fun_prop (disch := positivity)
  have hF : DifferentiableAt ℝ F 0 := by
    dsimp only [F]
    fun_prop (disch := positivity)
  have h3zero := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 by norm_num)
  have h5zero := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 by norm_num)
  have h7zero := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 7 by norm_num)
  have hL : HasDerivAt L
      ((iteratedDeriv 8 thetaCuspLogSource 0-4*iteratedDeriv 6 thetaCuspLogSource 0)-
        β 0*(iteratedDeriv 6 thetaCuspLogSource 0-4*iteratedDeriv 4 thetaCuspLogSource 0)) 0 := by
    have h := ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 7 0).sub
      ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 0).const_mul 4)).sub
      (hβ.hasDerivAt.mul ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 0).sub
        ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 0).const_mul 4)))
    exact h.congr_deriv (by simp only [Pi.sub_apply,Nat.reduceAdd,h5zero,h3zero,mul_zero,sub_zero,zero_add])
  have hR : HasDerivAt R
      (F 0*growthSlope (thetaCuspLikelihoodCoordinate 0)
        (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate 0))*
          (2*thetaCuspSingleAtomReflectionScale 1 0)) 0 := by
    have h := hF.hasDerivAt.mul ((hasDerivAt_sourceGrowth hq0).comp 0 hq)
    exact h.congr_deriv (by simp only [Function.comp_apply,sourceGrowth_coordinate_zero,mul_zero,zero_add]; ring)
  have he : ∀ x ∈ Ici (0:ℝ), L x=R x := by
    intro x hx
    change (0:ℝ) ≤ x at hx
    rcases eq_or_lt_of_le hx with hx0|hx0
    · subst x
      dsimp only [L,R]
      rw [h3zero,h5zero,h7zero,sourceGrowth_coordinate_zero]
      ring
    · exact source_growth_eq hx0
  have hR' := hR.hasDerivWithinAt.congr_of_mem he (show (0:ℝ) ∈ Ici 0 by simp only [mem_Ici]; exact le_rfl)
  have heq := (hL.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hR'.derivWithin (uniqueDiffWithinAt_Ici 0))
  have hnegative : F 0*growthSlope (thetaCuspLikelihoodCoordinate 0)
      (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate 0))*
        (2*thetaCuspSingleAtomReflectionScale 1 0)<0 := by
    rw [←heq]
    dsimp only [β]
    linarith [sourceCenter_growthLogValue_pos]
  have hFneg : F 0<0 := by
    dsimp only [F]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (by positivity)) (by positivity)
  have hA : 0 < 2*thetaCuspSingleAtomReflectionScale 1 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  by_contra h
  have hn := le_of_not_gt h
  have hp := mul_nonneg_of_nonpos_of_nonpos hFneg.le hn
  have hp' := mul_nonneg hp hA.le
  exact (not_lt_of_ge hp') hnegative

theorem sourceCenter_growthTransfer_neg :
    growthTransferFunctional (thetaCuspLikelihoodCoordinate 0)
      (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate 0))<0 := by
  have hq0 := thetaCuspLikelihoodCoordinate_pos (show (0:ℝ) ≤ 0 from le_rfl)
  have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate 0 := by
    rw [thetaCuspLikelihoodCoordinate_zero_eq]
    linarith [Real.pi_gt_three]
  have ha := atom_growthFunctional_pos (by omega : 2 ≤ (2:ℕ)) hq
  have hg := sourceCenter_growthSlope_pos
  have h := growthTransferFunctional_anchor hq0 (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate 0))
  rw [growthFunctional_likelihoodCumulantEight,sourceGrowth_coordinate_zero,mul_zero,zero_sub] at h
  have hf : 0 < dominantAtomScale (thetaCuspLikelihoodCoordinate 0)/(thetaCuspLikelihoodCoordinate 0)^9 :=
    div_pos (dominantAtomScale_pos _) (pow_pos hq0 9)
  have hn := neg_neg_of_pos (mul_pos ha hg)
  rw [h] at hn
  by_contra he
  exact (not_lt_of_ge (mul_nonneg hf.le (le_of_not_gt he))) hn


theorem sourceGrowth_coordinate_eventually_pos :
    ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), 0 < sourceGrowth (thetaCuspLikelihoodCoordinate x) := by
  have hq0 := thetaCuspLikelihoodCoordinate_pos (show (0:ℝ) ≤ 0 from le_rfl)
  have h := (hasDerivAt_sourceGrowth hq0).comp 0 (hasDerivAt_thetaCuspLikelihoodCoordinate 0)
  have hA : 0 < 2*thetaCuspSingleAtomReflectionScale 1 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hd := mul_pos sourceCenter_growthSlope_pos hA
  have hs := h.tendsto_slope_zero_right.eventually (eventually_gt_nhds hd)
  filter_upwards [hs,self_mem_nhdsWithin] with x hx hx0
  simp only [zero_add,Function.comp_apply,sourceGrowth_coordinate_zero,sub_zero,smul_eq_mul] at hx
  exact pos_of_mul_pos_right hx (inv_nonneg.mpr (le_of_lt hx0))

end
end RHTower.ThetaCuspDefect
