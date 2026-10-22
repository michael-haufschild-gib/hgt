import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthPureNextSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthCenterSourceTransfer
/-! The complete pair-relative source sign propagates the center transfer sign
to every nonnegative coordinate. The normalized source growth then increases
strictly from zero, proving the actual seventh-order growth sign globally. -/

namespace RHTower.ThetaCuspDefect
open Filter Set Topology
noncomputable section

def sourceTransferCoordinateRatio (x : ℝ) : ℝ :=
  growthTransferFunctional (thetaCuspLikelihoodCoordinate x)
    (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate x))/
      dominantPairTransfer (thetaCuspLikelihoodCoordinate x)

private theorem hasDerivAt_sourceTransferCoordinateRatio {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt sourceTransferCoordinateRatio
      ((-pairRelativeSourceTransfer (thetaCuspLikelihoodCoordinate x)/
        (thetaCuspLikelihoodCoordinate x*dominantPairPolynomial (thetaCuspLikelihoodCoordinate x)*
          dominantPairTransfer (thetaCuspLikelihoodCoordinate x)))*
            (2*thetaCuspSingleAtomReflectionScale 1 x)) x := by
  have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate x := by
    linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  exact (hasDerivAt_sourceTransfer_relative hq).comp x (hasDerivAt_thetaCuspLikelihoodCoordinate x)

theorem sourceTransferCoordinateRatio_strictAntiOn :
    StrictAntiOn sourceTransferCoordinateRatio (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_sourceTransferCoordinateRatio hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate x := by
      linarith [sourceCoordinate_actual_lower hx0.le,Real.pi_gt_three]
    have hq0 := thetaCuspLikelihoodCoordinate_pos hx0.le
    have hP := dominantPairPolynomial_pos hq
    have hJ := growthTransferFunctional_dominant_pair_pos hq
    have hE := pairRelativeSourceTransfer_coordinate_pos hx0.le
    have hscale : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    rw [(hasDerivAt_sourceTransferCoordinateRatio hx0.le).deriv]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos hE) (by positivity)) hscale

theorem sourceTransfer_coordinate_neg {x : ℝ} (hx : 0 ≤ x) :
    growthTransferFunctional (thetaCuspLikelihoodCoordinate x)
      (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate x)) < 0 := by
  rcases eq_or_lt_of_le hx with he | hx0
  · subst x
    exact sourceCenter_growthTransfer_neg
  · have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate x := by
      linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
    have hqcenter : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate 0 := by
      linarith [sourceCoordinate_actual_lower (show (0:ℝ) ≤ 0 from le_rfl),Real.pi_gt_three]
    have h0 : sourceTransferCoordinateRatio 0 < 0 :=
      div_neg_of_neg_of_pos sourceCenter_growthTransfer_neg (growthTransferFunctional_dominant_pair_pos hqcenter)
    have hlt := sourceTransferCoordinateRatio_strictAntiOn (show (0:ℝ) ∈ Ici 0 from by change (0:ℝ) ≤ 0; exact le_rfl) hx hx0
    have hneg := hlt.trans h0
    unfold sourceTransferCoordinateRatio at hneg
    simpa using (div_lt_iff₀ (growthTransferFunctional_dominant_pair_pos hq)).mp hneg

private theorem hasDerivAt_sourceRelativeGrowthCoordinate {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => sourceRelativeGrowth (thetaCuspLikelihoodCoordinate t))
      ((-(dominantAtomScale (thetaCuspLikelihoodCoordinate x)/(thetaCuspLikelihoodCoordinate x)^9)*
        growthTransferFunctional (thetaCuspLikelihoodCoordinate x)
          (likelihoodCumulantEight (thetaCuspLikelihoodCoordinate x))/
        (growthFunctional (thetaCuspLikelihoodCoordinate x) (atomMoment 2 (thetaCuspLikelihoodCoordinate x)))^2)*
          (2*thetaCuspSingleAtomReflectionScale 1 x)) x := by
  have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate x := by
    linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  exact (hasDerivAt_sourceRelativeGrowth hq).comp x (hasDerivAt_thetaCuspLikelihoodCoordinate x)

theorem sourceRelativeGrowthCoordinate_strictMonoOn :
    StrictMonoOn (fun x => sourceRelativeGrowth (thetaCuspLikelihoodCoordinate x)) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_sourceRelativeGrowthCoordinate hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate x := by
      linarith [sourceCoordinate_actual_lower hx0.le,Real.pi_gt_three]
    have hq0 := thetaCuspLikelihoodCoordinate_pos hx0.le
    have hA := atom_growthFunctional_pos (by omega : 2 ≤ (2:ℕ)) hq
    have hscale : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    have hfactor : 0 < dominantAtomScale (thetaCuspLikelihoodCoordinate x)/(thetaCuspLikelihoodCoordinate x)^9 :=
      div_pos (dominantAtomScale_pos _) (pow_pos hq0 9)
    have hprod := mul_pos_of_neg_of_neg (neg_neg_of_pos hfactor) (sourceTransfer_coordinate_neg hx0.le)
    rw [(hasDerivAt_sourceRelativeGrowthCoordinate hx0.le).deriv]
    exact mul_pos (div_pos hprod (pow_pos hA 2)) hscale

theorem sourceGrowth_coordinate_pos {x : ℝ} (hx : 0 < x) :
    0 < sourceGrowth (thetaCuspLikelihoodCoordinate x) := by
  have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate x := by
    linarith [sourceCoordinate_actual_lower hx.le,Real.pi_gt_three]
  have h := sourceRelativeGrowthCoordinate_strictMonoOn (show (0:ℝ) ∈ Ici 0 from by change (0:ℝ) ≤ 0; exact le_rfl) hx.le hx
  dsimp only at h
  rw [sourceRelativeGrowth_coordinate_zero] at h
  unfold sourceRelativeGrowth at h
  simpa using (lt_div_iff₀ (atom_growthFunctional_pos (by omega : 2 ≤ (2:ℕ)) hq)).mp h

end
end RHTower.ThetaCuspDefect
