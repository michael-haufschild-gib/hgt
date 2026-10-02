import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectFiniteLogConvolution
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectBinaryGrowthFlow

/-!
# Exact complete-source growth ratio derivative

The source cumulant chain and literal dominant-atom moment chain identify
sourceRelativeGrowth' with minus a positive factor times the complete
finite growth-transfer functional. The ratio vanishes at the modular
center. Its positive-half-line sign still requires the signed-sector
comparison; no positivity premise is introduced here.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section

theorem growthFunctional_likelihoodCumulantEight (q : ℝ) :
    growthFunctional q (likelihoodCumulantEight q)=sourceGrowth q := by
  unfold sourceGrowth growthFunctional
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant]

theorem hasDerivAt_sourceGrowth {q : ℝ} (hq : 0 < q) :
    HasDerivAt sourceGrowth (growthSlope q (likelihoodCumulantEight q)) q := by
  unfold sourceGrowth growthFunctional growthSlope
  apply HasDerivAt.fun_sum
  intro j hj
  have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
  interval_cases j <;> norm_num [Nat.reduceAdd,likelihoodCumulantEight,
    likelihoodCumulantSeven,likelihoodCumulant,ite_true,ite_false]
  · exact ((hasDerivAt_growthCoefficient q 2 (by omega)).mul
      (hasDerivAt_thetaCuspLikelihoodVariance hq)).congr_deriv (by ring)
  · exact ((hasDerivAt_growthCoefficient q 3 (by omega)).mul
      (hasDerivAt_thetaCuspLikelihoodThirdCumulant hq)).congr_deriv (by ring)
  · exact ((hasDerivAt_growthCoefficient q 4 (by omega)).mul
      (hasDerivAt_thetaCuspLikelihoodFourthCumulant hq)).congr_deriv (by ring)
  · exact ((hasDerivAt_growthCoefficient q 5 (by omega)).mul
      (hasDerivAt_thetaCuspLikelihoodFifthCumulant hq)).congr_deriv (by ring)
  · exact ((hasDerivAt_growthCoefficient q 6 (by omega)).mul
      (hasDerivAt_thetaCuspLikelihoodSixthCumulant hq)).congr_deriv (by ring)
  · exact ((hasDerivAt_growthCoefficient q 7 (by omega)).mul
      (hasDerivAt_thetaCuspLikelihoodSeventhCumulant hq)).congr_deriv (by ring)

theorem growthTransferFunctional_eq (q : ℝ) (m : ℕ → ℝ) :
    growthTransferFunctional q m =
      slopeNumerator q 3*growthFunctional q m-
      q*growthNumerator q 3*growthSlope q m := by
  unfold growthTransferFunctional growthFunctional growthSlope
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def dominantAtomScale (q : ℝ) : ℝ := 4*Real.exp (-(9/2))*Real.exp (-3*q)

theorem dominantAtomScale_pos (q : ℝ) : 0 < dominantAtomScale q := by
  unfold dominantAtomScale
  positivity

theorem growthTransferFunctional_anchor {q : ℝ} (hq : 0 < q) (m : ℕ → ℝ) :
    growthSlope q (atomMoment 2 q)*growthFunctional q m-
      growthFunctional q (atomMoment 2 q)*growthSlope q m =
      dominantAtomScale q/q^9*growthTransferFunctional q m := by
  have ham : atomMoment 2 q=(fun j => dominantAtomScale q*bareMoment q 3 j) := by
    funext j
    have hg : thetaCuspLikelihoodGap 2=(3:ℝ) := by norm_num [thetaCuspLikelihoodGap]
    rw [atomMoment_eq_bare (by omega : 2 ≤ (2:ℕ)) hq,hg]
    unfold dominantAtomScale
    rw [show -(3/2)*(3:ℝ)=-(9/2) by ring,show -q*(3:ℝ)=-3*q by ring]
    ring
  rw [ham,growthSlope_smul,growthFunctional_smul,growthSlope_bare_polynomial hq.ne',
    growthFunctional_bare_polynomial hq.ne',growthTransferFunctional_eq]
  field_simp [hq.ne']

def sourceRelativeGrowth (q : ℝ) : ℝ := sourceGrowth q/growthFunctional q (atomMoment 2 q)

theorem hasDerivAt_sourceRelativeGrowth {q : ℝ} (hq : 3/2 ≤ q) :
    HasDerivAt sourceRelativeGrowth
      (-(dominantAtomScale q/q^9)*growthTransferFunctional q (likelihoodCumulantEight q)/
        (growthFunctional q (atomMoment 2 q))^2) q := by
  have hq0 : 0 < q := by linarith
  have ha := hasDerivAt_atomGrowth (by omega : 2 ≤ (2:ℕ)) hq0
  have hb := hasDerivAt_sourceGrowth hq0
  have hpos := atom_growthFunctional_pos (by omega : 2 ≤ (2:ℕ)) hq
  have hw := growthTransferFunctional_anchor hq0 (likelihoodCumulantEight q)
  rw [growthFunctional_likelihoodCumulantEight] at hw
  unfold sourceRelativeGrowth
  apply (hb.div ha hpos.ne').congr_deriv
  calc
    (growthSlope q (likelihoodCumulantEight q)*growthFunctional q (atomMoment 2 q)-
      sourceGrowth q*growthSlope q (atomMoment 2 q))/(growthFunctional q (atomMoment 2 q))^2 =
      -(growthSlope q (atomMoment 2 q)*sourceGrowth q-
        growthFunctional q (atomMoment 2 q)*growthSlope q (likelihoodCumulantEight q))/
        (growthFunctional q (atomMoment 2 q))^2 := by ring
    _ = _ := by rw [hw]; ring

theorem sourceRelativeGrowth_coordinate_zero :
    sourceRelativeGrowth (thetaCuspLikelihoodCoordinate 0)=0 := by
  unfold sourceRelativeGrowth
  rw [sourceGrowth_coordinate_zero,zero_div]

end
end RHTower.ThetaCuspDefect
