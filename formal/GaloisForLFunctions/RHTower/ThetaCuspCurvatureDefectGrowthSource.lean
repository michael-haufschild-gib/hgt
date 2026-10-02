import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMoments
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectSource

/-!
# Exact seventh-order source defect growth and modular cancellation

The ordinary growth kernel has positive complete spectral integral.
Its cumulant counterpart is identified exactly with the seventh-versus-fifth
logarithmic source jet, after subtracting the curvature of the first-atom
defect factor. Modular odd-jet vanishing forces this cumulant growth
functional to vanish at the center. Its sign for positive source coordinate
is a remaining mathematical target, not an assumption of this module.
-/

namespace RHTower.ThetaCuspDefect
open Set Filter
noncomputable section

def likelihoodCumulantSeven (q : ℝ) (j : ℕ) : ℝ :=
  if j=7 then thetaCuspLikelihoodSeventhCumulant q else likelihoodCumulant q j

def sourceGrowth (q : ℝ) : ℝ := growthFunctional q (likelihoodCumulantSeven q)

def factorLogSlope (q : ℝ) : ℝ := 4+2*(q+3/2)/(q+3)-10*(q+3/2)/q

def factorCurvature (q : ℝ) : ℝ :=
  factorLogSlope q^2+2*(q+3/2)*(3/(q+3)^2+15/q^2)

theorem source_growth_eq {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x)-
      factorCurvature (thetaCuspLikelihoodCoordinate x)*
        (iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x) =
      -128*(thetaCuspLikelihoodCoordinate x+3/2)^3/
        ((thetaCuspLikelihoodCoordinate x)^2*(thetaCuspLikelihoodCoordinate x+3))*
          sourceGrowth (thetaCuspLikelihoodCoordinate x) := by
  rw [iteratedDeriv_seven_thetaCuspLogSource_eq_full_jets hx,
    iteratedDeriv_five_thetaCuspLogSource_eq_full_jets hx,
    iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx,
    ←thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx]
  unfold thetaCuspFullLogJetSeven thetaCuspFullLogJetFive thetaCuspFirstAtomLogJetThree
    thetaCuspBornWittenLogSeventhDerivative thetaCuspBornWittenLogFifthDerivative
    thetaCuspBornWittenLogThirdDerivative thetaCuspLikelihoodSourceLogPartitionJetSeven
    thetaCuspLikelihoodSourceLogPartitionJetFive thetaCuspLikelihoodSourceLogPartitionJetThree
  simp only [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  unfold sourceGrowth growthFunctional
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,coolingCoefficient,coolingCoefficientJet,
    likelihoodCumulantSeven,likelihoodCumulant]
  unfold factorCurvature factorLogSlope
  have hq := thetaCuspLikelihoodCoordinate_pos hx.le
  have hq3 : thetaCuspLikelihoodCoordinate x+3 ≠ 0 := by positivity
  field_simp [hq.ne',hq3]
  ring
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
open Set Filter
noncomputable section

private theorem continuousAt_sourceGrowth_coordinate_zero :
    ContinuousAt (fun x => sourceGrowth (thetaCuspLikelihoodCoordinate x)) 0 := by
  have hq := hasDerivAt_thetaCuspLikelihoodCoordinate 0
  have hq0 := thetaCuspLikelihoodCoordinate_pos (show (0:ℝ) ≤ 0 from le_rfl)
  have hc := hq.continuousAt
  have h2 := ((hasDerivAt_thetaCuspLikelihoodVariance hq0).comp 0 hq).continuousAt
  have h3 := ((hasDerivAt_thetaCuspLikelihoodThirdCumulant hq0).comp 0 hq).continuousAt
  have h4 := ((hasDerivAt_thetaCuspLikelihoodFourthCumulant hq0).comp 0 hq).continuousAt
  have h5 := ((hasDerivAt_thetaCuspLikelihoodFifthCumulant hq0).comp 0 hq).continuousAt
  have h6 := ((hasDerivAt_thetaCuspLikelihoodSixthCumulant hq0).comp 0 hq).continuousAt
  have h7 := ((hasDerivAt_thetaCuspLikelihoodSeventhCumulant hq0).comp 0 hq).continuousAt
  unfold sourceGrowth growthFunctional
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,coolingCoefficient,coolingCoefficientJet,
    likelihoodCumulantSeven,likelihoodCumulant]
  fun_prop

theorem sourceGrowth_coordinate_zero : sourceGrowth (thetaCuspLikelihoodCoordinate 0)=0 := by
  have hq := (hasDerivAt_thetaCuspLikelihoodCoordinate 0).continuousAt
  have hq0 := thetaCuspLikelihoodCoordinate_pos (show (0:ℝ) ≤ 0 from le_rfl)
  have hqne := hq0.ne'
  have hq3 : thetaCuspLikelihoodCoordinate 0+3 ≠ 0 := by positivity
  have hbeta : ContinuousAt (fun x => factorCurvature (thetaCuspLikelihoodCoordinate x)) 0 := by
    unfold factorCurvature factorLogSlope
    fun_prop (disch := positivity)
  let L : ℝ → ℝ := fun x =>
    (iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x)-
      factorCurvature (thetaCuspLikelihoodCoordinate x)*
        (iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x)
  have hj (n : ℕ) : ContinuousAt (iteratedDeriv n thetaCuspLogSource) 0 :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource n 0).continuousAt
  have hLc : ContinuousAt L 0 := by dsimp only [L]; fun_prop
  have hL0 : L 0=0 := by
    simp only [L,iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 7 from ⟨3,rfl⟩),
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 from ⟨2,rfl⟩),
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1,rfl⟩),
      mul_zero,sub_self]
  have hlim : Tendsto L (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [hL0] using hLc.tendsto.mono_left nhdsWithin_le_nhds
  let Q : ℝ → ℝ := fun x => -128*(thetaCuspLikelihoodCoordinate x+3/2)^3/
    ((thetaCuspLikelihoodCoordinate x)^2*(thetaCuspLikelihoodCoordinate x+3))*
      sourceGrowth (thetaCuspLikelihoodCoordinate x)
  have hQc : ContinuousAt Q 0 := by
    have hg := continuousAt_sourceGrowth_coordinate_zero
    dsimp only [Q]
    fun_prop (disch := positivity)
  have heq : L =ᶠ[nhdsWithin 0 (Ioi 0)] Q := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact source_growth_eq hx
  have hz := tendsto_nhds_unique (hlim.congr' heq) (hQc.tendsto.mono_left nhdsWithin_le_nhds)
  have hmul : (-128*(thetaCuspLikelihoodCoordinate 0+3/2)^3/
      ((thetaCuspLikelihoodCoordinate 0)^2*(thetaCuspLikelihoodCoordinate 0+3)))*
        sourceGrowth (thetaCuspLikelihoodCoordinate 0)=0 := hz.symm
  have hfac : -128*(thetaCuspLikelihoodCoordinate 0+3/2)^3/
      ((thetaCuspLikelihoodCoordinate 0)^2*(thetaCuspLikelihoodCoordinate 0+3)) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (by positivity))
    · positivity
  exact (mul_eq_zero.mp hmul).resolve_left hfac
end
end RHTower.ThetaCuspDefect
