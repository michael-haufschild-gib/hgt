import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectCumulants
import GaloisForLFunctions.RHTower.ThetaCuspExactCompletedC5SeamFarTail
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati

/-!
# Global fifth-versus-third logarithmic jet sign

The complete likelihood cumulant cooling functional makes the normalized
source defect strictly decreasing. Modular odd-jet vanishing fixes its
value at the center to one. Therefore L5 - 4 L3 is strictly positive on
the positive real axis, without an assumed source sign.
-/

namespace RHTower.ThetaCuspDefect
open Set Filter
noncomputable section

def sourceDefectFactor (q : ℝ) : ℝ := 864*(q+3/2)^2*(q+3)/q^5
def sourceDefectRatio (x : ℝ) : ℝ := logarithmicDefectRatio (thetaCuspLikelihoodCoordinate x)

theorem sourceDefectFactor_pos {q : ℝ} (hq : 0 < q) : 0 < sourceDefectFactor q := by
  unfold sourceDefectFactor
  positivity

theorem source_defect_eq {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x =
      sourceDefectFactor (thetaCuspLikelihoodCoordinate x)*(1-sourceDefectRatio x) := by
  rw [iteratedDeriv_five_thetaCuspLogSource_eq_full_jets hx,
    iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx,
    ←thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx]
  unfold thetaCuspFullLogJetFive thetaCuspFirstAtomLogJetThree
    thetaCuspBornWittenLogFifthDerivative thetaCuspBornWittenLogThirdDerivative
    thetaCuspLikelihoodSourceLogPartitionJetFive thetaCuspLikelihoodSourceLogPartitionJetThree
  simp only [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  unfold sourceDefectFactor sourceDefectRatio logarithmicDefectRatio
  have hq := thetaCuspLikelihoodCoordinate_pos hx.le
  have hq3 : thetaCuspLikelihoodCoordinate x+3 ≠ 0 := by positivity
  field_simp [hq.ne',hq3]
  ring

theorem hasDerivAt_sourceDefectRatio {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt sourceDefectRatio
      ((-(thetaCuspLikelihoodCoordinate x)^4/(27*(thetaCuspLikelihoodCoordinate x+3)^2)*
        coolingFunctional (thetaCuspLikelihoodCoordinate x)
          (likelihoodCumulant (thetaCuspLikelihoodCoordinate x)))*
        (2*thetaCuspSingleAtomReflectionScale 1 x)) x :=
  (hasDerivAt_logarithmicDefectRatio (thetaCuspLikelihoodCoordinate_pos hx)).comp x
    (hasDerivAt_thetaCuspLikelihoodCoordinate x)

theorem sourceDefectRatio_deriv_neg {x : ℝ} (hx : 0 ≤ x) :
    deriv sourceDefectRatio x < 0 := by
  rw [(hasDerivAt_sourceDefectRatio hx).deriv]
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  have hco : -(thetaCuspLikelihoodCoordinate x)^4/
      (27*(thetaCuspLikelihoodCoordinate x+3)^2) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (pow_pos hq 4)) (by positivity)
  have hscale : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hco (source_cooling_cumulant_pos hx)) hscale

theorem sourceDefectRatio_strictAntiOn : StrictAntiOn sourceDefectRatio (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_sourceDefectRatio (mem_Ici.mp hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact sourceDefectRatio_deriv_neg hx'.le

private theorem continuousAt_sourceDefectFactor_coordinate_zero :
    ContinuousAt (fun x => sourceDefectFactor (thetaCuspLikelihoodCoordinate x)) 0 := by
  have hq := hasDerivAt_thetaCuspLikelihoodCoordinate 0
  have hq0 := thetaCuspLikelihoodCoordinate_pos (show (0:ℝ) ≤ 0 from le_rfl)
  have h := (((((hq.add_const (3/2:ℝ)).pow 2).const_mul 864).mul
    (hq.add_const (3:ℝ))).div (hq.pow 5) (pow_ne_zero 5 hq0.ne')).continuousAt
  exact h

theorem sourceDefectRatio_zero : sourceDefectRatio 0 = 1 := by
  let F : ℝ → ℝ := fun x => iteratedDeriv 5 thetaCuspLogSource x-
    4*iteratedDeriv 3 thetaCuspLogSource x
  have hFc : ContinuousAt F 0 :=
    ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 0).sub
      ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 0).const_mul 4)).continuousAt
  have hF0 : F 0 = 0 := by
    simp only [F,iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 from ⟨2,rfl⟩),
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1,rfl⟩),mul_zero,sub_self]
  have hlim : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [hF0] using hFc.tendsto.mono_left nhdsWithin_le_nhds
  have hRc : ContinuousAt sourceDefectRatio 0 :=
    (hasDerivAt_sourceDefectRatio (show (0:ℝ) ≤ 0 from le_rfl)).continuousAt
  have hright : ContinuousAt
      (fun x => sourceDefectFactor (thetaCuspLikelihoodCoordinate x)*(1-sourceDefectRatio x)) 0 :=
    continuousAt_sourceDefectFactor_coordinate_zero.mul (continuousAt_const.sub hRc)
  have heq : F =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun x => sourceDefectFactor (thetaCuspLikelihoodCoordinate x)*(1-sourceDefectRatio x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact source_defect_eq hx
  have hz := tendsto_nhds_unique (hlim.congr' heq) (hright.tendsto.mono_left nhdsWithin_le_nhds)
  have hmul : sourceDefectFactor (thetaCuspLikelihoodCoordinate 0)*(1-sourceDefectRatio 0)=0 := hz.symm
  have hp := (sourceDefectFactor_pos
    (thetaCuspLikelihoodCoordinate_pos (show (0:ℝ) ≤ 0 from le_rfl))).ne'
  have h := (mul_eq_zero.mp hmul).resolve_left hp
  linarith

theorem source_defect_pos {x : ℝ} (hx : 0 < x) :
    0 < iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x := by
  rw [source_defect_eq hx]
  have hR : sourceDefectRatio x < 1 := by
    have h := sourceDefectRatio_strictAntiOn (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
      (show x ∈ Ici 0 from hx.le) hx
    simpa only [sourceDefectRatio_zero] using h
  exact mul_pos (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx.le))
    (sub_pos.mpr hR)
end
end RHTower.ThetaCuspDefect
