import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointConformalConjugation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceFieldDifferential

/-! Identification of the Euclidean conjugation with the original metric wave operator. -/
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMJointConformal
open D4BMJointSource D4BMHorizon
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def angularSlice (U : Point3 → ℂ) (t : ℝ) (z : Fin 2 → ℝ) : ℂ := U ![t,z 0,z 1]

theorem angularSlice_smooth (U : Point3 → ℂ) (t : ℝ) (z : Fin 2 → ℝ)
    (hU : ContDiffAt ℝ 2 U ![t,z 0,z 1]) : ContDiffAt ℝ 2 (angularSlice U t) z := by
  apply hU.comp z
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_const
  · exact (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
  · exact (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt

theorem angularSlice_second (U : Point3 → ℂ) (t : ℝ) (z : Fin 2 → ℝ)
    (hU : ContDiffAt ℝ 2 U ![t,z 0,z 1]) (i : Fin 2) :
    coordDeriv i (coordDeriv i (angularSlice U t)) z =
      coordDeriv i.succ (coordDeriv i.succ U) ![t,z 0,z 1] := by
  rw [coordinate_secondDerivative _ z i (angularSlice_smooth U t z hU),
    coordinate_secondDerivative _ ![t,z 0,z 1] i.succ hU]
  have he : (fun s => angularSlice U t (coordinateLine z i s)) =
      (fun s => U (coordinateLine ![t,z 0,z 1] i.succ s)) := by
    funext s
    apply congrArg U
    ext j
    fin_cases i <;> fin_cases j <;> simp [coordinateLine]
  rw [he]
  fin_cases i <;> rfl

theorem radialSlice_second (U : Point3 → ℂ) (t : ℝ) (z : Fin 2 → ℝ)
    (hU : ContDiffAt ℝ 2 U ![t,z 0,z 1]) :
    deriv (deriv (fun s => angularSlice U s z)) t =
      coordDeriv 0 (coordDeriv 0 U) ![t,z 0,z 1] := by
  rw [coordinate_secondDerivative _ ![t,z 0,z 1] 0 hU]
  have he : (fun s => angularSlice U s z) = (fun s => U (coordinateLine ![t,z 0,z 1] 0 s)) := by
    funext s
    apply congrArg U
    ext j
    fin_cases j <;> simp [coordinateLine]
  rw [he]
  rfl

/-- The original radial and metric angular wave is exactly the three-coordinate differential expression. -/
theorem originalWave_coordinate (U : Point3 → ℂ) (w : ℂ) (t : ℝ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (hU : ContDiffAt ℝ 2 U ![t,z 0,z 1]) :
    fieldWave w (angularSlice U) t z =
      w^2*U ![t,z 0,z 1]-jointSpatial U ![t,z 0,z 1] := by
  have hc : (horizonCoordinate t:ℂ) = (warp t:ℂ)^2 := by
    have hr := congrArg Complex.ofReal (warp_relation t)
    dsimp only [horizonCoordinate]
    push_cast at hr ⊢
    linear_combination -hr
  unfold fieldWave
  rw [radialSlice_second U t z hU,scalarLaplacian_eq _ z hz]
  simp_rw [angularSlice_second U t z hU]
  rw [hc]
  dsimp [angularSlice,jointSpatial,ellipticCoefficient]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  push_cast
  ring

/-- Exact Euclidean reduction of the original independent-frequency wave on actual fields. -/
theorem originalWave_conjugation (F : Point3 → ℂ) (w : ℂ) (t : ℝ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (hF : ContDiffAt ℝ 2 F (chart ![t,z 0,z 1])) :
    fieldWave w (angularSlice (liftedField F)) t z =
      weight ![t,z 0,z 1]*((w^2-1/4)*F (chart ![t,z 0,z 1])-
        (chart ![t,z 0,z 1] 1:ℂ)^2*flatLaplacian F (chart ![t,z 0,z 1])) := by
  rw [originalWave_coordinate _ w t z hz (liftedField_smooth F _ hz hF)]
  exact jointWave_conjugation F w _ hz hF

end
end RHTower.D4BMJointConformal
