import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLowCuspPower
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarCutoffPeriodStrip
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The reverse cutoff kernel has its actual reflected Eisenstein height mean. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMJointSource D4BMGlobalAngularResponse D4BMAngularSeries D4BMCuspProjection
noncomputable section

/-- The original full scalar has its exact two-power mean on the standard unit interval. -/
theorem cuspScalar_unit_interval_mean (u : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0:ℝ) 1, scalar u ![x,y]) = principal u ![0,y] := by
  have hp : Function.Periodic (fun x : ℝ => scalar u ![x,y]) 1 := by
    intro x
    exact d4BM_completedEisensteinCuspLeg_scalar_periodic u y x
  have hs := hp.intervalIntegral_add_eq 0 (-1/2)
  have hs' : (∫ x in (0:ℝ)..1, scalar u ![x,y]) =
      ∫ x in (-1/2:ℝ)..(1/2:ℝ), scalar u ![x,y] := by
    convert hs using 1 <;> norm_num
  rw [intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
    intervalIntegral.integral_of_le (show (-1/2:ℝ)≤1/2 by norm_num)] at hs'
  rw [integral_Ico_eq_integral_Ioc,hs']
  exact mean_scalar u hy

/-- The reverse kernel's full original horizontal mean is the reflected completed-zeta power. -/
theorem lowCuspPower_completed_mean (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (y : ℝ) (hy : 2 ≤ y) :
    (∫ x in Ico (0:ℝ) 1,
      reflectedCompletedLambda (2*P.s)*
        periodize (cuspHeightSeed (lowCuspPower P.s)) (ofComplex (⟨x,y⟩:ℂ))) =
      reflectedCompletedLambda (2*P.s-1)*(y:ℂ)^(1-P.s) := by
  have hy0 : 0 < y := by linarith
  have he (x : ℝ) : reflectedCompletedLambda (2*P.s)*
      periodize (cuspHeightSeed (lowCuspPower P.s)) (ofComplex (⟨x,y⟩:ℂ)) =
      scalar (P.s-1/2) ![x,y]-reflectedCompletedLambda (2*P.s)*(y:ℂ)^P.s := by
    have him : (ofComplex (⟨x,y⟩:ℂ)).im = y := by
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      rfl
    rw [lowCuspPower_periodize_completed P _ (by rw [him]; exact hy),him]
    congr 1
    rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
    rfl
  have hf : Continuous (fun x : ℝ => scalar (P.s-1/2) ![x,y]) :=
    (cuspLeg_contDiffOn .scalar (P.s-1/2)).continuousOn.comp_continuous (by fun_prop) (fun _ => hy0)
  simp_rw [he]
  rw [integral_sub (hf.integrableOn_Icc.mono_set Ico_subset_Icc_self) (integrable_const _),
    cuspScalar_unit_interval_mean _ hy0]
  have hc : (∫ _x in Ico (0:ℝ) 1, reflectedCompletedLambda (2*P.s)*(y:ℂ)^P.s) =
      reflectedCompletedLambda (2*P.s)*(y:ℂ)^P.s := by simp
  rw [hc]
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,Bool.false_eq_true,if_false,if_true,mul_one]
  norm_num only
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [show (2:ℂ)*(P.s-1/2)=2*P.s-1 by ring,
    show (1:ℂ)+(2*P.s-1)=2*P.s by ring,
    show (1/2:ℂ)+(-1)*(P.s-1/2)=1-P.s by ring,
    show (1/2:ℂ)+1*(P.s-1/2)=P.s by ring]
  ring

end
end RHTower.D4BMModularCore
