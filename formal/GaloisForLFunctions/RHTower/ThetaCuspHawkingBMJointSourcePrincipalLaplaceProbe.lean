import GaloisForLFunctions.HTGeometry.ScalarLaplaceSecondOrder
import GaloisForLFunctions.HTGeometry.L2SchwartzProbe
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalSpatialEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalTimeLaplace

/-! The actual principal acceleration has its original Laplace law against every spatial probe. -/
open MeasureTheory Set TemperedDistribution
open scoped SchwartzMap Laplacian
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMJointWave D4BMModularCore
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The native horizon bound gives a uniform bound on the actual whole-line forcing. -/
theorem principalTimeForcing_bounded (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖principalTimeForcing q branch a i t‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := timeRadialSourceVector_bound q branch a 0 (by norm_num)
  let L : NegativeLineL2 →L[ℂ] FourierRealL2 := principalAmplitude q i • negativeOddExtension
  refine ⟨‖L‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro t
  change ‖L (timeRadialSourceVector (physicalRate q branch) a t)‖ ≤ _
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (by simpa using hb t) (norm_nonneg _))

/-- The paired acceleration is determined by the original spatial equation and literal forcing. -/
theorem principalTimeAcceleration_probe (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (ψ : 𝓢(ℝ,ℂ)) (t : ℝ) :
    l2SchwartzProbe ψ (deriv (deriv (principalTimeResponse q branch a i)) t) =
      l2SchwartzProbe (Δ ψ) (principalTimeResponse q branch a i t)+
        l2SchwartzProbe ψ (principalRadialPotentialOp q i (principalTimeResponse q branch a i t))+
          l2SchwartzProbe ψ (principalTimeForcing q branch a i t) := by
  have h := congrArg (fun T : 𝓢'(ℝ,ℂ) => T ψ) (principalTimeResponse_distribution_equation q branch a i t)
  simp only [sub_apply,add_apply,TemperedDistribution.laplacian_apply_apply] at h
  simp only [l2SchwartzProbe_apply]
  linear_combination h

/-- The exact second time derivative transforms to the frequency square, with zero data derived. -/
theorem principalTimeAcceleration_laplace_probe (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (ψ : 𝓢(ℝ,ℂ)) (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*
      l2SchwartzProbe ψ (deriv (deriv (principalTimeResponse q branch a i)) t)) =
        w^2*l2SchwartzProbe ψ (principalTimeLaplace q branch a i w) := by
  let U := principalTimeResponse q branch a i
  let F := principalTimeForcing q branch a i
  let P := l2SchwartzProbe ψ
  let Q := l2SchwartzProbe (Δ ψ)+P.comp (principalRadialPotentialOp q i)
  let r := principalResponseGrowth q i
  let A := principalResponseSize q branch a i
  obtain ⟨C,hC,hF⟩ := principalTimeForcing_bounded q branch a i
  have hr : 0 ≤ r := principalResponseGrowth_nonneg q i
  have hA : 0 ≤ A := principalResponseSize_nonneg q branch a i
  have hU (t : ℝ) (ht : 0 ≤ t) : ‖U t‖ ≤ A*Real.exp (r*t) := by
    simpa only [U,A,r,abs_of_nonneg ht] using principalTimeResponse_bound q branch a i t
  have hF' (t : ℝ) (ht : 0 ≤ t) : ‖F t‖ ≤ C*Real.exp (r*t) :=
    (hF t).trans (le_mul_of_one_le_right hC (Real.one_le_exp (mul_nonneg hr ht)))
  have hP (L : FourierRealL2 →L[ℂ] ℂ) (t : ℝ) (ht : 0 ≤ t) :
      ‖L (U t)‖ ≤ (‖L‖*A)*Real.exp (r*t) := by
    exact (L.le_opNorm _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hU t ht) (norm_nonneg L))
  have he (t : ℝ) : P (deriv (deriv U) t) = Q (U t)+P (F t) :=
    principalTimeAcceleration_probe q branch a i ψ t
  have hg (t : ℝ) (ht : 0 ≤ t) :
      ‖P (deriv (deriv U) t)‖ ≤ (‖Q‖*A+‖P‖*C)*Real.exp (r*t) := by
    rw [he]
    have hPF : ‖P (F t)‖ ≤ (‖P‖*C)*Real.exp (r*t) :=
      (P.le_opNorm _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hF' t ht) (norm_nonneg P))
    exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hP Q t ht) hPF)
  have hf (t : ℝ) : HasDerivAt (fun t => P (U t)) (P (deriv U t)) t :=
    (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t ((principalTimeResponse_hasDerivAt q branch a i t).differentiableAt.hasDerivAt)
  have hv (t : ℝ) : HasDerivAt (fun t => P (deriv U t)) (P (deriv (deriv U) t)) t :=
    (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t ((principalTimeResponse_second_hasDerivAt q branch a i t).differentiableAt.hasDerivAt)
  have h := scalarLaplace_second_of_growth (fun t => P (U t)) (fun t => P (deriv U t))
    (fun t => P (deriv (deriv U) t)) r (‖P‖*A) (‖Q‖*A+‖P‖*C) hr (by positivity) hf hv
    (P.continuous.comp (principalTimeResponse_second_continuous q branch a i)) (hP P) hg w hw
  have hu₀ : U 0 = 0 := (principalTimeResponse_initial_data q branch a i).1
  have hv₀ : deriv U 0 = 0 := (principalTimeResponse_initial_data q branch a i).2
  simp only [scalarLaplaceDamp,hu₀,hv₀,map_zero,mul_zero,sub_zero] at h
  rw [l2SchwartzProbe_laplace ψ U w (principalTimeResponse_laplace_integrable q branch a i w hw)] at h
  exact h

end
end RHTower.D4BMJointSource
