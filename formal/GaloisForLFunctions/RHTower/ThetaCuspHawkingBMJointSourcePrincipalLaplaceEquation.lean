import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceProbe

/-! The original spatial equation of the genuine principal causal Laplace transform. -/
open MeasureTheory Set TemperedDistribution
open scoped SchwartzMap Laplacian
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every spatial Schwartz probe sees the original frequency equation of the actual transform. -/
theorem principalTimeLaplace_probe_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (ψ : 𝓢(ℝ,ℂ)) (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    w^2*l2SchwartzProbe ψ (principalTimeLaplace q branch a i w)-
      l2SchwartzProbe (Δ ψ) (principalTimeLaplace q branch a i w) =
        l2SchwartzProbe ψ (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t)+
          l2SchwartzProbe ψ (principalRadialPotentialOp q i (principalTimeLaplace q branch a i w)) := by
  let U := principalTimeResponse q branch a i
  let F := principalTimeForcing q branch a i
  let P := l2SchwartzProbe ψ
  let Q := l2SchwartzProbe (Δ ψ)+P.comp (principalRadialPotentialOp q i)
  have hu := principalTimeResponse_laplace_integrable q branch a i w hw
  have hw' : -2 < w.re := lt_trans (by linarith [principalResponseGrowth_nonneg q i]) hw
  have hf := principalTimeForcing_laplace_integrable q branch a i w hw'
  have hiQ : IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ))*Q (U t)) (Ioi 0) := by
    simpa only [U,IntegrableOn,map_smul,smul_eq_mul] using! Q.integrable_comp hu
  have hiP : IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ))*P (F t)) (Ioi 0) := by
    simpa only [F,IntegrableOn,map_smul,smul_eq_mul] using! P.integrable_comp hf
  have hQ := Q.integral_comp_comm hu
  have hP := P.integral_comp_comm hf
  simp only [map_smul,smul_eq_mul] at hQ hP
  have h : (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*P (deriv (deriv U) t)) =
      Q (principalTimeLaplace q branch a i w)+
        P (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • F t) := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Complex.exp (-w*(t:ℂ))*Q (U t)+Complex.exp (-w*(t:ℂ))*P (F t)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        have he : P (deriv (deriv U) t) = Q (U t)+P (F t) :=
          principalTimeAcceleration_probe q branch a i ψ t
        rw [he,mul_add]
      _ = _ := by rw [integral_add hiQ hiP,hQ,hP]; rfl
  rw [principalTimeAcceleration_laplace_probe q branch a i ψ w hw] at h
  change w^2*P (principalTimeLaplace q branch a i w) =
    l2SchwartzProbe (Δ ψ) (principalTimeLaplace q branch a i w)+
      P (principalRadialPotentialOp q i (principalTimeLaplace q branch a i w))+
        P (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • F t) at h
  change w^2*P (principalTimeLaplace q branch a i w)-
    l2SchwartzProbe (Δ ψ) (principalTimeLaplace q branch a i w) = _
  linear_combination h

/-- The actual Bochner transform solves the original radial frequency equation as a distribution. -/
theorem principalTimeLaplace_distribution_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    w^2 • ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ))-
      Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
        (((∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t) : FourierRealL2) : 𝓢'(ℝ,ℂ))+
          ((principalRadialPotentialOp q i (principalTimeLaplace q branch a i w) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  ext ψ
  simp only [sub_apply,smul_apply,add_apply,TemperedDistribution.laplacian_apply_apply,smul_eq_mul]
  exact principalTimeLaplace_probe_equation q branch a i ψ w hw

/-- The forcing in the transformed equation is the literal source with its original onset transform. -/
theorem principalTimeLaplace_original_source_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hw' : -2 < w.re) :
    w^2 • ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ))-
      Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
        ((principalAmplitude q i • negativeOddExtension (radialSourceLaplaceVector q branch a w hw') : FourierRealL2) : 𝓢'(ℝ,ℂ))+
          ((principalRadialPotentialOp q i (principalTimeLaplace q branch a i w) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  rw [← principalTimeForcing_laplace q branch a i w hw']
  exact principalTimeLaplace_distribution_equation q branch a i w hw

end
end RHTower.D4BMJointSource
