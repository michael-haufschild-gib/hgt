import GaloisForLFunctions.HTGeometry.UnitWaveDistributionEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalTimeSecondDerivative

/-! The literal principal radial wave equation, including the native complex potential. -/
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The physical potential after cancellation of the auxiliary free mass. -/
def principalRadialPotentialOp (q : XiZeroCopy) (i : Fin 3) : FourierRealL2 →L[ℂ] FourierRealL2 :=
  principalWavePotentialOp q i-(((2*Real.pi)^2:ℝ):ℂ) • ContinuousLinearMap.id ℂ FourierRealL2

/-- The remaining multiplier is exactly the original radial potential. -/
theorem principalRadialPotentialOp_ae (q : XiZeroCopy) (i : Fin 3) (u : FourierRealL2) :
    principalRadialPotentialOp q i u =ᵐ[volume]
      (fun x : ℝ => principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*u x) := by
  have hm := Lp.coeFn_smul ((((2*Real.pi)^2:ℝ):ℂ)) u
  filter_upwards [principalWavePotentialOp_ae q i u,hm,
    Lp.coeFn_sub (principalWavePotentialOp q i u) ((((2*Real.pi)^2:ℝ):ℂ) • u)] with x hW hm hs
  change (principalWavePotentialOp q i u-(((2*Real.pi)^2:ℝ):ℂ) • u) x = _
  rw [hs,Pi.sub_apply,hW,hm]
  simp only [Pi.smul_apply,smul_eq_mul,principalWavePotential]
  ring

/-- The actual causal family satisfies its original mass-free radial wave equation in distributions. -/
theorem principalTimeResponse_distribution_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    ((deriv (deriv (principalTimeResponse q branch a i)) τ : FourierRealL2) : 𝓢'(ℝ,ℂ))-
      Δ ((principalTimeResponse q branch a i τ : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
      ((principalTimeForcing q branch a i τ : FourierRealL2) : 𝓢'(ℝ,ℂ))+
        ((principalRadialPotentialOp q i (principalTimeResponse q branch a i τ) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  let U := principalTimeResponse q branch a i τ
  let F := principalTimeForcing q branch a i τ
  let B := deriv (deriv (principalTimeResponse q branch a i)) τ
  let D := Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2
  have hU : unitWaveEllipticInv (F+principalWavePotentialOp q i U-B) = U :=
    (principalTimeResponse_wave_graph q branch a i τ).symm
  have h := unitWaveEllipticInv_distribution_equation (F+principalWavePotentialOp q i U-B)
  rw [hU] at h
  change ((2*Real.pi)^2:ℝ) • D U-Δ (D U) = D (F+principalWavePotentialOp q i U-B) at h
  rw [map_sub,map_add] at h
  have hW : principalWavePotentialOp q i U = (((2*Real.pi)^2:ℝ):ℂ) • U+principalRadialPotentialOp q i U := by
    change principalWavePotentialOp q i U = (((2*Real.pi)^2:ℝ):ℂ) • U+
      (principalWavePotentialOp q i U-(((2*Real.pi)^2:ℝ):ℂ) • U)
    abel
  rw [hW,map_add,map_smul] at h
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
  have he := congrArg (fun z : 𝓢'(ℝ,ℂ) => z+D B-(((2*Real.pi)^2:ℝ):ℂ) • D U) h
  change D B-Δ (D U) = D F+D (principalRadialPotentialOp q i U)
  convert he using 1
  all_goals abel_nf
  all_goals simp

/-- Every actual Schwartz probe sees the original radial second derivative and native potential. -/
theorem principalTimeResponse_schwartz_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (τ : ℝ) (ψ : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, ψ x • deriv (deriv (principalTimeResponse q branch a i)) τ x)-
      (∫ x : ℝ, deriv (deriv (ψ : ℝ → ℂ)) x • principalTimeResponse q branch a i τ x) =
      (∫ x : ℝ, ψ x • principalTimeForcing q branch a i τ x)+
        ∫ x : ℝ, ψ x • (principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*
          principalTimeResponse q branch a i τ x) := by
  have h := congrArg (fun T : 𝓢'(ℝ,ℂ) => T ψ) (principalTimeResponse_distribution_equation q branch a i τ)
  simp only [sub_apply,add_apply,TemperedDistribution.laplacian_apply_apply,Lp.toTemperedDistribution_apply,
    SchwartzMap.laplacian_apply,InnerProductSpace.laplacian_eq_iteratedDeriv_real,
    iteratedDeriv_succ,iteratedDeriv_zero] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [principalRadialPotentialOp_ae q i (principalTimeResponse q branch a i τ)] with x hx
  rw [hx]

end
end RHTower.D4BMJointSource
