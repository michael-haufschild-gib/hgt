import GaloisForLFunctions.HTGeometry.L2BesselDistribution
import GaloisForLFunctions.HTGeometry.EuclideanSobolevLaplacianGain

/-! The inverse elliptic range satisfies the original spatial differential equation. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem bessel_two_laplacian (f : 𝓢'(ℝ,ℂ)) :
    ((2*Real.pi)^(2 : ℕ):ℝ) • besselPotential ℝ ℂ 2 f = ((2*Real.pi)^(2 : ℕ):ℝ) • f-Δ f := by
  rw [besselPotential_two_euclidean,smul_sub]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
  simp

/-- The actual inverse-frequency image solves the original elliptic equation as a distribution. -/
theorem unitWaveEllipticInv_distribution_equation (f : FourierRealL2) :
    ((2*Real.pi)^(2 : ℕ):ℝ) • ((unitWaveEllipticInv f : FourierRealL2) : 𝓢'(ℝ,ℂ))-
      Δ ((unitWaveEllipticInv f : FourierRealL2) : 𝓢'(ℝ,ℂ)) = (f : 𝓢'(ℝ,ℂ)) := by
  rw [← bessel_two_laplacian,unitWaveEllipticInv_toDistribution]
  change ((2*Real.pi)^(2 : ℕ):ℝ) • besselPotential ℝ ℂ 2
    (((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) • besselPotential ℝ ℂ (-2) (f : 𝓢'(ℝ,ℂ))) = _
  rw [ContinuousLinearMap.map_smul_of_tower,besselPotential_besselPotential_apply]
  norm_num only [neg_add_cancel,besselPotential_zero,ContinuousLinearMap.id_apply]
  rw [smul_smul]
  have h : (2*Real.pi)^(2 : ℕ)*((2*Real.pi)⁻¹*(2*Real.pi)⁻¹) = (1:ℝ) := by
    field_simp
  rw [h,one_smul]

/-- The original spatial equation can be tested against every Schwartz probe. -/
theorem unitWaveEllipticInv_schwartz_equation (f : FourierRealL2) (ψ : 𝓢(ℝ,ℂ)) :
    ((2*Real.pi)^(2 : ℕ):ℝ) • (∫ x : ℝ, ψ x • unitWaveEllipticInv f x)-
      (∫ x : ℝ, deriv (deriv (ψ : ℝ → ℂ)) x • unitWaveEllipticInv f x) = ∫ x : ℝ, ψ x • f x := by
  have h := congrArg (fun T : 𝓢'(ℝ,ℂ) => T ψ) (unitWaveEllipticInv_distribution_equation f)
  simpa only [sub_apply,smul_apply,
    TemperedDistribution.laplacian_apply_apply,Lp.toTemperedDistribution_apply,
    SchwartzMap.laplacian_apply,InnerProductSpace.laplacian_eq_iteratedDeriv_real,
    iteratedDeriv_succ,iteratedDeriv_zero] using h

end
end GaloisForLFunctions.HTGeometry
