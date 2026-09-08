import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalSpatialEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalSpatialTrace
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The original negative-ray wave equation with its literal source and proved boundary trace. -/
open MeasureTheory Set Filter
open scoped SchwartzMap
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem negativePairing_eq (f g : ℝ → ℂ) (hs : tsupport f ⊆ Iio (0:ℝ)) :
    (∫ x : ℝ, f x • g x) = ∫ x in Iio (0:ℝ), f x • g x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),zero_smul]

/-- The actual causal profile solves the physical radial equation against every interior Schwartz test.
The source is the literal delayed radial source, and no auxiliary free-mass term remains. -/
theorem principalTimeProfile_weak_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (τ : ℝ) (ψ : 𝓢(ℝ,ℂ)) (hψ : tsupport (ψ : ℝ → ℂ) ⊆ Iio (0:ℝ)) :
    (∫ x in Iio (0:ℝ), ψ x • deriv (deriv (principalTimeResponse q branch a i)) τ x)-
      (∫ x in Iio (0:ℝ), deriv (deriv (ψ : ℝ → ℂ)) x • principalTimeProfile q branch a i τ x) =
      (∫ x in Iio (0:ℝ), ψ x • (principalAmplitude q i*timeReducedCoefficient (physicalRate q branch) a τ x))+
        ∫ x in Iio (0:ℝ), ψ x • (principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*
          principalTimeProfile q branch a i τ x) := by
  have h₂ : tsupport (deriv (deriv (ψ : ℝ → ℂ))) ⊆ Iio (0:ℝ) :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hψ)
  have h := principalTimeResponse_schwartz_equation q branch a i τ ψ
  rw [negativePairing_eq _ _ hψ,negativePairing_eq _ _ h₂,
    negativePairing_eq _ _ hψ,negativePairing_eq _ _ hψ] at h
  have ha : principalTimeProfile q branch a i τ =ᵐ[volume.restrict (Iio (0:ℝ))]
      principalTimeResponse q branch a i τ := ae_restrict_of_ae (principalTimeProfile_ae q branch a i τ)
  have he : (∫ x in Iio (0:ℝ), deriv (deriv (ψ : ℝ → ℂ)) x • principalTimeProfile q branch a i τ x) =
      ∫ x in Iio (0:ℝ), deriv (deriv (ψ : ℝ → ℂ)) x • principalTimeResponse q branch a i τ x := by
    apply integral_congr_ae
    filter_upwards [ha] with x hx
    rw [hx]
  rw [he,h]
  congr 1
  · apply integral_congr_ae
    filter_upwards [principalTimeForcing_ae_negative q branch a i τ] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [ha] with x hx
    rw [hx]

end
end RHTower.D4BMJointSource
