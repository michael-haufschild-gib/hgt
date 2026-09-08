import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceTrace
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Original negative-ray source, equation and spatial admission of the causal Laplace profile. -/
open MeasureTheory Set Filter TemperedDistribution
open scoped SchwartzMap Laplacian
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMJointWave D4BMModularCore
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The continuous transform profile belongs to the original spatial L² class. -/
theorem principalLaplaceProfile_memLp (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    MemLp (principalLaplaceProfile q branch a i w hw) 2 (volume : Measure ℝ) :=
  (Lp.memLp (principalTimeLaplace q branch a i w)).ae_eq (principalLaplaceProfile_ae q branch a i w hw).symm

/-- The convergent forcing transform has the literal original negative-ray source representative. -/
theorem principalForcingLaplace_ae_negative (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : -2 < w.re) :
    ((∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t) : FourierRealL2) =ᵐ[radialMeasure]
      (fun x => principalAmplitude q i*reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) x) := by
  rw [principalTimeForcing_laplace q branch a i w hw]
  have hs := (Lp.coeFn_smul (principalAmplitude q i)
    (negativeOddExtension (radialSourceLaplaceVector q branch a w hw))).filter_mono
      (ae_mono (show radialMeasure ≤ volume from Measure.restrict_le_self))
  filter_upwards [hs,negativeOddExtension_ae_negative (radialSourceLaplaceVector q branch a w hw),
    radialSourceLaplaceVector_ae q branch a w hw] with x hs he hf
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,he,hf]

private theorem negativePairing_eq (f g : ℝ → ℂ) (hs : tsupport f ⊆ Iio (0:ℝ)) :
    (∫ x : ℝ, f x • g x) = ∫ x in Iio (0:ℝ), f x • g x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),zero_smul]

/-- The actual transformed profile solves the original radial weak equation with its physical onset factor. -/
theorem principalLaplaceProfile_weak_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re)
    (ψ : 𝓢(ℝ,ℂ)) (hψ : tsupport (ψ : ℝ → ℂ) ⊆ Iio (0:ℝ)) :
    w^2*(∫ x in Iio (0:ℝ), ψ x • principalLaplaceProfile q branch a i w hw x)-
      (∫ x in Iio (0:ℝ), deriv (deriv (ψ : ℝ → ℂ)) x • principalLaplaceProfile q branch a i w hw x) =
      (∫ x in Iio (0:ℝ), ψ x • (principalAmplitude q i*reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) x))+
        ∫ x in Iio (0:ℝ), ψ x • (principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*
          principalLaplaceProfile q branch a i w hw x) := by
  let U := principalTimeLaplace q branch a i w
  let F := ∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t
  have h := principalTimeLaplace_probe_equation q branch a i ψ w hw
  simp only [l2SchwartzProbe_integral,SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real,iteratedDeriv_succ,iteratedDeriv_zero] at h
  have h₂ : tsupport (deriv (deriv (ψ : ℝ → ℂ))) ⊆ Iio (0:ℝ) :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hψ)
  rw [negativePairing_eq _ _ hψ,negativePairing_eq _ _ h₂,
    negativePairing_eq _ _ hψ,negativePairing_eq _ _ hψ] at h
  have ha : principalLaplaceProfile q branch a i w hw =ᵐ[radialMeasure] U :=
    ae_restrict_of_ae (principalLaplaceProfile_ae q branch a i w hw)
  have hp (g : ℝ → ℂ) : (∫ x in Iio (0:ℝ), g x • principalLaplaceProfile q branch a i w hw x) =
      ∫ x in Iio (0:ℝ), g x • U x := by
    apply integral_congr_ae
    filter_upwards [ha] with x hx
    rw [hx]
  rw [hp,hp,h]
  congr 1
  · apply integral_congr_ae
    have hw' : -2 < w.re := lt_trans (by linarith [principalResponseGrowth_nonneg q i]) hw
    filter_upwards [principalForcingLaplace_ae_negative q branch a i w hw'] with x hx
    rw [hx]
  · apply integral_congr_ae
    have hv := ae_restrict_of_ae (s := Iio (0:ℝ)) (principalRadialPotentialOp_ae q i U)
    filter_upwards [ha,hv] with x hx hv
    rw [hx,hv]

end
end RHTower.D4BMJointSource
