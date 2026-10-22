import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalGreenDefect
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceHorizonModeLimits
import GaloisForLFunctions.HTGeometry.NegativeWronskianUniqueness

/-! Identification of the actual causal Laplace profile with the original endpoint Green response. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMModularCore D4BMLaplaceRadial D4BMJointWave
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- The actual causal transform equals the literal Green correction with its physical onset transform. -/
theorem principalLaplaceProfile_eq_principalDifference (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hc : PrincipalChamber q w)
    (x : ℝ) (hx : x < 0) : principalLaplaceProfile q branch a i w hw x=
      principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i x := by
  have hd := principalGreenDefect_hasDerivAt q branch a i w hw hc
  have hm (outer : Bool) (t : ℝ) (ht : t < 0) :
      HasDerivAt (tortoiseMode outer w (principalFrequency q i)) (tortoiseModeFirst outer w (principalFrequency q i) t) t ∧
        HasDerivAt (tortoiseModeFirst outer w (principalFrequency q i))
          (principalHomogeneousCoefficient q i w t*tortoiseMode outer w (principalFrequency q i) t) t := by
    have h := tortoiseMode_hasDerivAt (hc i) outer t ht
    refine ⟨h.1,h.2.congr_deriv ?_⟩
    rw [tortoiseMode_equation (hc i) outer t ht,principalFrequency_parameter]
    unfold principalHomogeneousCoefficient
    ring
  have hz := negative_homogeneous_eq_zero
    (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
    (fun t ht => (hm false t ht).1) (fun t ht => (hm false t ht).2)
    (fun t ht => (hm true t ht).1) (fun t ht => (hm true t ht).2)
    (neg_ne_zero.mpr (connection_ne_zero (hc i)))
    (fun t ht => tortoiseMode_wronskian (hc i) t ht)
    (connection_ne_zero (hc i)) (tortoiseHorizon_boundary (hc i))
    (principalGreenDefect_boundary q branch a i w hw hc)
    (tortoiseHorizon_tendsto_horizon (hc i)) (tortoiseHorizonFirst_tendsto_horizon (hc i))
    (principalGreenDefect_bounded q branch a i w hw hc)
    (principalGreenDefectFirst_bounded_tail q branch a i w hw hc) x hx
  exact sub_eq_zero.mp hz

/-- Identification holds for the actual original L² transform class, not only its selected representative. -/
theorem principalTimeLaplace_ae_principalDifference (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hc : PrincipalChamber q w) :
    (principalTimeLaplace q branch a i w : ℝ → ℂ) =ᵐ[radialMeasure]
      principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i := by
  filter_upwards [ae_restrict_of_ae (s := Iio (0:ℝ)) (principalLaplaceProfile_ae q branch a i w hw),
    ae_restrict_mem measurableSet_Iio] with x ha hx
  exact ha.symm.trans (principalLaplaceProfile_eq_principalDifference q branch a i w hw hc x hx)

end
end RHTower.D4BMJointSource
