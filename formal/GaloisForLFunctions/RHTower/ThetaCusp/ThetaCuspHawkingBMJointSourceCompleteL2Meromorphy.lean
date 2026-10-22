import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceRadialL2Meromorphy
import GaloisForLFunctions.HTGeometry.L2MeromorphicAlgebra

/-! Genuine meromorphy of the complete original residual in the actual joint L² space. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The complete original continued source is admitted on the entire nonreal continuation band. -/
theorem continuedCuspResidualForcing_band_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (continuedCuspResidualForcing q branch w a) 2 (radialMeasure.prod D4BMModularCore.measure) := by
  have hm := l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _
    (reducedCoefficient_memLp_horizon (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w)
      (abs_lt.mp hwr).1) (squareResidual_memLp q)
  have hs := memLp_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _
      (continuedCutoffRadialCoefficient_band_memLp q branch w a hw hwr i)
      (cutoffCommutator_memLp (principalExponent q i)))
  exact hm.add hs

/-- The actual complete residual class: no channel, cutoff derivative, or pole numerator is removed. -/
def continuedCuspResidualL2 (q : XiZeroCopy) (branch : Bool) (a w : ℂ) : SpatialSpace :=
  l2Family (radialMeasure.prod D4BMModularCore.measure) (fun u => continuedCuspResidualForcing q branch u a) w

/-- Exact assembly from the same radial source classes and the original admitted angular factors. -/
theorem continuedCuspResidualL2_assembly (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    continuedCuspResidualL2 q branch a w =
      l2SeparatedProductContinuousBilinear
        (l2Family radialMeasure (fun u => reducedCoefficient (physicalRate q branch) u a
          (continuedOnset (physicalRate q branch) u)) w)
        ((squareResidual_memLp q).toLp (fun z => squareResidual q (coordinates z)))+
      ∑ i : Fin 3, l2SeparatedProductContinuousBilinear
        (l2Family radialMeasure (fun u => continuedCutoffRadialCoefficient q branch u a i) w)
        ((cutoffCommutator_memLp (principalExponent q i)).toLp
          (fun z => cutoffCommutator (principalExponent q i) (coordinates z))) := by
  have hM := reducedCoefficient_memLp_horizon (physicalRate q branch) w a
    (continuedOnset (physicalRate q branch) w) (abs_lt.mp hwr).1
  have hC := continuedCutoffRadialCoefficient_band_memLp q branch w a hw hwr
  have hpM := l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _ hM (squareResidual_memLp q)
  have hpC := fun i => l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _ (hC i)
    (cutoffCommutator_memLp (principalExponent q i))
  unfold continuedCuspResidualL2 continuedCuspResidualForcing
  rw [l2Family_add _ _ _ _ hpM (memLp_finsetSum Finset.univ (fun i _ => hpC i)),
    l2Family_sum _ _ _ hpC,l2Family_separated _ _
      (fun u => reducedCoefficient (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u))
      _ w hM (squareResidual_memLp q)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact l2Family_separated _ _ (fun u => continuedCutoffRadialCoefficient q branch u a i) _ w (hC i) (cutoffCommutator_memLp (principalExponent q i))

/-- The full original cusp residual has a genuine joint L²-valued meromorphic germ at every
nonreal frequency in the band. This is a norm-valued conclusion, not merely pointwise meromorphy. -/
theorem continuedCuspResidualL2_meromorphicAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) : MeromorphicAt (continuedCuspResidualL2 q branch a) w := by
  let M : Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace := l2SeparatedProductContinuousBilinear.flip
    ((squareResidual_memLp q).toLp (fun z => squareResidual q (coordinates z)))
  let C (i : Fin 3) : Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace := l2SeparatedProductContinuousBilinear.flip
    ((cutoffCommutator_memLp (principalExponent q i)).toLp
      (fun z => cutoffCommutator (principalExponent q i) (coordinates z)))
  have hm := meromorphicAt_continuousLinearMap M _ w
    (continuedReducedCoefficient_l2_analyticAt q branch w a (abs_lt.mp hwr).1).meromorphicAt
  have hc := MeromorphicAt.fun_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ =>
    meromorphicAt_continuousLinearMap (C i) _ w
      (continuedCutoffRadialCoefficient_l2_meromorphicAt q branch w a hw hwr i))
  apply (hm.add hc).congr
  have hn : ∀ᶠ u in 𝓝[≠] w, u.im ≠ 0 ∧ |u.re| < 2 :=
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (Complex.continuous_re.continuousAt.abs.eventually_lt_const hwr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn] with u hu
  exact (continuedCuspResidualL2_assembly q branch u a hu.1 hu.2).symm

end
end RHTower.D4BMJointSource
