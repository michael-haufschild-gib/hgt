import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularFunctional
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCompleteL2Meromorphy

/-! The original complete source in the topology admitting its physical angular test. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem height_forcing (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (p : ℝ × UpperHalfPlane) :
    (p.2.im:ℂ) * continuedCuspResidualForcing q branch w a p =
      reducedCoefficient (physicalRate q branch) w a
        (continuedOnset (physicalRate q branch) w) p.1 *
        ((p.2.im:ℂ)^(1:ℂ) * squareResidual q (coordinates p.2)) +
      ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i p.1 *
        ((p.2.im:ℂ)^(1:ℂ) * cutoffCommutator (principalExponent q i) (coordinates p.2)) := by
  simp only [continuedCuspResidualForcing,Complex.cpow_one,mul_add,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- The actual complete forcing remains square-integrable after multiplication by height. -/
theorem weightedCuspResidualForcing_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (fun p : ℝ × UpperHalfPlane =>
      (p.2.im:ℂ) * continuedCuspResidualForcing q branch w a p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  have hm := l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _
    (reducedCoefficient_memLp_horizon (physicalRate q branch) w a
      (continuedOnset (physicalRate q branch) w) (abs_lt.mp hwr).1)
    (weightedSquareResidual_memLp q 1)
  have hs := memLp_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _
      (continuedCutoffRadialCoefficient_band_memLp q branch w a hw hwr i)
      (weightedCutoffCommutator_memLp 1 (principalExponent q i)))
  apply (hm.add hs).ae_eq
  filter_upwards with p
  exact (height_forcing q branch w a p).symm

/-- Height-weighted class of the original complete forcing, defined before any channel expansion. -/
def weightedCuspResidualL2 (q : XiZeroCopy) (branch : Bool) (a w : ℂ) : SpatialSpace :=
  l2Family (radialMeasure.prod D4BMModularCore.measure)
    (fun u p => (p.2.im:ℂ) * continuedCuspResidualForcing q branch u a p) w

/-- All four original channels survive unchanged in the weighted source class. -/
theorem weightedCuspResidualL2_assembly (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    weightedCuspResidualL2 q branch a w =
      l2SeparatedProductContinuousBilinear
        (l2Family radialMeasure (fun u => reducedCoefficient (physicalRate q branch) u a
          (continuedOnset (physicalRate q branch) u)) w) (weightedResidualVector q) +
      ∑ i : Fin 3, l2SeparatedProductContinuousBilinear
        (l2Family radialMeasure (fun u => continuedCutoffRadialCoefficient q branch u a i) w)
        (weightedCutoffVector (principalExponent q i)) := by
  have hM := reducedCoefficient_memLp_horizon (physicalRate q branch) w a
    (continuedOnset (physicalRate q branch) w) (abs_lt.mp hwr).1
  have hC := continuedCutoffRadialCoefficient_band_memLp q branch w a hw hwr
  have hpM := l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _
    hM (weightedSquareResidual_memLp q 1)
  have hpC := fun i => l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _
    (hC i) (weightedCutoffCommutator_memLp 1 (principalExponent q i))
  unfold weightedCuspResidualL2
  simp_rw [height_forcing]
  rw [l2Family_add _ _ _ _ hpM (memLp_finsetSum Finset.univ (fun i _ => hpC i)),
    l2Family_sum _ _ _ hpC,l2Family_separated _ _
      (fun u => reducedCoefficient (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u))
      _ w hM (weightedSquareResidual_memLp q 1)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact l2Family_separated _ _ (fun u => continuedCutoffRadialCoefficient q branch u a i)
    _ w (hC i) (weightedCutoffCommutator_memLp 1 (principalExponent q i))

/-- The complete source germ is meromorphic in the stronger height-weighted joint norm. -/
theorem weightedCuspResidualL2_meromorphicAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) : MeromorphicAt (weightedCuspResidualL2 q branch a) w := by
  let M : Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace :=
    l2SeparatedProductContinuousBilinear.flip (weightedResidualVector q)
  let C (i : Fin 3) : Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace :=
    l2SeparatedProductContinuousBilinear.flip (weightedCutoffVector (principalExponent q i))
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
  exact (weightedCuspResidualL2_assembly q branch u a hu.1 hu.2).symm

end
end RHTower.D4BMJointSource
