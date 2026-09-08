import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalGreenIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCausalCuspSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceResidualAssembly

/-! The complete actual causal source has the literal original cusp-residual Bochner transform. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMModularCore D4BMJointWave D4BMGlobalAngularResponse
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- Common strict right half-plane for the causal evolutions and original endpoint Green chamber. -/
def causalGreenThreshold (q : XiZeroCopy) : ℝ := max (causalPrincipalThreshold q) (principalThreshold q)

/-- Every retained cutoff channel transforms to its literal original spatial coefficient. -/
theorem principalCutoffSpatialOp_laplace_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (hc : PrincipalChamber q w) :
    principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      (fun p : ℝ × UpperHalfPlane => cutoffRadialCoefficient q branch w a (onsetTransform (2*physicalRate q branch) w) i p.1*
        cutoffCommutator (principalExponent q i) (coordinates p.2)) := by
  rw [principalCutoffSpatialOp_apply]
  filter_upwards [l2SeparatedProduct_ae (principalCutoffRadialOp (principalTimeLaplace q branch a i w))
      (cutoffCommutatorVector (principalExponent q i)),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (principalCutoffRadialOp_ae (principalTimeLaplace q branch a i w)),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (principalTimeLaplace_ae_principalDifference q branch a i w hw hc),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (cutoffCommutator_memLp (principalExponent q i)).coeFn_toLp]
      with p hp hr hd ha
  rw [hp]
  change principalCutoffRadialOp (principalTimeLaplace q branch a i w) p.1*
    cutoffCommutatorVector (principalExponent q i) p.2 = _
  simp only [Function.comp_apply] at hr hd ha
  rw [hr,hd]
  change cutoffCommutatorVector (principalExponent q i) p.2 =
    cutoffCommutator (principalExponent q i) (coordinates p.2) at ha
  rw [ha]
  rfl

/-- The full assembled transform equals the admitted original residual vector in the actual joint Hilbert space. -/
theorem causalCuspSourceVector_laplace_original (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalGreenThreshold q < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) =
      cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
        (principalChamber_of_threshold q w ((le_max_right _ _).trans_lt hw)) := by
  have ht : causalPrincipalThreshold q < w.re := (le_max_left _ _).trans_lt hw
  have hc : PrincipalChamber q w := principalChamber_of_threshold q w ((le_max_right _ _).trans_lt hw)
  have hw₀ : -2 < w.re := by have := causalPrincipalThreshold_pos q; linarith
  rw [causalCuspSourceVector_laplace q branch a w ht]
  apply Lp.ext
  have hall := ae_all_iff.mpr (fun i : Fin 3 => principalCutoffSpatialOp_laplace_ae q branch a i w
    ((principalResponseGrowth_lt_threshold q i).trans ht) hc)
  filter_upwards [Lp.coeFn_add (cuspMainLaplaceVector q branch a w hw₀)
      (∑ i : Fin 3, principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w)),
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w)),
    cuspMainLaplaceVector_ae q branch a w hw₀,hall,
    cuspResidualVector_ae q branch w a (onsetTransform (2*physicalRate q branch) w) hc]
      with p hAdd hSum hMain hCut hResidual
  rw [hAdd]
  simp only [Pi.add_apply]
  rw [hMain,hSum,hResidual]
  unfold cuspResidualForcing
  congr 1
  change (∑ i : Fin 3, principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) p) = _
  exact Finset.sum_congr rfl (fun i _ => hCut i)

/-- The physical source has both absolute Bochner convergence and exact original transform throughout one nonempty right half-plane. -/
theorem causalCuspSourceVector_original_transform (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalGreenThreshold q < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) (Ioi 0) ∧
      (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) =
        cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
          (principalChamber_of_threshold q w ((le_max_right _ _).trans_lt hw)) :=
  ⟨causalCuspSourceVector_laplace_integrable q branch a w ((le_max_left _ _).trans_lt hw),
    causalCuspSourceVector_laplace_original q branch a w hw⟩

end
end RHTower.D4BMJointSource
