import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalWeightedAngularData

/-! A continuous realization of the original bilinear physical source integral. -/
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The conjugated, inverse-height physical field in the original angular Hilbert space. -/
def physicalDualVector (q : XiZeroCopy) : D4BMModularCore.Space :=
  (physicalDualDensity_memLp q).star.toLp (star (physicalDualDensity q))

theorem physicalDualVector_coe (q : XiZeroCopy) :
    physicalDualVector q =ᵐ[D4BMModularCore.measure] fun z => conj (physicalDualDensity q z) :=
  (physicalDualDensity_memLp q).star.coeFn_toLp

/-- The physical bilinear source pairing acts continuously on height-weighted source representatives. -/
def physicalAngularFunctional (q : XiZeroCopy) : D4BMModularCore.Space →L[ℂ] ℂ :=
  innerSL ℂ (physicalDualVector q)

/-- The constructed functional integrates the actual full physical field, with the original measure. -/
theorem physicalAngularFunctional_integral (q : XiZeroCopy) (f : D4BMModularCore.Space) :
    physicalAngularFunctional q f =
      ∫ z : UpperHalfPlane, physicalDualDensity q z * f z ∂D4BMModularCore.measure := by
  change inner ℂ (physicalDualVector q) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [physicalDualVector_coe q] with z hz
  rw [hz]
  simp [RCLike.inner_apply,mul_comm]

/-- A norm bound for the actual physical testing functional in its weighted source topology. -/
theorem physicalAngularFunctional_bound (q : XiZeroCopy) (f : D4BMModularCore.Space) :
    ‖physicalAngularFunctional q f‖ ≤ ‖physicalDualVector q‖ * ‖f‖ := by
  change ‖inner ℂ (physicalDualVector q) f‖ ≤ _
  exact norm_inner_le_norm _ _

/-- The full original residual multiplied by one height, as an admitted source representative. -/
def weightedResidualVector (q : XiZeroCopy) : D4BMModularCore.Space :=
  (weightedSquareResidual_memLp q 1).toLp
    (fun z : UpperHalfPlane => (z.im:ℂ)^1 * squareResidual q (coordinates z))

theorem weightedResidualVector_coe (q : XiZeroCopy) :
    weightedResidualVector q =ᵐ[D4BMModularCore.measure]
      fun z : UpperHalfPlane => (z.im:ℂ) * squareResidual q (coordinates z) := by
  simpa only [weightedResidualVector,Complex.cpow_one] using
    (weightedSquareResidual_memLp q 1).coeFn_toLp

/-- Each complete differential cutoff multiplied by one height, without changing its coefficients. -/
def weightedCutoffVector (k : ℂ) : D4BMModularCore.Space :=
  (weightedCutoffCommutator_memLp 1 k).toLp
    (fun z : UpperHalfPlane => (z.im:ℂ)^1 * cutoffCommutator k (coordinates z))

theorem weightedCutoffVector_coe (k : ℂ) :
    weightedCutoffVector k =ᵐ[D4BMModularCore.measure]
      fun z : UpperHalfPlane => (z.im:ℂ) * cutoffCommutator k (coordinates z) := by
  simpa only [weightedCutoffVector,Complex.cpow_one] using
    (weightedCutoffCommutator_memLp 1 k).coeFn_toLp

/-- The continuous functional recovers the original native period for every source and physical target. -/
theorem physicalAngularFunctional_native (q r : XiZeroCopy) :
    physicalAngularFunctional q (weightedResidualVector r) =
      scalarResidualPeriod r (physicalAngularParameter q) := by
  rw [physicalAngularFunctional_integral,scalarResidualPeriod]
  apply integral_congr_ae
  filter_upwards [weightedResidualVector_coe r] with z hz
  rw [hz]
  dsimp [physicalDualDensity]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne']

/-- The same functional retains the actual boundary and bulk value of each differential cutoff. -/
theorem physicalAngularFunctional_cutoff (q : XiZeroCopy) (k : ℂ) :
    physicalAngularFunctional q (weightedCutoffVector k) =
      scalarCutoffBoundaryValue (physicalAngularParameter q) k := by
  rw [← scalarCutoffPeriod_eq_boundary_value,physicalAngularFunctional_integral,scalarCutoffPeriod]
  apply integral_congr_ae
  filter_upwards [weightedCutoffVector_coe k] with z hz
  rw [hz]
  dsimp [physicalDualDensity]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne']

end
end RHTower.D4BMJointSource
