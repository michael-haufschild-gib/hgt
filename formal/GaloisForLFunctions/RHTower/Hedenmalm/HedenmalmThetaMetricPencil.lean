import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPinnedBoundaryTwoPort
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceCompressedInverseDeterminant

/-!
# Source-faithful singular theta metric pencil

The literal theta source pencil is `I + zB`.  Its canonical metric `G` is injective but not
bounded below, so left multiplication creates a genuinely singular generalized pencil rather than
a bounded similarity.  This file proves the fact needed for source fidelity: its nonzero kernel
divisor remains exactly the completed Xi divisor.  Together with the exact two-port Green defect,
this is the concrete interface for a closed-relation/index-one capacity theorem.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmThetaSource HedenmalmHilbertSchmidt

/-- Singular metric realization of the literal theta source pencil. -/
def thetaMetricSourcePencil (z : ℂ) :=
  thetaMetricOperator * thetaSourcePencil z

/-- The theta metric does not collapse any source vector. -/
theorem thetaMetricOperator_injective :
    Function.Injective thetaMetricOperator := by
  rw [thetaMetricOperator]
  exact metricOperator_injective thetaSource thetaMetricBound_nonneg
    norm_metricSymbol_thetaSource_le

/-- Left multiplication by the singular metric preserves every source-pencil kernel exactly. -/
theorem thetaMetricSourcePencil_apply_eq_zero_iff (z : ℂ) (f : H) :
    thetaMetricSourcePencil z f = 0 ↔ thetaSourcePencil z f = 0 := by
  constructor
  · intro h
    apply thetaMetricOperator_injective
    simpa [thetaMetricSourcePencil] using h
  · intro h
    simp [thetaMetricSourcePencil, h]

/-- The singular metric pencil has exactly the literal completed-Xi zero set as its nonzero
kernel divisor. -/
theorem XiC_eq_zero_iff_exists_thetaMetricSourcePencil_kernel (z : ℂ) :
    XiC z = 0 ↔ ∃ f : H, f ≠ 0 ∧ thetaMetricSourcePencil z f = 0 := by
  constructor
  · intro hXi
    have hz : z ≠ 0 := fun hz => XiC_zero_ne (hz ▸ hXi)
    obtain ⟨_, f, hf0, hf⟩ :=
      (XiC_eq_zero_iff_sourcePencil_not_isUnit_iff_eigenvector z).mp hXi
    refine ⟨f, hf0, (thetaMetricSourcePencil_apply_eq_zero_iff z f).mpr ?_⟩
    rw [thetaSourcePencil, add_apply, one_apply_eq_self, smul_apply, hf, smul_smul]
    field_simp [hz]
    simp
  · rintro ⟨f, hf0, hzero⟩
    apply (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).mp
    intro hunit
    apply hf0
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    have hsource := (thetaMetricSourcePencil_apply_eq_zero_iff z f).mp hzero
    simpa using hsource

/-- The literal theta metric Green defect factors through exactly one incoming and one outgoing
scalar port. -/
theorem thetaMetric_commutator_thetaKernelOperator_eq_twoPort :
    thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator =
      Complex.I • (pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
        pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) := by
  rw [thetaMetric_commutator_thetaKernelOperator,
    pinnedBoundaryCLM_eq_port_difference]

end

end RHTower
