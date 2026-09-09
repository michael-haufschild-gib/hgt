import GaloisForLFunctions.RHTower.SelbergScatteringCuspSubtraction
import GaloisForLFunctions.RHTower.SelbergScatteringEntireXiPackets

/-!
# A full-source vector in the actual entire-operator domain

The original physical Xi field, after the proved modular cusp subtraction, is
admitted and nonzero in the native Hilbert space. Applying the constructed
injective entire covariance gives an explicit nonzero domain vector and its
exact unit normalization. Its transformed equation retains the complete
full-Xi residual. No vanishing or spectral occurrence is assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.SelbergScatteringSourceVector
open D4BMModularCore SelbergScatteringCuspSubtraction
open SelbergScatteringEntireOperator SelbergScatteringEntireXiPackets
noncomputable section

/-- The full cusp-subtracted original Xi field is admitted in the original modular Hilbert space. -/
theorem globalResidual_memLp (q : XiZeroCopy) : MemLp (globalResidual q) 2 measure := by
  obtain ⟨C,_,hb⟩ := globalResidual_bounded q
  exact MemLp.of_bound (globalResidual_smooth q).continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall hb)

/-- A concrete original-source vector retaining the entire complex Xi parameter. -/
def sourceVector (q : XiZeroCopy) : Space := (globalResidual_memLp q).toLp (globalResidual q)

/-- Its native Hilbert representative is the full modular correction almost everywhere. -/
theorem sourceVector_coe (q : XiZeroCopy) :
    (sourceVector q : UpperHalfPlane → ℂ) =ᵐ[measure] globalResidual q :=
  (globalResidual_memLp q).coeFn_toLp

/-- The original source supplies nonvanishing in the native Hilbert space, without an occurrence premise. -/
theorem sourceVector_ne_zero (q : XiZeroCopy) : sourceVector q ≠ 0 := by
  intro h
  have hz : (sourceVector q : UpperHalfPlane → ℂ) =ᵐ[measure] (fun _ => (0:ℂ)) := by
    rw [h]
    exact Lp.coeFn_zero ℂ 2 measure
  have hg := (sourceVector_coe q).symm.trans hz
  change globalResidual q =ᵐ[volume.restrict fd] (fun _ => (0:ℂ)) at hg
  have hclosure : fd ⊆ closure (interior fd) := by
    rw [← fdo_eq_interior_fd,← fd_eq_closure_fdo]
  have he := Measure.eqOn_of_ae_eq hg (globalResidual_smooth q).continuous.continuousOn
    continuousOn_const hclosure
  obtain ⟨z,hz,hn⟩ := globalResidual_nonzero_on_fd q
  exact hn (he hz)

/-- The injective entire covariance preserves the full original source. -/
theorem sourceCovariance_norm_pos (q : XiZeroCopy) : 0 < ‖entireCovariance (sourceVector q)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  exact sourceVector_ne_zero q (entireCovariance_injective (by simpa only [map_zero] using hz))

/-- Actual entire-operator domain vector produced from the complete modular source. -/
def sourceDomainVector (q : XiZeroCopy) : entireOperator.domain :=
  ⟨entireCovariance (sourceVector q),entireCovariance_mem_domain (sourceVector q)⟩

theorem sourceDomainVector_ne_zero (q : XiZeroCopy) : (sourceDomainVector q : Space) ≠ 0 :=
  (norm_pos_iff.mp (sourceCovariance_norm_pos q))

/-- Exact native normalization of that source-derived domain vector. -/
def sourceUnitVector (q : XiZeroCopy) : entireOperator.domain :=
  ((‖entireCovariance (sourceVector q)‖⁻¹:ℝ):ℂ) • sourceDomainVector q

theorem sourceUnitVector_norm (q : XiZeroCopy) : ‖(sourceUnitVector q : Space)‖ = 1 := by
  rw [sourceUnitVector,Submodule.coe_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sourceCovariance_norm_pos q))]
  exact inv_mul_cancel₀ (sourceCovariance_norm_pos q).ne'

/-- The full original Xi target remains in the forcing numerator after domain admission. -/
def sourceResidual (q : XiZeroCopy) : Space :=
  sourceVector q - (2+xiEntireTarget q) • entireCovariance (sourceVector q)

/-- Exact transformed equation of the actual domain vector; no zero residual is assumed. -/
theorem sourceDomainVector_equation (q : XiZeroCopy) :
    entireOperator (sourceDomainVector q) - xiEntireTarget q • (sourceDomainVector q : Space) =
      sourceResidual q := by
  rw [sourceDomainVector,entireOperator_apply_covariance]
  change sourceVector q - (2:ℂ) • entireCovariance (sourceVector q) -
    xiEntireTarget q • entireCovariance (sourceVector q) = _
  rw [sourceResidual,add_smul]
  module

/-- Normalization retains the exact full-parameter residual and its positive source norm denominator. -/
theorem sourceUnitVector_residual_norm (q : XiZeroCopy) :
    ‖entireOperator (sourceUnitVector q) - xiEntireTarget q • (sourceUnitVector q : Space)‖ =
      ‖entireCovariance (sourceVector q)‖⁻¹ * ‖sourceResidual q‖ := by
  rw [sourceUnitVector,entireOperator.map_smul,Submodule.coe_smul,
    smul_comm (xiEntireTarget q),← smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sourceCovariance_norm_pos q)),sourceDomainVector_equation]

end
end RHTower.SelbergScatteringSourceVector
