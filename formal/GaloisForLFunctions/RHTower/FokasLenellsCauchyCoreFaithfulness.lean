import GaloisForLFunctions.HTGeometry.FokasLenellsHardyGapUniqueness
import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexFaithfulness
import GaloisForLFunctions.RHTower.FokasLenellsRawComplexCauchyCore

/-!
# Cauchy faithfulness on the common entire core

The full Cauchy projection has an infinite-dimensional Hardy kernel, but an
actual core vector has a spectral gap. Hardy boundary uniqueness removes
that kernel on the core. All raw complex-time derivatives retain the core
and are faithful, so their actual Cauchy compression is faithful as well.
-/

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual common entire core meets the full upper Hardy kernel only at zero. -/
theorem rawComplexEntireCore_mem_hardy_iff_zero (u : rawComplexEntireCore) :
    u.val ∈ hardyL2 ↔ u = 0 := by
  constructor
  · intro hu
    obtain ⟨a,ha⟩ := rawComplexEntireCore_exists_zeroGap u
    let v : UpperHardyL2 := ⟨u.val,hu⟩
    have hv : v = 0 := (upperHardyL2_gap_zero_iff v 0 a).1 ha
    apply Subtype.ext
    exact congrArg (fun v : UpperHardyL2 => v.val) hv
  · rintro rfl
    exact Submodule.zero_mem _

/-- The actual Cauchy projection has no nonzero kernel vector in the common entire core. -/
theorem negativeCauchy_core_eq_zero_iff (u : rawComplexEntireCore) :
    negativeCauchy u.val = 0 ↔ u = 0 := by
  rw [negativeCauchy_eq_zero_iff,rawComplexEntireCore_mem_hardy_iff_zero]

/-- Cauchy boundary data determine an actual common-core input uniquely. -/
theorem negativeCauchy_core_injective :
    Function.Injective (fun u : rawComplexEntireCore => negativeCauchy u.val) := by
  intro u v h
  change negativeCauchy u.val = negativeCauchy v.val at h
  apply sub_eq_zero.mp
  apply (negativeCauchy_core_eq_zero_iff (u-v)).1
  change negativeCauchy (u.val-v.val) = 0
  rw [map_sub,h,sub_self]

/-- Every actual Cauchy-compressed raw derivative and complex-time action is injective on the core. -/
theorem rawComplexCauchyCoreHierarchy_injective (n : ℕ) (τ : ℂ) :
    Function.Injective (rawComplexCauchyCoreHierarchy n τ) := by
  intro u v h
  apply rawComplexCoreHierarchy_injective n τ
  apply negativeCauchy_core_injective
  exact h

/-- No derivative order or complex time creates a Cauchy kernel on the common entire core. -/
theorem rawComplexCauchyCoreHierarchy_eq_zero_iff (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    rawComplexCauchyCoreHierarchy n τ u = 0 ↔ u = 0 := by
  rw [← map_zero (rawComplexCauchyCoreHierarchy n τ),
    (rawComplexCauchyCoreHierarchy_injective n τ).eq_iff]

end
end RHTower.FokasLenells
