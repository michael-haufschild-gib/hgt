import GaloisForLFunctions.HTGeometry.CycleTwistedTorsion
import GaloisForLFunctions.HTGeometry.DSSDeterminant

/-!
# Hasse gluing for a twisted cycle

Local transport equations around a finite cycle admit a nonzero global flat section exactly when
their single holonomy obstruction vanishes.  For nonzero edge weights, product-one holonomy is
therefore a complete local--global criterion rather than only a determinant identity.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- **Twisted-cycle Hasse principle.**  Local transport data glue to a nonzero global flat section
exactly when their product holonomy is one. -/
theorem cycle_nontrivial_global_flat_section_iff_holonomy_one
    {w u : CycleIndex n → ℂ} (hw : ∀ j, w j ≠ 0) :
    (∃ f : CycleIndex n → ℂ,
      f ≠ 0 ∧ (cycleDifferential n w u).mulVec f = 0) ↔ cycleHolonomy u = 1 :=
  (GaloisForLFunctions.matrix_nontrivial_kernel_iff_det_eq_zero
    (cycleDifferential n w u)).trans (det_cycleDifferential_eq_zero_iff hw)

/-- Failure of product-one reciprocity is exactly failure of global flat-section gluing. -/
theorem cycle_no_nontrivial_global_flat_section_iff_holonomy_ne_one
    {w u : CycleIndex n → ℂ} (hw : ∀ j, w j ≠ 0) :
    (¬ ∃ f : CycleIndex n → ℂ,
      f ≠ 0 ∧ (cycleDifferential n w u).mulVec f = 0) ↔ cycleHolonomy u ≠ 1 :=
  not_congr (cycle_nontrivial_global_flat_section_iff_holonomy_one hw)

/-- A globally glued nonzero flat section forces product-one reciprocity. -/
theorem cycleHolonomy_eq_one_of_nontrivial_global_flat_section
    {w u : CycleIndex n → ℂ} (hw : ∀ j, w j ≠ 0)
    {f : CycleIndex n → ℂ} (hf : f ≠ 0)
    (hflat : (cycleDifferential n w u).mulVec f = 0) :
    cycleHolonomy u = 1 :=
  (cycle_nontrivial_global_flat_section_iff_holonomy_one hw).mp ⟨f, hf, hflat⟩

/-- Product-one reciprocity produces a nonzero global flat section. -/
theorem exists_cycle_nontrivial_global_flat_section_of_holonomy_one
    {w u : CycleIndex n → ℂ} (hw : ∀ j, w j ≠ 0)
    (hu : cycleHolonomy u = 1) :
    ∃ f : CycleIndex n → ℂ,
      f ≠ 0 ∧ (cycleDifferential n w u).mulVec f = 0 :=
  (cycle_nontrivial_global_flat_section_iff_holonomy_one hw).mpr hu

end GaloisForLFunctions.HTGeometry
