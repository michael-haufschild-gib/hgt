import GaloisForLFunctions.HTGeometry.CompactProjectiveSeparationAtlas
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Topology of collision-free finite shift configurations

The space of ordered distinct complex shifts is the natural uncountable configuration space in
full-translation hypertranscendence.  For a finite label type it is an open subset of the
finite-dimensional complex packet space: injectivity is the finite intersection of the open
inequalities `shift i ≠ shift j`.  Hence it is locally compact, second countable, and
sigma-compact.

The sigma-compact conclusion supplies the countable compact exhaustion required by
`CompactConfigurationBaire`; no countable discretization of the actual shifts is used.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-- The collision-free locus inside the ambient finite complex packet space. -/
def injectiveShiftConfigurationSet (ι : Type*) [Fintype ι] : Set (ι → ℂ) :=
  {shift | Function.Injective shift}

/-- Finite collision-free complex shift configurations form an open set. -/
theorem injectiveShiftConfigurationSet_isOpen
    (ι : Type*) [Fintype ι] :
    IsOpen (injectiveShiftConfigurationSet ι) := by
  classical
  rw [show injectiveShiftConfigurationSet ι =
      ⋂ i : ι, ⋂ j : ι, ⋂ (_h : i ≠ j), {shift : ι → ℂ | shift i ≠ shift j} by
    ext shift
    simp only [injectiveShiftConfigurationSet, mem_setOf_eq, mem_iInter]
    constructor
    · intro hinj i j hij
      exact fun heq ↦ hij (hinj heq)
    · intro hpairs i j heq
      by_contra hij
      exact hpairs i j hij heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  have hcont : Continuous (fun shift : ι → ℂ ↦ shift i - shift j) :=
    (continuous_apply i).sub (continuous_apply j)
  have hopen := hcont.isOpen_preimage {z : ℂ | z ≠ 0} isOpen_ne
  convert hopen using 1
  ext shift
  simp only [mem_preimage, mem_setOf_eq, sub_ne_zero]

/-- The collision-free shift configuration type is sigma-compact.  Its compact exhaustion is
therefore available noncomputably from `SigmaCompactSpace.exists_compact_covering`. -/
noncomputable instance injectiveShiftConfigurationSigmaCompactSpace
    (ι : Type*) [Fintype ι] :
    SigmaCompactSpace (InjectiveShiftConfiguration ι) := by
  letI : LocallyCompactSpace (InjectiveShiftConfiguration ι) :=
    (injectiveShiftConfigurationSet_isOpen ι).locallyCompactSpace
  infer_instance

end

end GaloisForLFunctions.HTGeometry
