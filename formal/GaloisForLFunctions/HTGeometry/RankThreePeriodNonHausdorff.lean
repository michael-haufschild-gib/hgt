import GaloisForLFunctions.HTGeometry.RankThreePeriods
import Mathlib.LinearAlgebra.Countable
import Mathlib.Topology.Baire.Lemmas

/-!
# The non-Hausdorff rank-three period horizon

A countable closed subgroup of the complex plane is a complete Baire space.  Its decomposition
into singleton closed sets forces one singleton to have interior, hence forces the subgroup to be
discrete.  The integer span of three `ℚ`-linearly independent complex periods is already known to
be nondiscrete, so it cannot be closed.  Consequently its topological quotient is not Hausdorff.
-/

namespace GaloisForLFunctions

open scoped Topology

/-- A countable closed integer submodule of the complex plane is discrete. -/
theorem discrete_of_countable_isClosed_intSubmodule
    (L : Submodule ℤ ℂ) [Countable L] (hL : IsClosed (L : Set ℂ)) :
    DiscreteTopology L := by
  letI : IsClosed (L : Set ℂ) := hL
  letI : CompleteSpace L := inferInstance
  obtain ⟨x, hx⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun x : L => ({x} : Set L)) (fun _ => isClosed_singleton)
    (by ext y; simp)
  have hopenx : IsOpen ({x} : Set L) := by
    have hxin : x ∈ interior ({x} : Set L) := by
      obtain ⟨y, hy⟩ := hx
      have hyx : y = x := Set.mem_singleton_iff.mp (interior_subset hy)
      simpa [hyx] using hy
    have heq : interior ({x} : Set L) = {x} := by
      apply Set.Subset.antisymm interior_subset
      simpa only [Set.singleton_subset_iff]
    rw [← heq]
    exact isOpen_interior
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have htranslate : Continuous (fun y : L => x + y) := continuous_const.add continuous_id
  simpa using hopenx.preimage htranslate

/-- The integer span of three `ℚ`-linearly independent complex periods is not closed. -/
theorem not_isClosed_intSpan_fin_three (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    ¬ IsClosed (Submodule.span ℤ (Set.range v) : Set ℂ) := by
  intro hclosed
  exact not_discrete_intSpan_fin_three v hv
    (discrete_of_countable_isClosed_intSubmodule _ hclosed)

/-- The quotient of the complex plane by three `ℚ`-linearly independent periods is not
Hausdorff. -/
theorem not_t2Space_quotient_intSpan_fin_three (v : Fin 3 → ℂ)
    (hv : LinearIndependent ℚ v) :
    ¬ T2Space (ℂ ⧸ Submodule.span ℤ (Set.range v)) := by
  intro hT2
  letI : T2Space (ℂ ⧸ Submodule.span ℤ (Set.range v)) := hT2
  let L : Submodule ℤ ℂ := Submodule.span ℤ (Set.range v)
  have hpre : IsClosed (L.mkQ ⁻¹' ({0} : Set (ℂ ⧸ L))) :=
    isClosed_singleton.preimage L.continuous_mkQ
  have heq : L.mkQ ⁻¹' ({0} : Set (ℂ ⧸ L)) = (L : Set ℂ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hclosed : IsClosed (L : Set ℂ) := by
    rw [← heq]
    exact hpre
  exact not_isClosed_intSpan_fin_three v hv hclosed

/-- An integer span contained in a real lattice of the complex plane is closed.  The explicit
lattice-containment hypothesis is essential: abstract rational rank two does not exclude an
irrationally generated dense subgroup of a real line. -/
theorem isClosed_intSpan_of_subset_realBasis
    {ι : Type*} (v : ι → ℂ) (b : Module.Basis (Fin 2) ℝ ℂ)
    (hv : Set.range v ⊆ (Submodule.span ℤ (Set.range b) : Set ℂ)) :
    IsClosed (Submodule.span ℤ (Set.range v) : Set ℂ) := by
  let H : Submodule ℤ ℂ := Submodule.span ℤ (Set.range v)
  let L : Submodule ℤ ℂ := Submodule.span ℤ (Set.range b)
  have hHL : H ≤ L := Submodule.span_le.mpr hv
  let inclusion : H → L := fun x => ⟨x, hHL x.2⟩
  have hcontinuous : Continuous inclusion := continuous_subtype_val.subtype_mk _
  have hinjective : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : L => (z : ℂ)) hxy
  letI : DiscreteTopology L := inferInstance
  letI : DiscreteTopology H :=
    DiscreteTopology.of_continuous_injective hcontinuous hinjective
  change IsClosed (H.toAddSubgroup : Set ℂ)
  exact H.toAddSubgroup.isClosed_of_discrete

/-- The quotient by an integer span contained in a real lattice is Hausdorff. -/
theorem t2Space_quotient_intSpan_of_subset_realBasis
    {ι : Type*} (v : ι → ℂ) (b : Module.Basis (Fin 2) ℝ ℂ)
    (hv : Set.range v ⊆ (Submodule.span ℤ (Set.range b) : Set ℂ)) :
    T2Space (ℂ ⧸ Submodule.span ℤ (Set.range v)) := by
  letI : IsClosed (Submodule.span ℤ (Set.range v) : Set ℂ) :=
    isClosed_intSpan_of_subset_realBasis v b hv
  infer_instance

end GaloisForLFunctions
