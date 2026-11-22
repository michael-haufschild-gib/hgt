import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothStalkDomains
import Mathlib.AlgebraicGeometry.Properties

/-! A quasi-compact smooth scheme over a field splits into integral clopen components. -/

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

namespace UpperTheory.Cb

universe u

private theorem irreducibleComponent_eq_stalk_generic_closure
    (Z : Scheme) (x : Z) [IsDomain (Z.presheaf.stalk x)]
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) (hx : x ∈ C) :
    C = closure {Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))} := by
  let ξ := Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))
  have hgen : IsGenericPoint hC.1.genericPoint C := by
    simpa only [(isClosed_of_mem_irreducibleComponents C hC).closure_eq] using
      hC.1.isGenericPoint_genericPoint_closure
  obtain ⟨p, hp⟩ : hC.1.genericPoint ∈ Set.range (Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hgen.specializes hx
  have hξη : ξ ⤳ hC.1.genericPoint := by
    rw [← hp]
    exact ((genericPoint_spec (Spec (Z.presheaf.stalk x))).specializes trivial).map
      (Z.fromSpecStalk x).continuous
  have hsub : C ⊆ closure {ξ} := by
    rw [← hgen.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hξη) isClosed_closure
  exact le_antisymm hsub (hC.2 isIrreducible_singleton.closure hsub)

/-- The finitely many irreducible components of a quasi-compact smooth scheme over a
field are disjoint open subschemes and carry their integral scheme structures. -/
theorem exists_integral_clopen_decomposition_of_smooth {k : Type u} [Field k]
    (Z : Scheme.{u}) (s : Z ⟶ Spec (.of k)) [Smooth s] [CompactSpace Z] :
    ∃ (J : Type u) (_ : Fintype J) (V : J → Z.Opens),
      (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  have hdom (x : Z) := isDomain_stalk_of_smooth_over_field s x
  haveI : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x => by
    haveI := hdom x
    infer_instance
  haveI : AlgebraicGeometry.IsReduced Z := isReduced_of_isReduced_stalk Z
  haveI : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian s }
  have hfin : (irreducibleComponents Z).Finite := finite_irreducibleComponents_of_isNoetherian
  have disj (C D : Set Z) (hC : C ∈ irreducibleComponents Z)
      (hD : D ∈ irreducibleComponents Z) (hne : C ≠ D) : Disjoint C D := by
    rw [Set.disjoint_left]
    intro x hxC hxD
    haveI := hdom x
    exact hne ((irreducibleComponent_eq_stalk_generic_closure Z x hC hxC).trans
      (irreducibleComponent_eq_stalk_generic_closure Z x hD hxD).symm)
  have cover (x : Z) : ∃ C ∈ irreducibleComponents Z, x ∈ C :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      mem_irreducibleComponent⟩
  have hopen (C : Set Z) (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
    have hc : Cᶜ = ⋃ D ∈ irreducibleComponents Z \ {C}, D := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro hx
        obtain ⟨D, hD, hxD⟩ := cover x
        exact ⟨D, ⟨hD, fun h => hx (h ▸ hxD)⟩, hxD⟩
      · rintro ⟨D, ⟨hD, hne⟩, hxD⟩ hxC
        exact Set.disjoint_left.mp (disj D C hD hC hne) hxD hxC
    rw [← isClosed_compl_iff, hc]
    exact (hfin.subset Set.sdiff_subset).isClosed_biUnion fun D hD =>
      isClosed_of_mem_irreducibleComponents D hD.1
  letI : Fintype (irreducibleComponents Z) := hfin.fintype
  refine ⟨irreducibleComponents Z, inferInstance, fun C => ⟨C.1, hopen C.1 C.2⟩, ?_, ?_, ?_⟩
  · intro i j hij
    apply Opens.ext
    simp only [Opens.coe_inf, Opens.coe_bot]
    exact Set.disjoint_iff_inter_eq_empty.mp (disj i.1 j.1 i.2 j.2 (fun h => hij (Subtype.ext h)))
  · refine eq_top_iff.mpr fun x _ => ?_
    rw [Opens.mem_iSup]
    obtain ⟨C, hC, hxC⟩ := cover x
    exact ⟨⟨C, hC⟩, hxC⟩
  · intro C
    let U : Z.Opens := ⟨C.1, hopen C.1 C.2⟩
    change IsIntegral U.toScheme
    haveI : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace C.2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _

end UpperTheory.Cb
