import GaloisForLFunctions.HTGeometry.MilnorBassTateDegreeDrop
import Mathlib.FieldTheory.PrimitiveElement

/-!
# The degree drop for a finite separable extension

A finite separable extension is simple, so Bass and Tate's degree drop applies to it: if the Milnor
`K`-theory of the base is torsion from degree `n₀` on, then that of the extension is torsion from
degree `n₀ + [E : F] − 1` on.

* `milnorKDeg_torsion_transfer` : torsion transports along a field isomorphism.
* `milnorKDeg_torsion_of_finite_separable` : **the degree drop for a finite separable extension.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- **Torsion of Milnor `K`-theory transports along a field isomorphism.** -/
theorem milnorKDeg_torsion_transfer {A B : Type*} [Field A] [Field B] (e : A ≃+* B) (m : ℕ)
    (h : ∀ x : MilnorKDeg A m, x ∈ torsionAddSubgroup (MilnorKDeg A m))
    (y : MilnorKDeg B m) : y ∈ torsionAddSubgroup (MilnorKDeg B m) := by
  refine milnorKDeg_mem_of_gen _ (fun s => ?_) y
  have hlen : (s.val.map (milnorUnitMap (e.symm : B →+* A))).length = m := by
    rw [List.length_map]; exact s.property
  have hback : milnorKDegMap (e : A →+* B) m
      (milnorClassDeg A m ⟨s.val.map (milnorUnitMap (e.symm : B →+* A)), hlen⟩)
      = milnorClassDeg B m s := by
    rw [milnorKDegMap_class]
    refine congrArg (milnorClassDeg B m) (Subtype.ext ?_)
    rw [milnorSymbolDegMap_val, List.map_map]
    refine (List.map_congr_left fun a _ => ?_).trans (List.map_id _)
    exact Units.ext (by simp)
  rw [← hback]
  exact milnorKDegMap_mem_torsion _ m (h _)

/-- **Bass and Tate's degree drop for a finite separable extension.** -/
theorem milnorKDeg_torsion_of_finite_separable {E : Type*} [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] {n₀ : ℕ}
    (hF : ∀ j, n₀ ≤ j → ∀ x : MilnorKDeg F j, x ∈ torsionAddSubgroup (MilnorKDeg F j))
    (m : ℕ) (hm : n₀ + (Module.finrank F E - 1) ≤ m) (y : MilnorKDeg E m) :
    y ∈ torsionAddSubgroup (MilnorKDeg E m) := by
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  set π : Polynomial F := minpoly F α with hπdef
  have hπ : Irreducible π := minpoly.irreducible hint
  have hmπ : π.Monic := minpoly.monic hint
  have hdeg : π.natDegree = Module.finrank F E := by
    rw [hπdef, ← IntermediateField.adjoin.finrank hint, hα]
    exact (IntermediateField.topEquiv (F := F) (E := E)).toLinearEquiv.finrank_eq
  have hd : 1 ≤ π.natDegree := by
    rw [hdeg]
    exact Module.finrank_pos
  -- `E` is the residue field at `π`
  have hquot : (Polynomial F ⧸ (polyPlace hπ).asIdeal) ≃+* E :=
    ((RingEquiv.refl (AdjoinRoot π)).trans
      ((IntermediateField.adjoinRootEquivAdjoin F hint).toRingEquiv.trans
        (((IntermediateField.equivOfEq hα).trans
          (IntermediateField.topEquiv (F := F) (E := E))).toRingEquiv)))
  have hres : polyResidueField hπ ≃+* E :=
    (residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ)).trans hquot
  refine milnorKDeg_torsion_transfer hres m (fun x => ?_) y
  exact milnorKDeg_torsion_of_bassTate hπ hmπ hd hF m (by rw [hdeg]; exact hm) x

end GaloisForLFunctions.HTGeometry
