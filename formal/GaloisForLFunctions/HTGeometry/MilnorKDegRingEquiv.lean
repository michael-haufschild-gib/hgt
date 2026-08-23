/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality

/-!
# Transport of graded Milnor `K`-theory across field equivalences

A field equivalence carries every Milnor symbol to the corresponding symbol and its inverse does
the reverse.  Therefore it induces an additive equivalence on every graded Milnor `K` group.
This is the reusable transport needed for residue-field comparisons under completion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A field equivalence induces an additive equivalence on the degree-`n` Milnor `K` group. -/
noncomputable def milnorKDegAddEquivOfRingEquiv
    {A B : Type*} [Field A] [Field B] (e : A ≃+* B) (n : ℕ) :
    MilnorKDeg A n ≃+ MilnorKDeg B n where
  toFun := milnorKDegMap (e : A →+* B) n
  invFun := milnorKDegMap (e.symm : B →+* A) n
  left_inv x := by
    have hcomp : (milnorKDegMap (e.symm : B →+* A) n).comp
        (milnorKDegMap (e : A →+* B) n) = AddMonoidHom.id (MilnorKDeg A n) := by
      apply milnorKDeg_hom_ext A
      intro s
      rw [AddMonoidHom.comp_apply, milnorKDegMap_class, milnorKDegMap_class]
      refine congrArg (milnorClassDeg A n) (Subtype.ext ?_)
      rw [milnorSymbolDegMap_val, milnorSymbolDegMap_val, List.map_map]
      refine (List.map_congr_left fun a _ => ?_).trans (List.map_id _)
      exact Units.ext (by simp)
    exact DFunLike.congr_fun hcomp x
  right_inv y := by
    have hcomp : (milnorKDegMap (e : A →+* B) n).comp
        (milnorKDegMap (e.symm : B →+* A) n) = AddMonoidHom.id (MilnorKDeg B n) := by
      apply milnorKDeg_hom_ext B
      intro s
      rw [AddMonoidHom.comp_apply, milnorKDegMap_class, milnorKDegMap_class]
      refine congrArg (milnorClassDeg B n) (Subtype.ext ?_)
      rw [milnorSymbolDegMap_val, milnorSymbolDegMap_val, List.map_map]
      refine (List.map_congr_left fun a _ => ?_).trans (List.map_id _)
      exact Units.ext (by simp)
    exact DFunLike.congr_fun hcomp y
  map_add' := (milnorKDegMap (e : A →+* B) n).map_add

/-- The forward map of the transported equivalence is the usual Milnor functoriality map. -/
theorem milnorKDegAddEquivOfRingEquiv_apply
    {A B : Type*} [Field A] [Field B] (e : A ≃+* B) (n : ℕ) (x : MilnorKDeg A n) :
    milnorKDegAddEquivOfRingEquiv e n x = milnorKDegMap (e : A →+* B) n x := rfl

end

end GaloisForLFunctions.HTGeometry
