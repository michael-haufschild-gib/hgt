import GaloisForLFunctions.HTGeometry.BuildingVanishingSubmodule

/-!
# Solomon--Tits vanishing for the horizon complex

The horizon complex of the parent theorem is the order complex of the common-horizon fields, which
is the order complex of the proper nonzero subspaces **with the order reversed** — the assignment
`S ↦ I_S` is order-reversing.  So the vanishing theorem has to be read on the dual lattice.

That costs nothing: the dual of a bounded modular lattice is one, the proper part of the dual is
the dual of the proper part, and for subspaces the dual rank is the codimension, whose covering
increments are the same.  Atoms of the dual are coatoms — hyperplanes — and every proper subspace
lies in one.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

variable {L : Type u} [Lattice L] [BoundedOrder L]

/-- The proper part, in the `≠ ⊥ ∧ ≠ ⊤` presentation used by the horizon work. -/
def properPartNeOrderIso : properPart L ≃o {S : L // S ≠ ⊥ ∧ S ≠ ⊤} where
  toFun x := ⟨(x : L), ne_of_gt x.2.1, ne_of_lt x.2.2⟩
  invFun y := ⟨(y : L), lt_of_le_of_ne bot_le (Ne.symm y.2.1), lt_of_le_of_ne le_top y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **The proper part of the dual lattice is the dual of the proper part.** -/
def properPartDualOrderIso : properPart Lᵒᵈ ≃o (properPart L)ᵒᵈ where
  toFun x := OrderDual.toDual ⟨OrderDual.ofDual (x : Lᵒᵈ), x.2.2, x.2.1⟩
  invFun y := ⟨OrderDual.toDual ((OrderDual.ofDual y : properPart L) : L),
    (OrderDual.ofDual y : properPart L).2.2, (OrderDual.ofDual y : properPart L).2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

section

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **Solomon--Tits vanishing on the dual lattice of subspaces**, which is the order in which the
horizon complex presents it. -/
theorem isZero_homology_properPart_submodule_dual [Nontrivial V] (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hrank : i + 3 ≤ finrank K V) :
    Limits.IsZero ((nerve (properPart (Submodule K V)ᵒᵈ)).homology R i) := by
  refine isZero_homology_properPart_of_rank
    (fun U : (Submodule K V)ᵒᵈ => finrank K V - finrank K (OrderDual.ofDual U : Submodule K V))
    ?_ ?_ ?_ R i hi ?_ ?_
  · show finrank K V - finrank K (⊤ : Submodule K V) = 0
    rw [finrank_top]
    omega
  · intro U W h
    show finrank K V - finrank K (OrderDual.ofDual W : Submodule K V)
      = (finrank K V - finrank K (OrderDual.ofDual U : Submodule K V)) + 1
    have hcov : (OrderDual.ofDual W : Submodule K V) ⋖ (OrderDual.ofDual U : Submodule K V) :=
      ofDual_covBy_ofDual_iff.2 h
    have hstep : finrank K (OrderDual.ofDual U : Submodule K V)
        = finrank K (OrderDual.ofDual W : Submodule K V) + 1 := finrank_of_covBy hcov
    have hle : finrank K (OrderDual.ofDual U : Submodule K V) ≤ finrank K V := by
      rw [← finrank_top (R := K) (M := V)]
      exact Submodule.finrank_mono le_top
    omega
  · intro U hU
    obtain ⟨H, hH, hUH⟩ :=
      (eq_top_or_exists_le_coatom (OrderDual.ofDual U : Submodule K V)).resolve_left
        (ne_of_lt hU)
    exact ⟨OrderDual.toDual H, hH.dual, hUH⟩
  · exact bot_lt_top
  · show i + 3 ≤ finrank K V - finrank K (⊥ : Submodule K V)
    rw [finrank_bot]
    omega

/-- **The same, on the order complex as the horizon picture presents it**: the proper nonzero
subspaces, with the order reversed. -/
theorem isZero_homology_properPart_submodule_orderDual [Nontrivial V] (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hrank : i + 3 ≤ finrank K V) :
    Limits.IsZero ((nerve ((properPart (Submodule K V))ᵒᵈ)).homology R i) :=
  Limits.IsZero.of_iso (isZero_homology_properPart_submodule_dual R i hi hrank)
    ((SSet.homologyFunctor R i).mapIso
      (orderIsoNerveIso (properPartDualOrderIso (L := Submodule K V))).symm)

end

end GaloisForLFunctions.HTGeometry
