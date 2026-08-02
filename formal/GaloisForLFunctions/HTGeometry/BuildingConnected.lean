import GaloisForLFunctions.HTGeometry.BuildingFreeSubmodule
import GaloisForLFunctions.HTGeometry.NerveHomotopy

/-!
# The building of a vector space is connected

Two nonzero proper subspaces of a space of dimension at least three are joined by a chain of
inclusions: each contains a line, and two lines span a plane, which is still proper.  So the order
complex of the proper nonzero subspaces is connected, and its degree-zero homology is a single copy
of the coefficients — the reduced homology vanishes in degree zero.

Together with the vanishing above degree zero this is the whole of the statement that the reduced
homology of the building is concentrated in the top degree.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

section

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- Every nonzero proper subspace contains a line. -/
theorem exists_atom_le_properPart (U : properPart (Submodule K V)) :
    ∃ l : properPart (Submodule K V), IsAtom (l : Submodule K V) ∧ l ≤ U := by
  obtain ⟨l, hl, hlU⟩ :=
    (eq_bot_or_exists_atom_le (U : Submodule K V)).resolve_left (ne_of_gt U.2.1)
  exact ⟨⟨l, hl.1.bot_lt, lt_of_le_of_lt hlU U.2.2⟩, hl, hlU⟩

/-- Two lines span a subspace of dimension at most two, which is proper in dimension at least
three. -/
theorem sup_atom_lt_top (h3 : 3 ≤ finrank K V) {l l' : Submodule K V} (hl : IsAtom l)
    (hl' : IsAtom l') : l ⊔ l' < ⊤ := by
  refine lt_of_le_of_ne le_top fun hcon => ?_
  have hsum : finrank K (l ⊔ l' : Submodule K V) + finrank K (l ⊓ l' : Submodule K V)
      = finrank K l + finrank K l' := Submodule.finrank_sup_add_finrank_inf_eq l l'
  rw [hcon, finrank_top, Submodule.isAtom_iff_finrank_eq_one.1 hl,
    Submodule.isAtom_iff_finrank_eq_one.1 hl'] at hsum
  omega

/-- **Any two nonzero proper subspaces are joined by a chain of inclusions.** -/
theorem reflTransGen_comparable_properPart_submodule (h3 : 3 ≤ finrank K V)
    (U U' : properPart (Submodule K V)) :
    Relation.ReflTransGen (fun x y : properPart (Submodule K V) => x ≤ y ∨ y ≤ x) U U' := by
  obtain ⟨l, hl, hlU⟩ := exists_atom_le_properPart U
  obtain ⟨l', hl', hlU'⟩ := exists_atom_le_properPart U'
  let J : properPart (Submodule K V) :=
    ⟨(l : Submodule K V) ⊔ (l' : Submodule K V), lt_of_lt_of_le l.2.1 le_sup_left,
      sup_atom_lt_top h3 hl hl'⟩
  have hlJ : l ≤ J :=
    show (l : Submodule K V) ≤ (l : Submodule K V) ⊔ (l' : Submodule K V) from le_sup_left
  have hl'J : l' ≤ J :=
    show (l' : Submodule K V) ≤ (l : Submodule K V) ⊔ (l' : Submodule K V) from le_sup_right
  exact .head (Or.inr hlU) (.head (Or.inl hlJ) (.head (Or.inr hl'J) (.single (Or.inl hlU'))))

/-- A zigzag of comparabilities in a poset is one in the opposite poset. -/
theorem reflTransGen_comparable_orderDual {P : Type u} [PartialOrder P] {a b : P}
    (h : Relation.ReflTransGen (fun x y : P => x ≤ y ∨ y ≤ x) a b) :
    Relation.ReflTransGen (fun x y : Pᵒᵈ => x ≤ y ∨ y ≤ x)
      (OrderDual.toDual a) (OrderDual.toDual b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (Or.symm hstep)

/-- **The building of a vector space of dimension at least three is connected.** -/
theorem isPreconnected_nerve_properPart_submodule (h3 : 3 ≤ finrank K V) :
    SSet.IsPreconnected (nerve (properPart (Submodule K V))) :=
  isPreconnected_nerve_of_zigzag (reflTransGen_comparable_properPart_submodule h3)

omit [FiniteDimensional K V] in
/-- **And it has a vertex**: a line is a nonzero proper subspace. -/
theorem nonempty_properPart_submodule (h3 : 3 ≤ finrank K V) :
    Nonempty (properPart (Submodule K V)) := by
  obtain ⟨l, hl, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule K V)).resolve_left (fun hcon => by
    rw [← finrank_top (R := K) (M := V)] at h3
    rw [hcon, finrank_bot] at h3
    omega)
  refine ⟨⟨l, hl.1.bot_lt, lt_of_le_of_ne le_top fun hcon => ?_⟩⟩
  rw [← finrank_top (R := K) (M := V), ← hcon, Submodule.isAtom_iff_finrank_eq_one.1 hl] at h3
  omega

theorem isConnected_nerve_properPart_submodule (h3 : 3 ≤ finrank K V) :
    SSet.IsConnected (nerve (properPart (Submodule K V))) := by
  haveI := isPreconnected_nerve_properPart_submodule h3
  obtain ⟨U⟩ := nonempty_properPart_submodule (K := K) (V := V) h3
  exact ⟨⟨ComposableArrows.mk₀ U⟩⟩

/-- **The horizon complex — the same order complex with the order reversed — is connected.** -/
theorem isPreconnected_nerve_properPart_submodule_orderDual (h3 : 3 ≤ finrank K V) :
    SSet.IsPreconnected (nerve ((properPart (Submodule K V))ᵒᵈ)) := by
  refine isPreconnected_nerve_of_zigzag fun a b => ?_
  exact reflTransGen_comparable_orderDual
    (reflTransGen_comparable_properPart_submodule h3 (OrderDual.ofDual a) (OrderDual.ofDual b))

theorem isConnected_nerve_properPart_submodule_orderDual (h3 : 3 ≤ finrank K V) :
    SSet.IsConnected (nerve ((properPart (Submodule K V))ᵒᵈ)) := by
  haveI := isPreconnected_nerve_properPart_submodule_orderDual h3
  obtain ⟨U⟩ := nonempty_properPart_submodule (K := K) (V := V) h3
  exact ⟨⟨ComposableArrows.mk₀ (OrderDual.toDual U)⟩⟩

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The degree-zero homology of the building is a single copy of the coefficients.**  This is the
degree-zero half of the statement that the reduced homology is concentrated in the top degree. -/
noncomputable def homologyZeroIsoProperPartSubmodule (h3 : 3 ≤ finrank K V) (R : C) :
    (nerve (properPart (Submodule K V))).homology R 0 ≅ R := by
  haveI := isConnected_nerve_properPart_submodule (K := K) (V := V) h3
  exact asIso ((nerve (properPart (Submodule K V))).homology₀ε R)

/-- The same for the building in the presentation of the horizon complex. -/
noncomputable def homologyZeroIsoBuilding (h3 : 3 ≤ finrank K V) (R : C) :
    (nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)).homology R 0 ≅ R := by
  haveI := isConnected_nerve_properPart_submodule_orderDual (K := K) (V := V) h3
  have e : (nerve ((properPart (Submodule K V))ᵒᵈ)).homology R 0 ≅ R :=
    asIso ((nerve ((properPart (Submodule K V))ᵒᵈ)).homology₀ε R)
  exact (SSet.homologyFunctor R 0).mapIso
      (orderIsoNerveIso (OrderIso.dual (properPartNeOrderIso (L := Submodule K V)))).symm ≪≫ e

end

end

end GaloisForLFunctions.HTGeometry
