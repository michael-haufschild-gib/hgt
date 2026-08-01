import GaloisForLFunctions.HTGeometry.HorizonGaloisAssignment
import GaloisForLFunctions.HTGeometry.CuspedHorizonHomotopy

/-!
# The horizon complex is the order complex of the building

An assignment of horizon fields that reverses the order and reflects it is an order isomorphism from
the opposite of its source onto its range.  Passing to nerves turns that into an isomorphism of order
complexes: the incidence complex of common-horizon fields is the order complex of the poset of
nonzero proper subspaces, with no further input.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory IntermediateField

universe u

/-! ## Order embeddings onto their range -/

/-- **A monotone, order-reflecting map is an order isomorphism onto its range.** -/
noncomputable def orderIsoRange {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α → β)
    (hmono : Monotone f) (hrefl : ∀ a b : α, f a ≤ f b → a ≤ b) :
    α ≃o Set.range f :=
  { Equiv.ofInjective f (fun a b hab =>
      le_antisymm (hrefl a b (le_of_eq hab)) (hrefl b a (le_of_eq hab.symm))) with
    map_rel_iff' := fun {a b} => ⟨fun h => hrefl a b h, fun h => hmono h⟩ }

/-- **An antitone, order-reflecting map is an order isomorphism from the opposite order onto its
range.** -/
noncomputable def orderIsoRangeOfAntitone {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α → β)
    (hanti : Antitone f) (hrefl : ∀ a b : α, f a ≤ f b → b ≤ a) :
    αᵒᵈ ≃o Set.range f :=
  (orderIsoRange (α := αᵒᵈ) (fun a => f (OrderDual.ofDual a))
    (fun _ _ h => hanti h) (fun _ _ h => hrefl _ _ h)).trans
      (OrderIso.setCongr _ _ (by
        ext y
        exact ⟨fun ⟨a, ha⟩ => ⟨OrderDual.ofDual a, ha⟩, fun ⟨a, ha⟩ => ⟨OrderDual.toDual a, ha⟩⟩))

/-- **The order complex of a poset is isomorphic to that of its image**, when the map reverses and
reflects the order. -/
noncomputable def nerveIsoRangeOfAntitone {α β : Type u} [PartialOrder α] [PartialOrder β]
    (f : α → β) (hanti : Antitone f) (hrefl : ∀ a b : α, f a ≤ f b → b ≤ a) :
    nerveFunctor.obj (Cat.of αᵒᵈ) ≅ nerveFunctor.obj (Cat.of (Set.range f)) :=
  orderIsoNerveIso (orderIsoRangeOfAntitone f hanti hrefl)

/-! ## The horizon complex -/

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- The fixed field of the stabiliser of a horizon, as a function of the horizon. -/
def stabiliserFixedField (G : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} → Subgroup (E ≃ₐ[F] E))
    (S : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) : IntermediateField F E :=
  fixedField (G S)

omit [FiniteDimensional F E] in
/-- **The horizon field assignment reverses the order.** -/
theorem stabiliserFixedField_antitone {G : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} → Subgroup (E ≃ₐ[F] E)}
    (hmono : Monotone G) : Antitone (stabiliserFixedField (F := F) (E := E) G) :=
  fun _ _ h => fixedField_antitone (hmono h)

/-- **And reflects it, as soon as the stabiliser assignment does.** -/
theorem stabiliserFixedField_reflects {G : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} → Subgroup (E ≃ₐ[F] E)}
    (hreflG : ∀ S T, G S ≤ G T → S ≤ T) (a b : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})
    (h : stabiliserFixedField (F := F) (E := E) G a ≤ stabiliserFixedField G b) : b ≤ a :=
  hreflG b a (fixedField_reflects_le h)

/-- **The canonical simplicial isomorphism between the horizon complex and the order complex of the
building.**  A strict chain of common-horizon fields is exactly a flag of nonzero proper subspaces,
and the two order complexes are isomorphic — no topology is used, only that the assignment reverses
and reflects the order. -/
noncomputable def horizonComplexIso
    (G : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} → Subgroup (E ≃ₐ[F] E))
    (hmono : Monotone G) (hreflG : ∀ S T, G S ≤ G T → S ≤ T) :
    nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)
      ≅ nerveFunctor.obj (Cat.of (Set.range (stabiliserFixedField (F := F) (E := E) G))) :=
  nerveIsoRangeOfAntitone _ (stabiliserFixedField_antitone hmono) (stabiliserFixedField_reflects hreflG)

/-- **The horizon complex has the homology of the building**, in every degree and with any
coefficients. -/
noncomputable def horizonComplexHomologyIso
    (G : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} → Subgroup (E ≃ₐ[F] E))
    (hmono : Monotone G) (hreflG : ∀ S T, G S ≤ G T → S ≤ T) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ) :
    (nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)).homology R n
      ≅ (nerveFunctor.obj
          (Cat.of (Set.range (stabiliserFixedField (F := F) (E := E) G)))).homology R n :=
  (SSet.homologyFunctor R n).mapIso (horizonComplexIso G hmono hreflG)

/-! ## The homology of the horizon complex -/

/-- **The horizon complex has no homology above the building's dimension.** -/
theorem isZero_horizonComplexHomology [FiniteDimensional K V]
    (G : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} → Subgroup (E ≃ₐ[F] E))
    (hmono : Monotone G) (hreflG : ∀ S T, G S ≤ G T → S ≤ T) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : Module.finrank K V - 1 ≤ n) :
    Limits.IsZero ((nerveFunctor.obj
      (Cat.of (Set.range (stabiliserFixedField (F := F) (E := E) G)))).homology R n) := by
  haveI := buildingHasDimensionLT K V
  exact Limits.IsZero.of_iso
    (isZero_homology_of_hasDimensionLT _ (Module.finrank K V - 1) R n hn)
    (horizonComplexHomologyIso G hmono hreflG R n).symm

/-- **The horizon complex is connected in dimension at least three**, so its homology in degree zero
is a single copy of the coefficients. -/
noncomputable def horizonComplexHomologyZeroIso [FiniteDimensional K V]
    (G : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} → Subgroup (E ≃ₐ[F] E))
    (hmono : Monotone G) (hreflG : ∀ S T, G S ≤ G T → S ≤ T)
    (hN : 3 ≤ Module.finrank K V) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) :
    (nerveFunctor.obj
      (Cat.of (Set.range (stabiliserFixedField (F := F) (E := E) G)))).homology R 0 ≅ R := by
  haveI : SSet.IsConnected
      (nerveFunctor.obj (Cat.of (({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ))) :=
    buildingIsConnected K V hN
  exact (horizonComplexHomologyIso G hmono hreflG R 0).symm ≪≫
    asIso ((nerveFunctor.obj (Cat.of (({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ))).homology₀ε R)

end GaloisForLFunctions.HTGeometry
