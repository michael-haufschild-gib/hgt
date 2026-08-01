import GaloisForLFunctions.HTGeometry.ProjectiveFlagDimension
import Mathlib.FieldTheory.Galois.Basic

/-!
# The horizon assignment is an order-reversing injection

The common-horizon field of a family of horizons is the fixed field of its stabiliser.  Over a finite
extension the fixed-field map on subgroups is injective and order-reversing, so an assignment of
stabilisers that is itself injective and order-preserving turns a poset of horizon data into a poset
of fields, with the order reversed.

Composed with the chain bound for subspaces, this is the passage from a strict chain of
common-horizon fields to a flag: the two order complexes have the same simplices, of dimension at
most `N - 2`.
-/

namespace GaloisForLFunctions.HTGeometry

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- **The fixed-field map on subgroups is injective.**  Its inverse on the image is the fixing
subgroup. -/
theorem fixedField_injective :
    Function.Injective (fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) := by
  intro H H' h
  rw [← fixingSubgroup_fixedField H, ← fixingSubgroup_fixedField H', h]

omit [FiniteDimensional F E] in
/-- **And order-reversing.** -/
theorem fixedField_antitone :
    Antitone (fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) := by
  intro H H' hle x hx
  rw [mem_fixedField_iff] at hx ⊢
  exact fun f hf => hx f (hle hf)

/-- **The horizon assignment is an order-reversing injection.**  If the stabiliser of a family of
horizons depends injectively and monotonically on the family, then its common field depends
injectively and antitonically. -/
theorem fixedField_comp_injective_antitone {α : Type*} [PartialOrder α]
    (G : α → Subgroup (E ≃ₐ[F] E)) (hmono : Monotone G) (hinj : Function.Injective G) :
    Function.Injective (fun S => fixedField (G S)) ∧ Antitone (fun S => fixedField (G S)) :=
  ⟨fun _ _ h => hinj (fixedField_injective h), fun _ _ h => fixedField_antitone (hmono h)⟩

omit [FiniteDimensional F E] in
/-- **The fixing subgroup is order-reversing.** -/
theorem fixingSubgroup_antitone :
    Antitone (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)) := by
  intro A B hle f hf
  rw [IntermediateField.mem_fixingSubgroup_iff] at hf ⊢
  exact fun x hx => hf x (hle hx)

/-- **The fixed-field map reflects the order.**  Over a finite extension it is an order embedding
into the opposite order, not merely an injection: if one fixed field contains another, the
subgroups are nested the other way. -/
theorem fixedField_reflects_le {H H' : Subgroup (E ≃ₐ[F] E)}
    (h : fixedField H' ≤ fixedField H) : H ≤ H' := by
  have := fixingSubgroup_antitone h
  rwa [fixingSubgroup_fixedField, fixingSubgroup_fixedField] at this

/-! ## Order embeddings and injectivity -/

/-- **An order-reflecting map is injective**, with no monotonicity needed either way.  So a horizon
assignment that reflects the order needs no separate injectivity hypothesis. -/
theorem injective_of_reflects_le {α γ : Type*} [PartialOrder α] [Preorder γ]
    (f : α → γ) (hrefl : ∀ S T : α, f T ≤ f S → S ≤ T) :
    Function.Injective f := by
  intro S T h
  exact le_antisymm (hrefl S T (le_of_eq h.symm)) (hrefl T S (le_of_eq h))

/-- **The horizon assignment is an order embedding as soon as the stabiliser assignment is.**  With
the fixed-field map reflecting the order automatically, the parent theorem owes only that a family of
horizons is recovered from its stabiliser: `G_S ≤ G_T → S ≤ T`. -/
theorem fixedField_comp_reflects {α : Type*} [PartialOrder α] (G : α → Subgroup (E ≃ₐ[F] E))
    (hrefl : ∀ S T : α, G S ≤ G T → S ≤ T) (S T : α)
    (h : fixedField (G T) ≤ fixedField (G S)) : S ≤ T :=
  hrefl S T (fixedField_reflects_le h)

/-- **And is then injective.** -/
theorem fixedField_comp_injective_of_reflects {α : Type*} [PartialOrder α]
    (G : α → Subgroup (E ≃ₐ[F] E)) (hrefl : ∀ S T : α, G S ≤ G T → S ≤ T) :
    Function.Injective (fun S => fixedField (G S)) :=
  injective_of_reflects_le _ (fun S T h => fixedField_comp_reflects G hrefl S T h)

/-! ## The chain bound for horizon fields -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A strict chain of common-horizon fields has at most `N - 1` members.**  The horizon assignment
carries a chain of subspaces to a chain of fields of the same size, and the subspace chains are
bounded by the flag bound. -/
theorem card_image_fixedField_le [DecidableEq (IntermediateField F E)]
    (G : Submodule K V → Subgroup (E ≃ₐ[F] E)) (hmono : Monotone G)
    (hinj : Function.Injective G) (S : Finset (Submodule K V))
    (hchain : ∀ W ∈ S, ∀ W' ∈ S, W ≤ W' ∨ W' ≤ W)
    (hbot : ∀ W ∈ S, W ≠ ⊥) (htop : ∀ W ∈ S, W ≠ ⊤) :
    (S.image (fun W => fixedField (G W))).card ≤ Module.finrank K V - 1 := by
  obtain ⟨hinj', hanti⟩ := fixedField_comp_injective_antitone G hmono hinj
  exact card_image_le_finrank_sub_one _ (fun W W' h => hanti h) hinj' S hchain hbot htop

/-- **And that bound is attained.** -/
theorem exists_image_fixedField_card_eq [DecidableEq (IntermediateField F E)]
    (G : Submodule K V → Subgroup (E ≃ₐ[F] E)) (hmono : Monotone G)
    (hinj : Function.Injective G) (hN : 0 < Module.finrank K V) :
    ∃ T : Finset (IntermediateField F E), T.card = Module.finrank K V - 1 ∧
      (∀ u ∈ T, ∀ v ∈ T, u ≤ v ∨ v ≤ u) := by
  obtain ⟨hinj', hanti⟩ := fixedField_comp_injective_antitone G hmono hinj
  exact exists_image_chain_card_eq _ (fun W W' h => hanti h) hinj' hN

/-! ## The stabiliser of a family of horizons -/

section Stabilizer

variable {β : Type*} [CompleteLattice β] {α : Type*} [Preorder α]

/-- The stabiliser of a family of horizons: the join of the stabilisers of all the elementary
horizons the family contains.  Stated for an arbitrary complete lattice, so that it applies to
subgroups, to subspaces, and to intermediate fields alike. -/
def horizonStabilizer (H : α → β) (S : α) : β :=
  ⨆ ℓ : {ℓ : α // ℓ ≤ S}, H ℓ.1

/-- **The stabiliser assignment is monotone.**  A larger family of horizons has a larger stabiliser,
so the horizon field it fixes is smaller: the order reversal of the card is already visible here. -/
theorem horizonStabilizer_monotone (H : α → β) : Monotone (horizonStabilizer H) := by
  intro S T hST
  refine iSup_le fun ℓ => ?_
  exact le_iSup (fun m : {m : α // m ≤ T} => H m.1) ⟨ℓ.1, le_trans ℓ.2 hST⟩

/-- **Each elementary horizon's stabiliser lies in the family's.** -/
theorem le_horizonStabilizer (H : α → β) {ℓ S : α} (h : ℓ ≤ S) :
    H ℓ ≤ horizonStabilizer H S :=
  le_iSup (fun m : {m : α // m ≤ S} => H m.1) ⟨ℓ, h⟩

/-- **Injectivity of the stabiliser assignment from detection and generation.**  If an elementary
horizon's stabiliser lies in a family's stabiliser only when that horizon belongs to the family, and
the families are determined by the elementary horizons they contain, then distinct families have
distinct stabilisers. -/
theorem horizonStabilizer_injective (H : α → β) (P : α → Prop)
    (detect : ∀ ℓ S : α, P ℓ → H ℓ ≤ horizonStabilizer H S → ℓ ≤ S)
    (gen : ∀ S T : α, (∀ ℓ, P ℓ → (ℓ ≤ S ↔ ℓ ≤ T)) → S = T) :
    Function.Injective (horizonStabilizer H) := by
  intro S T h
  refine gen S T fun ℓ hℓ => ⟨fun hS => ?_, fun hT => ?_⟩
  · exact detect ℓ T hℓ (h ▸ le_horizonStabilizer H hS)
  · exact detect ℓ S hℓ (h.symm ▸ le_horizonStabilizer H hT)

end Stabilizer

section IdentityWitness

variable {α : Type*} [CompleteLattice α]

/-- **The criterion is satisfiable.**  Taking each family of horizons to be its own stabiliser, the
assignment is the identity: the join of everything below a family is that family, so detection and
generation both hold and the assignment is injective. -/
theorem horizonStabilizer_id (S : α) : horizonStabilizer (id : α → α) S = S := by
  refine le_antisymm (iSup_le fun ℓ => ℓ.2) ?_
  exact le_iSup (fun m : {m : α // m ≤ S} => (id m.1 : α)) ⟨S, le_rfl⟩

end IdentityWitness

/-! ## Families of horizons are determined by their lines -/

omit [FiniteDimensional K V] in
/-- **A subspace is determined by the lines it contains.**  So the generation hypothesis of the
injectivity criterion holds for the poset of horizon families, and only detection is left to the
horizon geometry. -/
theorem eq_of_lines_le_iff {S T : Submodule K V}
    (h : ∀ ℓ : Submodule K V, Module.finrank K ℓ = 1 → (ℓ ≤ S ↔ ℓ ≤ T)) : S = T := by
  have key : ∀ (A B : Submodule K V),
      (∀ ℓ : Submodule K V, Module.finrank K ℓ = 1 → (ℓ ≤ A ↔ ℓ ≤ B)) → A ≤ B := by
    intro A B hAB x hx
    rcases eq_or_ne x 0 with rfl | hne
    · exact B.zero_mem
    · have hline : Module.finrank K (K ∙ x) = 1 := finrank_span_singleton hne
      have hxA : (K ∙ x) ≤ A := (Submodule.span_singleton_le_iff_mem x A).2 hx
      exact (Submodule.span_singleton_le_iff_mem x B).1 ((hAB _ hline).1 hxA)
  exact le_antisymm (key S T h) (key T S fun ℓ hℓ => (h ℓ hℓ).symm)

end GaloisForLFunctions.HTGeometry
