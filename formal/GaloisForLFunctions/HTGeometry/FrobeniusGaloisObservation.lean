import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Ext

/-!
# Frobenius–Galois operators on observation fibers

The right and left operators of Wang–Shi–Wang, arXiv:2609.09529,
Definition 3.8 and Proposition 3.13, are realized by universal and existential
quantification over fibers of an arbitrary observation. Multiplication is
intersection and the residual is Boolean implication. No separation,
surjectivity, finiteness, or nonemptiness condition is needed.
-/

namespace GaloisForLFunctions.HTGeometry.FrobeniusGalois

variable {X Y Z : Type*}

/-- States whose entire observation fiber satisfies a property. -/
def lower (q : X → Y) (S : Set X) : Set X :=
  {x | ∀ y, q y = q x → y ∈ S}

/-- States whose observation fiber contains a witness to a property. -/
def upper (q : X → Y) (S : Set X) : Set X :=
  {x | ∃ y ∈ S, q y = q x}

/-- Residuation for intersection on the Boolean algebra of properties. -/
def implication (S T : Set X) : Set X := Sᶜ ∪ T

/-- Boolean properties form a commutative integral residuated lattice. -/
theorem residuation (S T U : Set X) :
    S ∩ T ⊆ U ↔ T ⊆ implication S U := by
  classical
  constructor
  · intro h x hx
    by_cases hs : x ∈ S
    · exact Or.inr (h ⟨hs, hx⟩)
    · exact Or.inl hs
  · intro h x hx
    exact (h hx.2).resolve_left (fun hn => hn hx.1)

theorem lower_subset (q : X → Y) (S : Set X) : lower q S ⊆ S :=
  fun x hx => hx x rfl

theorem subset_upper (q : X → Y) (S : Set X) : S ⊆ upper q S :=
  fun x hx => ⟨x, hx, rfl⟩

/-- The paper's adjunction is closed for every observation map. -/
theorem adjunction (q : X → Y) : GaloisConnection (upper q) (lower q) := by
  intro S T
  constructor
  · intro h x hx y hy
    exact h ⟨x, hx, hy.symm⟩
  · intro h x hx
    obtain ⟨y, hy, he⟩ := hx
    exact h hy x he.symm

theorem upper_lower (q : X → Y) (S : Set X) : upper q (lower q S) = lower q S := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩ z hz
    exact hy z (hz.trans he.symm)
  · exact fun hx => subset_upper q _ hx

theorem lower_upper (q : X → Y) (S : Set X) : lower q (upper q S) = upper q S := by
  ext x
  constructor
  · exact fun hx => lower_subset q _ hx
  · rintro ⟨y, hy, he⟩ z hz
    exact ⟨y, hy, he.trans hz.symm⟩

theorem lower_idempotent (q : X → Y) (S : Set X) : lower q (lower q S) = lower q S := by
  rw [← upper_lower q S, lower_upper]

theorem upper_idempotent (q : X → Y) (S : Set X) : upper q (upper q S) = upper q S := by
  rw [← lower_upper q S, upper_lower]

theorem lower_empty (q : X → Y) : lower q ∅ = ∅ := by
  ext x
  exact ⟨fun hx => hx x rfl, False.elim⟩

theorem upper_empty (q : X → Y) : upper q ∅ = ∅ := by
  ext x
  simp [upper]

theorem lower_univ (q : X → Y) : lower q Set.univ = Set.univ := by
  ext x
  simp [lower]

theorem upper_univ (q : X → Y) : upper q Set.univ = Set.univ := by
  ext x
  exact ⟨fun _ => Set.mem_univ x, fun _ => ⟨x, Set.mem_univ x, rfl⟩⟩

theorem lower_inter (q : X → Y) (S T : Set X) :
    lower q (S ∩ T) = lower q S ∩ lower q T :=
  (adjunction q).u_inf

theorem upper_union (q : X → Y) (S T : Set X) :
    upper q (S ∪ T) = upper q S ∪ upper q T :=
  (adjunction q).l_sup

/-- FARL5: an already observable factor can be moved outside possibility. -/
theorem upper_inter_upper (q : X → Y) (S T : Set X) :
    upper q (S ∩ upper q T) = upper q S ∩ upper q T := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, z, hz, he⟩, hyx⟩
    exact ⟨⟨y, hy, hyx⟩, z, hz, he.trans hyx⟩
  · rintro ⟨⟨y, hy, hyx⟩, z, hz, hzx⟩
    exact ⟨y, ⟨hy, z, hz, hzx.trans hyx.symm⟩, hyx⟩

/-- FARL4: observable alternatives commute with certainty. -/
theorem lower_upper_union (q : X → Y) (S T : Set X) :
    lower q (upper q S ∪ T) = upper q S ∪ lower q T := by
  classical
  ext x
  constructor
  · intro h
    by_cases hx : x ∈ upper q S
    · exact Or.inl hx
    · right
      intro y hy
      rcases h y hy with hs | ht
      · obtain ⟨z, hz, he⟩ := hs
        exact False.elim (hx ⟨z, hz, he.trans hy⟩)
      · exact ht
  · rintro (⟨y, hy, he⟩ | ht) z hz
    · exact Or.inl ⟨y, hy, he.trans hz.symm⟩
    · exact Or.inr (ht z hz)

/-- FARL3: residual Frobenius reciprocity. -/
theorem lower_upper_implication (q : X → Y) (S T : Set X) :
    lower q (implication (upper q S) T) = implication (upper q S) (lower q T) := by
  classical
  ext x
  change (∀ y, q y = q x → (y ∉ upper q S ∨ y ∈ T)) ↔
    (x ∉ upper q S ∨ ∀ y, q y = q x → y ∈ T)
  constructor
  · intro h
    by_cases hx : x ∈ upper q S
    · right
      intro y hy
      rcases h y hy with hn | ht
      · obtain ⟨z, hz, he⟩ := hx
        exact False.elim (hn ⟨z, hz, he.trans hy.symm⟩)
      · exact ht
    · exact Or.inl hx
  · rintro (hn | ht) y hy
    · left
      rintro ⟨z, hz, he⟩
      exact hn ⟨z, hz, he.trans hy⟩
    · exact Or.inr (ht y hy)

/-- FARL24 and the involutive dual FARL30. -/
theorem lower_compl (q : X → Y) (S : Set X) : lower q Sᶜ = (upper q S)ᶜ := by
  ext x
  constructor
  · intro h hx
    obtain ⟨y, hy, he⟩ := hx
    exact h y he hy
  · intro h y he hy
    exact h ⟨y, hy, he⟩

theorem upper_compl (q : X → Y) (S : Set X) : upper q Sᶜ = (lower q S)ᶜ := by
  classical
  have h := lower_compl q Sᶜ
  simpa using congrArg (fun A : Set X => Aᶜ) h.symm

theorem lower_implication_lower (q : X → Y) (S T : Set X) :
    lower q (implication S (lower q T)) = implication (upper q S) (lower q T) := by
  rw [implication, Set.union_comm, ← upper_lower q T, lower_upper_union,
    lower_compl, upper_lower, Set.union_comm]
  rfl

theorem lower_lower_union (q : X → Y) (S T : Set X) :
    lower q (lower q S ∪ T) = lower q S ∪ lower q T := by
  rw [← upper_lower q S, lower_upper_union]

theorem upper_inter_lower (q : X → Y) (S T : Set X) :
    upper q (S ∩ lower q T) = upper q S ∩ lower q T := by
  rw [← upper_lower q T, upper_inter_upper]

theorem upper_eq_preimage_image (q : X → Y) (S : Set X) :
    upper q S = q ⁻¹' (q '' S) := rfl

/-- Properties expressed directly in observations are exactly fixed points. -/
theorem upper_fixed_iff (q : X → Y) (S : Set X) :
    upper q S = S ↔ ∃ T : Set Y, q ⁻¹' T = S := by
  constructor
  · intro h
    exact ⟨q '' S, h⟩
  · rintro ⟨T, rfl⟩
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      change q x ∈ T
      rwa [← he]
    · exact fun hx => subset_upper q _ hx

theorem lower_fixed_iff (q : X → Y) (S : Set X) :
    lower q S = S ↔ upper q S = S := by
  constructor
  · intro h
    rw [← h, upper_lower]
  · intro h
    rw [← h, lower_upper]

/-- A property has no uncertain states precisely when it is observable. -/
theorem lower_eq_upper_iff (q : X → Y) (S : Set X) :
    lower q S = upper q S ↔ ∃ T : Set Y, q ⁻¹' T = S := by
  rw [← upper_fixed_iff]
  constructor
  · intro h
    exact Set.Subset.antisymm (h ▸ lower_subset q S) (subset_upper q S)
  · intro h
    rw [h, (lower_fixed_iff q S).mpr h]

/-- Ambiguous states contain both a positive and a negative witness. -/
theorem uncertainty (q : X → Y) (S : Set X) :
    upper q S \ lower q S = upper q S ∩ upper q Sᶜ := by
  rw [upper_compl]
  rfl

/-- Forgetting observations can only enlarge possibility. -/
theorem upper_postprocess (q : X → Y) (r : Y → Z) (S : Set X) :
    upper q S ⊆ upper (r ∘ q) S := by
  rintro x ⟨y, hy, he⟩
  exact ⟨y, hy, congrArg r he⟩

/-- Forgetting observations can only reduce certainty. -/
theorem lower_postprocess (q : X → Y) (r : Y → Z) (S : Set X) :
    lower (r ∘ q) S ⊆ lower q S := by
  intro x hx y hy
  exact hx y (congrArg r hy)

/-- FARL17. -/
theorem lower_lower_implication (q : X → Y) (S T : Set X) :
    lower q (implication (lower q S) T) = implication (lower q S) (lower q T) := by
  rw [← upper_lower q S, lower_upper_implication]

/-- FARL19. -/
theorem lower_implication_upper (q : X → Y) (S T : Set X) :
    lower q (implication S (upper q T)) = implication (upper q S) (upper q T) := by
  rw [← lower_upper q T, lower_implication_lower]

/-- FARL20: certainty respects modus ponens. -/
theorem lower_implication_subset (q : X → Y) (S T : Set X) :
    lower q (implication S T) ⊆ implication (lower q S) (lower q T) := by
  classical
  intro x hx
  by_cases hs : x ∈ lower q S
  · right
    intro y hy
    exact (hx y hy).resolve_left (fun hn => hn (hs y hy))
  · exact Or.inl hs

/-- FARL21. -/
theorem lower_fixed_implication (q : X → Y) (S T : Set X) :
    lower q (implication (lower q S) (lower q T)) =
      implication (lower q S) (lower q T) := by
  rw [lower_lower_implication, lower_idempotent]

/-- FARL22. -/
theorem lower_compl_lower (q : X → Y) (S : Set X) :
    lower q (lower q S)ᶜ = (lower q S)ᶜ := by
  rw [lower_compl, upper_lower]

/-- FARL23. -/
theorem upper_compl_upper (q : X → Y) (S : Set X) :
    upper q (upper q S)ᶜ = (upper q S)ᶜ := by
  rw [upper_compl, lower_upper]

/-- FARL25. -/
theorem upper_fixed_inter (q : X → Y) (S T : Set X) :
    upper q (upper q S ∩ upper q T) = upper q S ∩ upper q T := by
  rw [upper_inter_upper, upper_idempotent]

/-- FARL26. -/
theorem upper_inter_lowers (q : X → Y) (S T : Set X) :
    upper q (lower q S ∩ lower q T) = lower q S ∩ lower q T := by
  rw [← lower_inter, upper_lower]

/-- FARL27. -/
theorem lower_inter_lowers (q : X → Y) (S T : Set X) :
    lower q (lower q S ∩ lower q T) = lower q S ∩ lower q T := by
  rw [← lower_inter, lower_idempotent]

/-- FARL28. -/
theorem lower_subset_iff (q : X → Y) (S T : Set X) :
    lower q S ⊆ T ↔ lower q S ⊆ lower q T := by
  rw [← (adjunction q) (lower q S) T, upper_lower]

/-- Every property is exactly observable precisely when the observation separates states. -/
theorem all_properties_exact_iff (q : X → Y) :
    (∀ S : Set X, lower q S = upper q S) ↔ Function.Injective q := by
  constructor
  · intro h x y he
    have hy : y ∈ upper q {x} := ⟨x, rfl, he⟩
    rw [← h {x}] at hy
    exact (lower_subset q {x} hy).symm
  · intro hinj S
    apply Set.Subset.antisymm
    · intro x hx
      exact subset_upper q S (lower_subset q S hx)
    · rintro x ⟨y, hy, he⟩ z hz
      rw [hinj hz, ← hinj he]
      exact hy

/-- The defining Frobenius laws hold simultaneously for every observation. -/
theorem frobenius_laws (q : X → Y) :
    (∀ S, lower q S ⊆ S) ∧ GaloisConnection (upper q) (lower q) ∧
    (∀ S T, lower q (implication (upper q S) T) =
      implication (upper q S) (lower q T)) ∧
    (∀ S T, lower q (upper q S ∪ T) = upper q S ∪ lower q T) ∧
    (∀ S T, upper q (S ∩ upper q T) = upper q S ∩ upper q T) :=
  ⟨lower_subset q, adjunction q, lower_upper_implication q,
    lower_upper_union q, upper_inter_upper q⟩

end GaloisForLFunctions.HTGeometry.FrobeniusGalois
