import GaloisForLFunctions.HTGeometry.ConstitutiveFinitaryFormation

/-!
# Canonical extensive formation witnesses

Every formation has a least pointwise extensive hull obtained by retaining the input alongside its
new consequences.  The construction preserves monotonicity and finitarity, so it supplies the
formation hypotheses used by finite-history saturation without changing their finite-ancestry
content.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- Retain every input law alongside the consequences of `f`. -/
def extensiveFormationHull {α : Type*} (f : Set α → Set α) (A : Set α) : Set α :=
  A ∪ f A

/-- Every formation's extensive hull is extensive. -/
theorem extensiveFormationHull_isExtensive {α : Type*} (f : Set α → Set α) :
    IsExtensiveFormation (extensiveFormationHull f) := by
  intro A
  exact subset_union_left

/-- Identity is an unconditional extensive formation. -/
theorem isExtensiveFormation_id {α : Type*} :
    IsExtensiveFormation (id : Set α → Set α) := by
  intro A
  exact Subset.rfl

/-- Every closure operator is an extensive formation. -/
theorem isExtensiveFormation_closureOperator
    {α : Type*} (c : ClosureOperator (Set α)) :
    IsExtensiveFormation c :=
  c.le_closure

/-- The extensive hull is the least pointwise extensive formation containing `f`. -/
theorem extensiveFormationHull_least
    {α : Type*} {f g : Set α → Set α}
    (hext : IsExtensiveFormation g) (hfg : ∀ A, f A ⊆ g A) :
    ∀ A, extensiveFormationHull f A ⊆ g A := by
  intro A x hx
  rcases hx with hx | hx
  · exact hext A hx
  · exact hfg A hx

/-- The extensive-hull construction preserves monotonicity. -/
theorem extensiveFormationHull_monotone
    {α : Type*} {f : Set α → Set α} (hf : Monotone f) :
    Monotone (extensiveFormationHull f) := by
  intro A B hAB x hx
  rcases hx with hx | hx
  · exact Or.inl (hAB hx)
  · exact Or.inr (hf hAB hx)

/-- The extensive-hull construction preserves finite ancestry. -/
theorem extensiveFormationHull_finitary
    {α : Type*} {f : Set α → Set α} (hf : IsFinitaryFormation f) :
    IsFinitaryFormation (extensiveFormationHull f) := by
  classical
  intro A x hx
  rcases hx with hxA | hxf
  · exact ⟨{x}, by simp [hxA], by simp [extensiveFormationHull]⟩
  · obtain ⟨F, hFA, hxF⟩ := hf hxf
    exact ⟨F, hFA, Or.inr hxF⟩

end GaloisForLFunctions.HTGeometry
