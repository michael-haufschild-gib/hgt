import GaloisForLFunctions.HTGeometry.CompactAbelianPeterWeyl

/-!
# Character Hasse principle for compact abelian groups

Continuous unitary characters are bundled into a reusable carrier.  Peter--Weyl separation then
becomes a faithful global character profile: all character values determine a compact-abelian
point, every nonzero point has one character witness, and the group is equivalent to the profile
range it realizes.

This is a Pontryagin-style local--global observability theorem.  It supplies character-dual
infrastructure useful well beyond any one RH route.
-/

namespace GaloisForLFunctions.CompactAbelian

noncomputable section

/-- A bundled continuous unitary character of an additive topological group. -/
structure UnitaryContinuousCharacter
    (G : Type*) [TopologicalSpace G] [Add G] where
  toFun : G → ℂ
  continuous_toFun : Continuous toFun
  map_add' : ∀ a b, toFun (a + b) = toFun a * toFun b
  norm_toFun : ∀ a, ‖toFun a‖ = 1

instance {G : Type*} [TopologicalSpace G] [Add G] :
    CoeFun (UnitaryContinuousCharacter G) (fun _ ↦ G → ℂ) :=
  ⟨UnitaryContinuousCharacter.toFun⟩

namespace UnitaryContinuousCharacter

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G]

theorem map_add (χ : UnitaryContinuousCharacter G) (a b : G) :
    χ (a + b) = χ a * χ b := χ.map_add' a b

theorem value_ne_zero (χ : UnitaryContinuousCharacter G) (a : G) : χ a ≠ 0 := by
  intro hzero
  have hnorm := χ.norm_toFun a
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

@[simp] theorem map_zero (χ : UnitaryContinuousCharacter G) : χ 0 = 1 := by
  have h := χ.map_add 0 0
  simp only [zero_add] at h
  apply mul_left_cancel₀ (χ.value_ne_zero 0)
  rw [← h, mul_one]

end UnitaryContinuousCharacter

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- Every nonzero point of a compact abelian group is detected by a bundled character. -/
theorem exists_unitaryContinuousCharacter_ne_one {g : G} (hg : g ≠ 0) :
    ∃ χ : UnitaryContinuousCharacter G, χ g ≠ 1 := by
  obtain ⟨χ, hcont, hadd, hnorm, hχ⟩ := exists_character_ne_one hg
  exact ⟨⟨χ, hcont, hadd, hnorm⟩, hχ⟩

/-- Distinct compact-abelian points are separated by one continuous unitary character. -/
theorem exists_unitaryContinuousCharacter_ne_of_ne
    {x y : G} (hxy : x ≠ y) :
    ∃ χ : UnitaryContinuousCharacter G, χ x ≠ χ y := by
  have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hxy
  obtain ⟨χ, hχ⟩ := exists_unitaryContinuousCharacter_ne_one hdiff
  refine ⟨χ, ?_⟩
  intro heq
  apply hχ
  apply mul_right_cancel₀ (χ.value_ne_zero y)
  have h := χ.map_add (x - y) y
  rw [sub_add_cancel, heq] at h
  simpa using h.symm

/-- Evaluation against every continuous unitary character. -/
def unitaryCharacterProfile (G : Type*) [TopologicalSpace G] [Add G] :
    G → (UnitaryContinuousCharacter G → ℂ) :=
  fun g χ ↦ χ g

/-- The full unitary-character profile is faithful on compact abelian groups. -/
theorem unitaryCharacterProfile_injective :
    Function.Injective (unitaryCharacterProfile G) := by
  intro x y hxy
  by_contra hne
  obtain ⟨χ, hχ⟩ := exists_unitaryContinuousCharacter_ne_of_ne hne
  exact hχ (congrFun hxy χ)

/-- A compact abelian group is equivalent to the character profiles it realizes. -/
noncomputable def unitaryCharacterProfileEquivRange :
    G ≃ Set.range (unitaryCharacterProfile G) :=
  Equiv.ofInjective (unitaryCharacterProfile G) unitaryCharacterProfile_injective

/-- Pontryagin-style Hasse congruence: all character values determine a point. -/
theorem compactAbelian_congr_character_hasse_iff (x y : G) :
    x = y ↔ ∀ χ : UnitaryContinuousCharacter G, χ x = χ y := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    exact unitaryCharacterProfile_injective (funext h)

/-- A compact-abelian point is zero exactly when every character is trivial there. -/
theorem compactAbelian_eq_zero_character_hasse_iff (g : G) :
    g = 0 ↔ ∀ χ : UnitaryContinuousCharacter G, χ g = 1 := by
  rw [compactAbelian_congr_character_hasse_iff]
  simp

end

end GaloisForLFunctions.CompactAbelian
