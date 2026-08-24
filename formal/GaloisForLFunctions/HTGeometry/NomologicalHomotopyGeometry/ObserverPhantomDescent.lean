import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.ObserverDescent
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Observer phantoms and effective descent

An observer phantom is a nonzero global morphism whose restriction to every member of an observer
family is zero.  It is the categorical normal form of a completion defect invisible to every
finite observer.

Universal effectivity rules out observer phantoms because a universally effective family is
jointly epimorphic.  Conversely, one observer phantom is a certificate that the family cannot be a
universally effective cover.  These statements are source-independent: an arithmetic application
must separately construct its observer family and prove universal effectivity without using the
global defect it is intended to exclude.
-/

open CategoryTheory

namespace HTGeometry.NomologicalHomotopyGeometry.ObserverDescent

open UniversalEffective

universe v u

variable {C : Type u} [Category.{v} C] [CategoryTheory.Limits.HasZeroMorphisms C]
variable {I : Type*} {X : I → C} {B W Z : C}

/-- Objects of a family obtained by adjoining a second observer stratum. -/
def SumObserverObject {J : Type*} (X : I → C) (Y : J → C) : I ⊕ J → C
  | .inl i => X i
  | .inr j => Y j

/-- Observer family obtained by adjoining a second stratum. -/
def sumObserverFamily {J : Type*} {Y : J → C}
    (π : ∀ i, X i ⟶ B) (κ : ∀ j, Y j ⟶ B) :
    ∀ s, SumObserverObject X Y s ⟶ B
  | .inl i => π i
  | .inr j => κ j

/-- A global morphism is invisible to an observer family when every observer restriction is zero. -/
def ObserverInvisible (π : ∀ i, X i ⟶ B) (χ : B ⟶ W) : Prop :=
  ∀ i, π i ≫ χ = 0

/-- A nonzero global morphism invisible to every observer. -/
def ObserverPhantom (π : ∀ i, X i ⟶ B) (χ : B ⟶ W) : Prop :=
  χ ≠ 0 ∧ ObserverInvisible π χ

/-- A charge is invisible to a sum of observer strata exactly when both strata miss it. -/
theorem observerInvisible_sum_iff {J : Type*} {Y : J → C}
    (π : ∀ i, X i ⟶ B) (κ : ∀ j, Y j ⟶ B) (χ : B ⟶ W) :
    ObserverInvisible (sumObserverFamily π κ) χ ↔
      ObserverInvisible π χ ∧ ObserverInvisible κ χ := by
  constructor
  · intro h
    exact ⟨fun i => h (.inl i), fun j => h (.inr j)⟩
  · rintro ⟨hπ, hκ⟩ (i | j)
    · exact hπ i
    · exact hκ j

/-- Refining an observer family retains precisely the old phantoms also missed by the added
stratum. -/
theorem observerPhantom_sum_iff {J : Type*} {Y : J → C}
    (π : ∀ i, X i ⟶ B) (κ : ∀ j, Y j ⟶ B) (χ : B ⟶ W) :
    ObserverPhantom (sumObserverFamily π κ) χ ↔
      ObserverPhantom π χ ∧ ObserverInvisible κ χ := by
  rw [ObserverPhantom, observerInvisible_sum_iff, ObserverPhantom]
  tauto

/-- One added observer that sees the old phantom charge removes that charge from the refined
phantom space. -/
theorem not_observerPhantom_sum_of_detected {J : Type*} {Y : J → C}
    (π : ∀ i, X i ⟶ B) (κ : ∀ j, Y j ⟶ B) (χ : B ⟶ W)
    (hdetect : ∃ j, κ j ≫ χ ≠ 0) :
    ¬ ObserverPhantom (sumObserverFamily π κ) χ := by
  rintro ⟨-, hinvisible⟩
  obtain ⟨j, hj⟩ := hdetect
  exact hj (hinvisible (.inr j))

/-- The zero global charge is invisible to every observer family. -/
theorem observerInvisible_zero (π : ∀ i, X i ⟶ B) :
    ObserverInvisible π (0 : B ⟶ W) := by
  intro i
  simp

/-- Observer invisibility is preserved by postprocessing the global charge. -/
theorem ObserverInvisible.postcomp
    {π : ∀ i, X i ⟶ B} {χ : B ⟶ W}
    (hχ : ObserverInvisible π χ) (f : W ⟶ Z) :
    ObserverInvisible π (χ ≫ f) := by
  intro i
  rw [← Category.assoc, hχ i, Limits.zero_comp]

/-- Universal effective observer descent forbids a nonzero globally surviving charge that is zero
on every observer. -/
theorem no_observerPhantom_of_universallyEffective
    (π : ∀ i, X i ⟶ B)
    (hπ : UniversallyEffective (Sieve.ofArrows X π))
    (χ : B ⟶ W) :
    ¬ ObserverPhantom π χ := by
  rintro ⟨hχ, hlocal⟩
  apply hχ
  apply universalEffectiveFamily_hom_ext π hπ χ 0
  intro i
  simpa [ObserverInvisible] using hlocal i

/-- One observer phantom is an exact obstruction certificate against universal effectivity. -/
theorem observerPhantom_not_universallyEffective
    (π : ∀ i, X i ⟶ B) (χ : B ⟶ W)
    (hχ : ObserverPhantom π χ) :
    ¬ UniversallyEffective (Sieve.ofArrows X π) := by
  exact not_universalEffective_of_parallel_not_separated π χ 0 hχ.1
    (fun i => by simpa [ObserverInvisible] using hχ.2 i)

end HTGeometry.NomologicalHomotopyGeometry.ObserverDescent

namespace HTGeometry.NomologicalHomotopyGeometry.SectionObserverDescent

universe u₁ u₂ u₃ u₄

variable {I : Type u₁} {X : I → Type u₂} {B : Type u₃} {W : Type u₄}

/-- Point-observer domains after adjoining a second observer stratum. -/
def SumSectionObserverObject {J : Type u₁}
    (X : I → Type u₂) (Y : J → Type u₂) : I ⊕ J → Type u₂
  | .inl i => X i
  | .inr j => Y j

/-- Point-observer family obtained by adjoining a second stratum. -/
def sumSectionObserverFamily {J : Type u₁} {Y : J → Type u₂}
    (π : ∀ i, X i → B) (κ : ∀ j, Y j → B) :
    ∀ s, SumSectionObserverObject X Y s → B
  | .inl i => π i
  | .inr j => κ j

/-- A global section is invisible when its restriction along every point observer is the
distinguished zero value. -/
def SectionObserverInvisible
    (π : ∀ i, X i → B) (zero : W) (χ : B → W) : Prop :=
  ∀ i x, χ (π i x) = zero

/-- A nonzero global section invisible on every point observer. -/
def SectionObserverPhantom
    (π : ∀ i, X i → B) (zero : W) (χ : B → W) : Prop :=
  χ ≠ (fun _ => zero) ∧ SectionObserverInvisible π zero χ

/-- A section is invisible to a sum of observer strata exactly when both strata miss it. -/
theorem sectionObserverInvisible_sum_iff {J : Type u₁} {Y : J → Type u₂}
    (π : ∀ i, X i → B) (κ : ∀ j, Y j → B) (zero : W) (χ : B → W) :
    SectionObserverInvisible (sumSectionObserverFamily π κ) zero χ ↔
      SectionObserverInvisible π zero χ ∧ SectionObserverInvisible κ zero χ := by
  constructor
  · intro h
    exact ⟨fun i x => h (.inl i) x, fun j y => h (.inr j) y⟩
  · rintro ⟨hπ, hκ⟩ (i | j) x
    · exact hπ i x
    · exact hκ j x

/-- Refining a point-observer family retains precisely the old section phantoms also missed by the
added stratum. -/
theorem sectionObserverPhantom_sum_iff {J : Type u₁} {Y : J → Type u₂}
    (π : ∀ i, X i → B) (κ : ∀ j, Y j → B) (zero : W) (χ : B → W) :
    SectionObserverPhantom (sumSectionObserverFamily π κ) zero χ ↔
      SectionObserverPhantom π zero χ ∧ SectionObserverInvisible κ zero χ := by
  rw [SectionObserverPhantom, sectionObserverInvisible_sum_iff,
    SectionObserverPhantom]
  tauto

/-- One added point observer that sees an old section phantom removes that section from the
refined phantom space. -/
theorem not_sectionObserverPhantom_sum_of_detected
    {J : Type u₁} {Y : J → Type u₂}
    (π : ∀ i, X i → B) (κ : ∀ j, Y j → B) (zero : W) (χ : B → W)
    (hdetect : ∃ j y, χ (κ j y) ≠ zero) :
    ¬ SectionObserverPhantom (sumSectionObserverFamily π κ) zero χ := by
  rintro ⟨-, hinvisible⟩
  obtain ⟨j, y, hj⟩ := hdetect
  exact hj (hinvisible (.inr j) y)

/-- A jointly surjective point-observer family admits no section phantom. -/
theorem no_sectionObserverPhantom_of_jointlySurjective
    (π : ∀ i, X i → B)
    (hπ : ∀ b, ∃ i x, π i x = b)
    (zero : W) (χ : B → W) :
    ¬ SectionObserverPhantom π zero χ := by
  rintro ⟨hχ, hlocal⟩
  apply hχ
  funext b
  obtain ⟨i, x, rfl⟩ := hπ b
  exact hlocal i x

/-- A section phantom certifies failure of joint point coverage. -/
theorem sectionObserverPhantom_not_jointlySurjective
    (π : ∀ i, X i → B) (zero : W) (χ : B → W)
    (hχ : SectionObserverPhantom π zero χ) :
    ¬ ∀ b, ∃ i x, π i x = b := by
  intro hπ
  exact no_sectionObserverPhantom_of_jointlySurjective π hπ zero χ hχ

end HTGeometry.NomologicalHomotopyGeometry.SectionObserverDescent
