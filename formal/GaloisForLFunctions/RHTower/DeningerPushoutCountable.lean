import GaloisForLFunctions.RHTower.DeningerPushoutDecomp
import GaloisForLFunctions.RHTower.DeningerAmalgamCyclic

/-!
# An amalgam of countable groups is countable

Every element of an amalgam is the product of a word of letters, an element of the base group being
the product of a one letter word, so the product map from lists of letters is surjective and the
amalgam is countable whenever the index type and the factors are.

* `deningerPushoutI_countable` : countability of an amalgam.
* `deningerRootAdjunction_countable` : countability of a root adjunction.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **An amalgam of countable groups over a countable base is countable.** -/
theorem deningerPushoutI_countable [Nonempty ι] [Countable ι] [∀ i, Countable (G i)]
    (hφ : ∀ i, Function.Injective (φ i)) : Countable (PushoutI φ) := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty φ hφ
  have hsurj : Function.Surjective
      (fun L : List (Σ i, G i) => deningerLetterProd (φ := φ) L) := by
    intro w
    rcases deningerExists_letterProd (d := d) w with ⟨h₀, hw, -⟩ | ⟨L, -, -, -, -, hw⟩
    · obtain ⟨i⟩ := ‹Nonempty ι›
      refine ⟨[(⟨i, φ i h₀⟩ : Σ i, G i)], ?_⟩
      show deningerLetterProd (φ := φ) [(⟨i, φ i h₀⟩ : Σ i, G i)] = w
      rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one, PushoutI.of_apply_eq_base, hw]
    · exact ⟨L, hw.symm⟩
  exact hsurj.countable

namespace RootAdjunction

universe u

/-- **A root adjunction of a countable group is countable.** -/
theorem deningerRootAdjunction_countable (A : Type u) [Group A] [Countable A] (a : A) (m : ℤ)
    (hm : m ≠ 0) (ha : ∀ n : ℤ, a ^ n = 1 → n = 0) :
    Countable (PushoutI (deningerRootMap A a m)) := by
  have hfac : ∀ i, Countable (deningerRootFactor A i) := by
    rintro ⟨b⟩
    cases b
    · have : Countable (Multiplicative ℤ) := Countable.of_equiv ℤ Multiplicative.ofAdd
      exact instCountableULift
    · exact inferInstanceAs (Countable A)
  exact deningerPushoutI_countable (G := deningerRootFactor A)
    (deningerRootMap_injective A a m hm ha)

end RootAdjunction

end RHTower
