/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittFaithful
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittFunctoriality

/-!
# Hasse detection by the rational Witt functor

The rational Witt functor is a conservative local chart for commutative-ring morphisms:
Teichmüller points detect source elements, induced Witt maps detect ring maps, and the Witt
construction reflects injectivity.  These are categorical Hasse principles rather than
place-by-place arithmetic ones.
-/

namespace RHTower

open CategoryTheory

/-- Two source elements agree exactly when their rational-Witt Teichmüller representatives
agree. -/
theorem deningerCanonicalRationalWittTeichmuller_congr_hasse_iff
    {A : Type*} [CommRing A] (a b : A) :
    deningerCanonicalRationalWittTeichmuller a =
      deningerCanonicalRationalWittTeichmuller b ↔ a = b := by
  exact ⟨fun h => deningerCanonicalRationalWittTeichmuller_injective h, congrArg _⟩

/-- Two commutative-ring maps agree exactly when their induced rational-Witt maps agree. -/
theorem deningerCanonicalRationalWittMap_congr_hasse_iff
    {A B : Type*} [CommRing A] [CommRing B] (f g : A →+* B) :
    deningerCanonicalRationalWittMap f = deningerCanonicalRationalWittMap g ↔ f = g := by
  exact ⟨deningerCanonicalRationalWittMap_faithful, congrArg _⟩

/-- Ring maps are equivalent to the rational-Witt morphisms actually realized by the functor. -/
noncomputable def deningerCanonicalRationalWittMapHasseEquivRange
    (A B : Type*) [CommRing A] [CommRing B] :
    (A →+* B) ≃ Set.range (fun f : A →+* B => deningerCanonicalRationalWittMap f) :=
  Equiv.ofInjective _ (fun _ _ h => deningerCanonicalRationalWittMap_faithful h)

/-- The realized rational-Witt morphism equivalence evaluates by the induced Witt map. -/
@[simp] theorem deningerCanonicalRationalWittMapHasseEquivRange_apply
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (deningerCanonicalRationalWittMapHasseEquivRange A B f).1 =
      deningerCanonicalRationalWittMap f := rfl

/-- Teichmüller points alone are a complete pointwise Hasse test for equality of induced
rational-Witt maps. -/
theorem deningerCanonicalRationalWittMap_teichmuller_congr_hasse_iff
    {A B : Type*} [CommRing A] [CommRing B] (f g : A →+* B) :
    f = g ↔ ∀ a,
      deningerCanonicalRationalWittMap f
          (deningerCanonicalRationalWittTeichmuller a) =
        deningerCanonicalRationalWittMap g
          (deningerCanonicalRationalWittTeichmuller a) := by
  constructor
  · intro h
    subst g
    exact fun _ => rfl
  · intro h
    ext a
    apply deningerCanonicalRationalWittTeichmuller_injective
    simpa only [deningerCanonicalRationalWittMap_teichmuller] using h a

/-- Rational Witt passage reflects injectivity: an induced Witt map is injective exactly when its
source ring map is. -/
theorem deningerCanonicalRationalWittMap_injective_hasse_iff
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    Function.Injective (deningerCanonicalRationalWittMap f) ↔ Function.Injective f := by
  constructor
  · intro hW a b hab
    apply deningerCanonicalRationalWittTeichmuller_injective
    apply hW
    simp only [deningerCanonicalRationalWittMap_teichmuller, hab]
  · exact deningerCanonicalRationalWittMap_injective f

/-- Categorical form: equality of commutative-ring morphisms is reflected and detected by the
rational Witt functor. -/
theorem deningerRationalWittFunctor_map_congr_hasse_iff
    {A B : CommRingCat} (f g : A ⟶ B) :
    deningerRationalWittFunctor.map f = deningerRationalWittFunctor.map g ↔ f = g := by
  exact ⟨fun h => deningerRationalWittFunctor.map_injective h, congrArg _⟩

end RHTower
