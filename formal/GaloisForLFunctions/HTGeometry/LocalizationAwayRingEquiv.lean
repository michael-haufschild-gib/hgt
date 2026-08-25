import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Transporting an away-localization through a ring equivalence

A ring equivalence carrying `f` to `g` induces a ring equivalence between the localizations away
from `f` and `g`.  This small transport lemma is used to identify concrete marked affine charts
after reindexing their polynomial coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An equivalence carrying the inverted element transports the away-localization.** -/
noncomputable def awayRingEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) {f : A} {g : B} (hfg : e f = g) :
    Localization.Away f ≃+* Localization.Away g :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers f) (T := Submonoid.powers g)
    (Localization.Away f) (Localization.Away g) e (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers hfg)

end GaloisForLFunctions.HTGeometry
