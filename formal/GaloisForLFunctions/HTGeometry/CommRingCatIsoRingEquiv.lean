import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Ring equivalence underlying a categorical commutative-ring isomorphism

This supplies the missing carrier-level dictionary for an arbitrary isomorphism in
`CommRingCat`; unlike specialized isomorphisms whose source is syntactically `CommRingCat.of R`,
an isomorphism between section objects does not expose a `.toRingEquiv` projection directly.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

/-- The ring equivalence carried by an isomorphism in `CommRingCat`. -/
noncomputable def commRingCatIsoRingEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : CommRingCat.of R ≅ CommRingCat.of S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom
    (by
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom e.inv_hom_id)
    (by
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom e.hom_inv_id)

@[simp]
theorem commRingCatIsoRingEquiv_apply {R S : Type u} [CommRing R] [CommRing S]
    (e : CommRingCat.of R ≅ CommRingCat.of S) (r : R) :
    commRingCatIsoRingEquiv e r = e.hom.hom r :=
  rfl

@[simp]
theorem commRingCatIsoRingEquiv_symm_apply {R S : Type u} [CommRing R] [CommRing S]
    (e : CommRingCat.of R ≅ CommRingCat.of S) (s : S) :
    (commRingCatIsoRingEquiv e).symm s = e.inv.hom s :=
  rfl

end GaloisForLFunctions.HTGeometry
