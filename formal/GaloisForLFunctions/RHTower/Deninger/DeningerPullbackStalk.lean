import GaloisForLFunctions.RHTower.Deninger.DeningerResidueStalk
import GaloisForLFunctions.RHTower.Deninger.DeningerSheafPullbackExact

/-!
# Stalks of an inverse image, and the support of the pulled back residue sheaf

The inverse image of a sheaf has, at a point, the stalk of the original sheaf at the image point:
the inverse image of sheaves is the sheafification of the inverse image of presheaves, and neither
step changes stalks.  Applied to the direct sum of skyscrapers along a finite set of primes, this
says the inverse image is `ℤ` on the preimage of a prime and zero off it — the extension by zero of
`ℤ` from that preimage — and the supports for distinct primes are disjoint.

* `deningerSheafPullbackStalkIso` : the stalk of an inverse image.
* `deningerPullbackResidueStalk_isZero`, `deningerPullbackResidueStalk_iso` : the support of the
  pulled back residue sheaf.
* `deningerPullbackSupport_disjoint` : the supports are pairwise disjoint.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

/-- **The stalk of an inverse image of sheaves** is the stalk at the image point. -/
noncomputable def deningerSheafPullbackStalkIso {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} Y) (x : X) :
    TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F).1 x ≅
      TopCat.Presheaf.stalk F.1 ((ConcreteCategory.hom f) x) := by
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{0}
    ((TopCat.Presheaf.pullback AddCommGrpCat.{0} f).obj F.1)
  exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapIso
      ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).mapIso
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{0} f).app F)) ≪≫
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback AddCommGrpCat.{0} f).obj F.1)))).symm ≪≫
    (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{0} f F.1 x).symm

/-- The preimage of a closed point of the arithmetic curve: the support of the pulled back
skyscraper. -/
def deningerPullbackSupport {X : TopCat.{0}} (a : X ⟶ deningerArithBase) (p : Nat.Primes) :
    Set X :=
  {x : X | (ConcreteCategory.hom a) x = deningerClosedPt p}

/-- **The supports of distinct primes are disjoint.** -/
theorem deningerPullbackSupport_disjoint {X : TopCat.{0}} (a : X ⟶ deningerArithBase)
    {p q : Nat.Primes} (hpq : p ≠ q) :
    Disjoint (deningerPullbackSupport a p) (deningerPullbackSupport a q) := by
  refine Set.disjoint_left.2 (fun x hx hx' => hpq ?_)
  exact deningerClosedPt_injective (hx.symm.trans hx')

/-- **The pulled back residue sheaf vanishes off the preimages of the primes of `P`.** -/
theorem deningerPullbackResidueStalk_isZero {X : TopCat.{0}} (a : X ⟶ deningerArithBase)
    (P : Finset Nat.Primes) (x : X)
    (hx : ∀ p ∈ P, x ∉ deningerPullbackSupport a p) :
    IsZero (TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback AddCommGrpCat.{0} a).obj
      (deningerResidueAddSheaf P ℤ)).1 x) := by
  refine IsZero.of_iso ?_ (deningerSheafPullbackStalkIso a (deningerResidueAddSheaf P ℤ) x)
  exact deningerResidueStalk_isZero P _ (fun p hp => hx p hp)

/-- **The pulled back residue sheaf is `ℤ` on the preimage of a prime of `P`.** -/
noncomputable def deningerPullbackResidueStalk_iso {X : TopCat.{0}} (a : X ⟶ deningerArithBase)
    (P : Finset Nat.Primes) {p : Nat.Primes} (hp : p ∈ P) (x : X)
    (hx : x ∈ deningerPullbackSupport a p) :
    TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback AddCommGrpCat.{0} a).obj
      (deningerResidueAddSheaf P ℤ)).1 x ≅ AddCommGrpCat.of ℤ := by
  haveI : IsIso (deningerResidueStalkDesc P hp) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    exact deningerResidueStalk_bijective P hp
  refine deningerSheafPullbackStalkIso a (deningerResidueAddSheaf P ℤ) x ≪≫ ?_
  refine (eqToIso ?_) ≪≫ asIso (deningerResidueStalkDesc P hp)
  rw [hx]
  rfl

end RHTower
