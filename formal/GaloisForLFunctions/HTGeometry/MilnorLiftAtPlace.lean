import GaloisForLFunctions.HTGeometry.MilnorLiftUniqueness

/-!
# The canonical lift of a residue class at a polynomial place

At the place of an irreducible `π`, every residue class is the residue of a **unique** nonzero
polynomial of degree below `deg π`.  That polynomial is the canonical lift, and Milnor's section is
built from it: the symbol `{lift ȳ₁, …, lift ȳ_{n}, π}` realises a class of the residue field with
no choices at all.

* `liftPoly` : the canonical lift.
* `liftPoly_ne_zero`, `liftPoly_natDegree_lt`, `liftPoly_residue` : its defining properties.
* `liftPoly_eq_of_residue_eq` : it is determined by the residue.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- The residue field at the place of an irreducible polynomial. -/
abbrev polyResidueField {π : Polynomial F} (hπ : Irreducible π) : Type _ :=
  IsLocalRing.ResidueField (((polyPlace hπ).valuation (RatFunc F)).valuationSubring)

/-- **The canonical lift**: the unique nonzero polynomial of degree below `deg π` with the given
residue. -/
noncomputable def liftPoly {π : Polynomial F} (hπ : Irreducible π)
    (y : (polyResidueField hπ)ˣ) : Polynomial F :=
  (exists_polyUnit_degree_lt hπ y).choose

theorem liftPoly_ne_zero {π : Polynomial F} (hπ : Irreducible π) (y : (polyResidueField hπ)ˣ) :
    liftPoly hπ y ≠ 0 :=
  (exists_polyUnit_degree_lt hπ y).choose_spec.choose

theorem liftPoly_natDegree_lt {π : Polynomial F} (hπ : Irreducible π)
    (y : (polyResidueField hπ)ˣ) : (liftPoly hπ y).natDegree < π.natDegree :=
  (exists_polyUnit_degree_lt hπ y).choose_spec.choose_spec.1

theorem liftPoly_residue {π : Polynomial F} (hπ : Irreducible π) (y : (polyResidueField hπ)ˣ) :
    (polyResidueData hπ).residueUnit (polyUnit (liftPoly_ne_zero hπ y)) = y :=
  (exists_polyUnit_degree_lt hπ y).choose_spec.choose_spec.2

/-- The canonical lift is determined by the residue. -/
theorem liftPoly_eq_of_residue_eq {π : Polynomial F} (hπ : Irreducible π)
    {p : Polynomial F} (hp : p ≠ 0) (hpd : p.natDegree < π.natDegree)
    {y : (polyResidueField hπ)ˣ}
    (h : (polyResidueData hπ).residueUnit (polyUnit hp) = y) : p = liftPoly hπ y :=
  polyUnit_degree_lt_unique hπ hp (liftPoly_ne_zero hπ y) hpd (liftPoly_natDegree_lt hπ y)
    (by rw [h, liftPoly_residue])

/-- Two polynomials of degree below `deg π` with the same residue are equal. -/
theorem eq_of_residue_eq {π : Polynomial F} (hπ : Irreducible π)
    {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpd : p.natDegree < π.natDegree) (hqd : q.natDegree < π.natDegree)
    (h : (polyResidueData hπ).residueUnit (polyUnit hp)
      = (polyResidueData hπ).residueUnit (polyUnit hq)) : p = q :=
  polyUnit_degree_lt_unique hπ hp hq hpd hqd h

end GaloisForLFunctions.HTGeometry
