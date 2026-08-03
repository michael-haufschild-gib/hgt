import GaloisForLFunctions.RHTower.DeningerFreeProductVanishing

/-!
# Induction from a trivial subgroup

A representation induced from a subgroup with one element has no homology in positive degrees,
whatever it is induced from: Shapiro's lemma moves the computation to the subgroup, where nothing
survives.  This is the edge side of the tree of a free product, where the edge stabilizers are
trivial.

* `deningerIsZero_ind_of_subsingleton` : the vanishing.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- **A representation induced from a trivial subgroup has no homology in positive degrees.** -/
theorem deningerIsZero_ind_of_subsingleton (k G : Type u) [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [Subsingleton S] (A : Rep.{u} k S) (n : ℕ) :
    IsZero (groupHomology (Rep.ind S.subtype A) (n + 1)) :=
  IsZero.of_iso (isZero_groupHomology_succ_of_subsingleton A n)
    (groupHomology.indIso S A (n + 1))

end RHTower
