import GaloisForLFunctions.HTGeometry.BuildingLinkQuotient

/-!
# The subspaces that do not span with a fixed point form a contractible piece

Fix a nonzero proper subspace `p`.  The nonzero subspaces `U` whose join with `p` is still proper
form a conically contractible poset: the monotone map `U ↦ U ⊔ p` stays inside the family, dominates
the identity, and dominates the constant `p`.

This is the contractible piece of the Solomon--Tits decomposition of a building: everything that
fails to span together with `p` retracts onto `p`.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

variable {R : Type*} {M : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- The nonzero subspaces whose join with `p` is still proper. -/
def notSpanningPoset (p : Submodule R M) : Type u :=
  {U : Submodule R M // ⊥ < U ∧ U ⊔ p < ⊤}

instance (p : Submodule R M) : Preorder (notSpanningPoset p) :=
  Subtype.preorder _

/-- Joining with `p` stays inside the family. -/
def notSpanningJoin (p : Submodule R M) : notSpanningPoset p →o notSpanningPoset p where
  toFun U := ⟨U.1 ⊔ p, lt_of_lt_of_le U.2.1 le_sup_left, by
    rw [sup_assoc, sup_idem]
    exact U.2.2⟩
  monotone' U W h := by
    change U.1 ⊔ p ≤ W.1 ⊔ p
    exact sup_le_sup_right h p

/-- **The non-spanning family is conically contractible.** -/
theorem isZero_homology_notSpanningPoset {p : Submodule R M} (hp : ⊥ < p) (hp' : p < ⊤)
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (Rc : C) (n : ℕ) (hn : 1 ≤ n) :
    Limits.IsZero ((nerveFunctor.obj (Cat.of (notSpanningPoset p))).homology Rc n) := by
  refine isZero_homology_of_conical
    (⟨p, hp, by rw [sup_idem]; exact hp'⟩ : notSpanningPoset p)
    (notSpanningJoin p) (fun U => ?_) (fun U => ?_) Rc n hn
  · show U.1 ≤ U.1 ⊔ p
    exact le_sup_left
  · show p ≤ U.1 ⊔ p
    exact le_sup_right

end GaloisForLFunctions.HTGeometry
