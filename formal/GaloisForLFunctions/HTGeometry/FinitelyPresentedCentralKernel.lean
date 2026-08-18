import GaloisForLFunctions.HTGeometry.FinitePresentationIndependence
import GaloisForLFunctions.HTGeometry.RelationModuleFG

/-!
# Central extensions of finitely presented groups

A group is **finitely presented** when it is the quotient of a finitely generated free group by the
normal closure of finitely many relators; by `exists_finite_relators` this does not depend on the
chosen presentation.

The consequence that matters for `K`-theory: a **central** extension of a finitely presented group
by a finitely generated group has finitely generated kernel.  Applied to `St(R) ↠ E(R)` — whose
kernel is `K₂(R)`, central in the stable range — this reduces the finite generation of `K₂` of a
ring of integers to the finite presentability of its elementary group.

* `IsFinitelyPresented` : the definition.
* `isFinitelyPresented_relators` : relators are finite for *every* finitely generated free
  presentation.
* `fg_ker_of_central_of_isFinitelyPresented` : **the central-kernel theorem.**
-/

namespace GaloisForLFunctions.HTGeometry

universe u

/-- A group is **finitely presented** when it is a quotient of a finitely generated free group by
the normal closure of a finite set of relators. -/
def IsFinitelyPresented (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (ψ : FreeGroup (Fin n) →* G), Function.Surjective ψ ∧
    ∃ S : Set (FreeGroup (Fin n)), S.Finite ∧ ψ.ker = Subgroup.normalClosure S

/-- A finitely generated group is a quotient of a finitely generated free group. -/
theorem exists_freeGroup_surjection {G : Type u} [Group G] (hG : Group.FG G) :
    ∃ (X : Type u) (_ : Finite X) (ψ : FreeGroup X →* G), Function.Surjective ψ := by
  obtain ⟨T, hTtop, hTfin⟩ := Group.fg_iff.1 hG
  haveI : Finite T := hTfin.to_subtype
  refine ⟨↥T, inferInstance, FreeGroup.lift (fun t : T => (t : G)), ?_⟩
  rw [← MonoidHom.range_eq_top]
  refine top_le_iff.1 ?_
  rw [← hTtop]
  refine (Subgroup.closure_le _).2 fun t ht => ?_
  exact ⟨FreeGroup.of ⟨t, ht⟩, by simp⟩

/-- A finitely presented group is finitely generated. -/
theorem Group.fg_of_isFinitelyPresented {G : Type*} [Group G] (hG : IsFinitelyPresented G) :
    Group.FG G := by
  obtain ⟨n, ψ, hψ, -⟩ := hG
  haveI : Group.FG (FreeGroup (Fin n)) :=
    Group.fg_iff.2 ⟨Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)),
      FreeGroup.closure_range_of _, Set.finite_range _⟩
  exact Group.fg_of_surjective hψ

/-- **The relators are finite for every finitely generated free presentation.** -/
theorem isFinitelyPresented_relators {G : Type*} [Group G] (hG : IsFinitelyPresented G)
    {X : Type*} [Finite X] (ψ : FreeGroup X →* G) (hψ : Function.Surjective ψ) :
    ∃ S : Set (FreeGroup X), S.Finite ∧ ψ.ker = Subgroup.normalClosure S := by
  obtain ⟨n, ψ₁, hψ₁, S₁, hS₁, hker₁⟩ := hG
  exact exists_finite_relators ψ₁ ψ hψ₁ hψ hS₁ hker₁

/-- **A central extension of a finitely presented group by a finitely generated group has finitely
generated kernel.** -/
theorem fg_ker_of_central_of_isFinitelyPresented {G : Type u} {H : Type*} [Group G] [Group H]
    (hG : Group.FG G) (π : G →* H) (hπ : Function.Surjective π) (hH : IsFinitelyPresented H)
    (hcentral : π.ker ≤ Subgroup.center G) : Group.FG π.ker := by
  obtain ⟨X, hX, ψ, hψ⟩ := exists_freeGroup_surjection hG
  haveI := hX
  obtain ⟨S, hSfin, hker⟩ := isFinitelyPresented_relators hH (π.comp ψ) (hπ.comp hψ)
  exact fg_ker_of_central_extension S hSfin ψ hψ π hker.symm hcentral

end GaloisForLFunctions.HTGeometry
