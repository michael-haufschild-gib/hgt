import GaloisForLFunctions.RHTower.DeningerDynSysInvariantPoints
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Proposition 3.5 for an affine base

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 3.5, the
affine case, which is the case his proof reduces to.

For a ring `B` with a continuous action of a profinite group `G` and invariant subring `A`, the
`C`-valued points of `Spec B` map onto those of `Spec A`, with fibres exactly the `G`-orbits.
Under the equivalence between morphisms `Spec C → Spec R` and ring homomorphisms `R → C` this is
Kucharczyk–Scholze Lemma 4.9.
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type u} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
variable {C : Type u} [Field C]

/-- The structural morphism `Spec B → Spec A`. -/
noncomputable def deningerSpecStructure :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- **Deninger, Proposition 3.5, affine case, surjectivity.**  Every `C`-point of `Spec A` lifts
to a `C`-point of `Spec B`. -/
theorem deningerSpecPoint_surjective [Algebra.IsInvariant A B G] [FaithfulSMul A B]
    [IsAlgClosed C] :
    Function.Surjective (fun f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B) =>
      f ≫ deningerSpecStructure (A := A) (B := B)) := by
  intro g
  obtain ⟨ψ, hψ⟩ := deningerHom_restrict_surjective (A := A) (B := B) (G := G) (C := C)
    (Spec.preimage g).hom
  have hψ' : ψ.comp (algebraMap A B) = (Spec.preimage g).hom := hψ
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_⟩
  dsimp only
  rw [deningerSpecStructure, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom ψ
      = CommRingCat.ofHom (ψ.comp (algebraMap A B)) from rfl, hψ']
  exact Spec.map_preimage g

/-- **Deninger, Proposition 3.5, affine case, the fibres.**  Two `C`-points of `Spec B` lie over
the same point of `Spec A` exactly when they differ by an element of `G`. -/
theorem deningerSpecPoint_eq_iff [Algebra.IsInvariant A B G]
    (f₁ f₂ : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B)) :
    f₁ ≫ deningerSpecStructure (A := A) (B := B)
        = f₂ ≫ deningerSpecStructure (A := A) (B := B)
      ↔ ∃ g : G, ∀ b : B, (Spec.preimage f₂).hom b = (Spec.preimage f₁).hom (g • b) := by
  have hfac : ∀ f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B),
      f ≫ deningerSpecStructure (A := A) (B := B)
        = Spec.map (CommRingCat.ofHom (algebraMap A B) ≫ Spec.preimage f) := by
    intro f
    rw [Spec.map_comp, Spec.map_preimage, deningerSpecStructure]
  rw [hfac f₁, hfac f₂, Spec.map_injective.eq_iff]
  rw [← deningerHom_restrict_eq_iff (A := A) (B := B) (G := G)
    (Spec.preimage f₁).hom (Spec.preimage f₂).hom]
  constructor
  · intro h
    have := congrArg CommRingCat.Hom.hom h
    exact this
  · intro h
    refine CommRingCat.hom_ext ?_
    exact h

end RHTower
