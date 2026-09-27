import GaloisForLFunctions.HTGeometry.AlgebraicGroupGenericPoint

/-!
# Points of a scheme over a field with values in local rings

Let `X` be a scheme over `Spec C` and `R` a local `C`-algebra.  An `R`-valued point of `X` over `C`
is the same as a point `x ∈ X` together with a local homomorphism `ψ : O_(X,x) → R` compatible with
the constants `C → O_(X,x)`.  This file packages that description as `stalkPoint x ψ` and proves:

* every `R`-point is a `stalkPoint` (at the image of the closed point);
* for fixed `x`, `stalkPoint x ψ` determines the local homomorphism `ψ`;
* two `stalkPoint`s agree only at the same point;
* reparametrisation along a map of `C`-algebras composes the homomorphism.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C : Type u} [Field C] (X : Over (Spec (.of C)))

/-- The constants `C → O_(X,x)` of the local ring at `x`. -/
def stalkConstants (x : X.left) : CommRingCat.of C ⟶ X.left.presheaf.stalk x :=
  (Scheme.ΓSpecIso (.of C)).inv ≫ (Spec (.of C)).presheaf.germ ⊤ (X.hom x) trivial ≫
    X.hom.stalkMap x

theorem fromSpecStalk_comp_hom (x : X.left) :
    X.left.fromSpecStalk x ≫ X.hom = Spec.map (stalkConstants X x) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

/-- The `R`-valued point through the local ring at `x` given by `ψ : O_(X,x) → R`. -/
def stalkPoint {R : Type u} [CommRing R] [Algebra C R] (x : X.left)
    (ψ : X.left.presheaf.stalk x ⟶ CommRingCat.of R)
    (hψ : stalkConstants X x ≫ ψ = CommRingCat.ofHom (algebraMap C R)) :
    algebraicPointSource (K := C) (R := R) ⟶ X :=
  Over.homMk (Spec.map ψ ≫ X.left.fromSpecStalk x) (by
    change (Spec.map ψ ≫ X.left.fromSpecStalk x) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap C R))
    rw [Category.assoc, fromSpecStalk_comp_hom, ← Spec.map_comp, hψ])

@[simp]
theorem stalkPoint_left {R : Type u} [CommRing R] [Algebra C R] (x : X.left)
    (ψ : X.left.presheaf.stalk x ⟶ CommRingCat.of R)
    (hψ : stalkConstants X x ≫ ψ = CommRingCat.ofHom (algebraMap C R)) :
    (stalkPoint X x ψ hψ).left = Spec.map ψ ≫ X.left.fromSpecStalk x := rfl

/-- Reparametrising a stalk point along a map of `C`-algebras composes its homomorphism. -/
theorem pointSourceMap_comp_stalkPoint {R S : Type u} [CommRing R] [CommRing S] [Algebra C R]
    [Algebra C S] (f : R →ₐ[C] S) (x : X.left) (ψ : X.left.presheaf.stalk x ⟶ CommRingCat.of R)
    (hψ : stalkConstants X x ≫ ψ = CommRingCat.ofHom (algebraMap C R)) :
    pointSourceMap f ≫ stalkPoint X x ψ hψ = stalkPoint X x (ψ ≫ CommRingCat.ofHom f.toRingHom)
      (by rw [← Category.assoc, hψ, ← CommRingCat.ofHom_comp]
          exact congrArg CommRingCat.ofHom (RingHom.ext f.commutes)) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map ψ ≫ X.left.fromSpecStalk x =
    Spec.map (ψ ≫ CommRingCat.ofHom f.toRingHom) ≫ X.left.fromSpecStalk x
  rw [Spec.map_comp, Category.assoc]

theorem stalkPoint_congr {R : Type u} [CommRing R] [Algebra C R] (x : X.left)
    {ψ₁ ψ₂ : X.left.presheaf.stalk x ⟶ CommRingCat.of R} (h : ψ₁ = ψ₂)
    (hψ₁ : stalkConstants X x ≫ ψ₁ = CommRingCat.ofHom (algebraMap C R))
    (hψ₂ : stalkConstants X x ≫ ψ₂ = CommRingCat.ofHom (algebraMap C R)) :
    stalkPoint X x ψ₁ hψ₁ = stalkPoint X x ψ₂ hψ₂ := by
  subst h
  rfl

variable {R : Type u} [CommRing R] [IsLocalRing R] [Algebra C R]

/-- **Every point with values in a local ring is a stalk point.** -/
theorem exists_eq_stalkPoint (p : algebraicPointSource (K := C) (R := R) ⟶ X) :
    ∃ (x : X.left) (ψ : X.left.presheaf.stalk x ⟶ CommRingCat.of R)
      (hψ : stalkConstants X x ≫ ψ = CommRingCat.ofHom (algebraMap C R)),
      IsLocalHom ψ.hom ∧ p = stalkPoint X x ψ hψ := by
  have hp : Spec.map (Scheme.stalkClosedPointTo p.left) ≫ X.left.fromSpecStalk _ = p.left :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p.left
  have hψ : stalkConstants X _ ≫ Scheme.stalkClosedPointTo p.left =
      CommRingCat.ofHom (algebraMap C R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpecStalk_comp_hom, ← Category.assoc, hp]
    exact Over.w p
  refine ⟨_, Scheme.stalkClosedPointTo p.left, hψ, inferInstance, ?_⟩
  apply Over.OverMorphism.ext
  exact hp.symm

/-- **Stalk points at a common point determine their local homomorphisms.** -/
theorem stalkPoint_injective {x : X.left} {ψ₁ ψ₂ : X.left.presheaf.stalk x ⟶ CommRingCat.of R}
    [IsLocalHom ψ₁.hom] [IsLocalHom ψ₂.hom]
    {hψ₁ : stalkConstants X x ≫ ψ₁ = CommRingCat.ofHom (algebraMap C R)}
    {hψ₂ : stalkConstants X x ≫ ψ₂ = CommRingCat.ofHom (algebraMap C R)}
    (h : stalkPoint X x ψ₁ hψ₁ = stalkPoint X x ψ₂ hψ₂) : ψ₁ = ψ₂ := by
  have h' := congrArg (SpecToEquivOfLocalRing X.left (CommRingCat.of R))
    (show (SpecToEquivOfLocalRing X.left (CommRingCat.of R)).symm ⟨x, ⟨ψ₁, inferInstance⟩⟩ =
      (SpecToEquivOfLocalRing X.left (CommRingCat.of R)).symm ⟨x, ⟨ψ₂, inferInstance⟩⟩ from
      congrArg CommaMorphism.left h)
  simp only [Equiv.apply_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and] at h'
  exact congrArg Subtype.val h'

/-- Stalk points agree only at a common point, with transported homomorphisms. -/
theorem stalkPoint_eq_stalkPoint {x y : X.left} {ψ₁ : X.left.presheaf.stalk x ⟶ CommRingCat.of R}
    {ψ₂ : X.left.presheaf.stalk y ⟶ CommRingCat.of R} [IsLocalHom ψ₁.hom] [IsLocalHom ψ₂.hom]
    {hψ₁ : stalkConstants X x ≫ ψ₁ = CommRingCat.ofHom (algebraMap C R)}
    {hψ₂ : stalkConstants X y ≫ ψ₂ = CommRingCat.ofHom (algebraMap C R)}
    (h : stalkPoint X x ψ₁ hψ₁ = stalkPoint X y ψ₂ hψ₂) :
    ∃ hxy : x = y, ψ₁ = (X.left.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ ψ₂ := by
  have h' := congrArg (SpecToEquivOfLocalRing X.left (CommRingCat.of R))
    (show (SpecToEquivOfLocalRing X.left (CommRingCat.of R)).symm ⟨x, ⟨ψ₁, inferInstance⟩⟩ =
      (SpecToEquivOfLocalRing X.left (CommRingCat.of R)).symm ⟨y, ⟨ψ₂, inferInstance⟩⟩ from
      congrArg CommaMorphism.left h)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, SpecToEquivOfLocalRing_eq_iff] at h'
  obtain ⟨hxy, hψ⟩ := h'
  exact ⟨hxy, hψ⟩

end

end GaloisForLFunctions.HTGeometry
