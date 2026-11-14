import GaloisForLFunctions.RepresentationLifting.CyclicProductRepresentation
import GaloisForLFunctions.RepresentationLifting.PermutationCohomologyTrace
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Projectivity and trace for a pair of regular representations

A product of two projective representations is projective. The scalar trace of
an endomorphism of a product is the sum of its two diagonal-block traces.
For a regular pair, both diagonal blocks are equivariant regular endomorphisms,
so every trace vanishes when the group order is zero in the coefficient field.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.RepresentationLifting
universe u


/-- Two equivariant lifts combine to give projectivity of a product representation. -/
theorem representation_product_projective {k G : Type u} [CommRing k] [Monoid G]
    (A B : Rep.{u} k G) [Projective A] [Projective B] :
    Projective (Rep.of (A.ρ.prod B.ρ)) where
  factors := by
    intro E X f e he
    let i₁ : A ⟶ Rep.of (A.ρ.prod B.ρ) := Rep.ofHom (Representation.IntertwiningMap.inl k A.ρ B.ρ)
    let i₂ : B ⟶ Rep.of (A.ρ.prod B.ρ) := Rep.ofHom (Representation.IntertwiningMap.inr k A.ρ B.ρ)
    let p₁ : Rep.of (A.ρ.prod B.ρ) ⟶ A := Rep.ofHom (Representation.IntertwiningMap.fst k A.ρ B.ρ)
    let p₂ : Rep.of (A.ρ.prod B.ρ) ⟶ B := Rep.ofHom (Representation.IntertwiningMap.snd k A.ρ B.ρ)
    obtain ⟨s₁, hs₁⟩ := Projective.factors (i₁ ≫ f) e
    obtain ⟨s₂, hs₂⟩ := Projective.factors (i₂ ≫ f) e
    refine ⟨p₁ ≫ s₁ + p₂ ≫ s₂, ?_⟩
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, hs₁, hs₂]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change f.hom (v.1, 0) + f.hom (0, v.2) = f.hom v
    rw [← map_add]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _)

/-- The scalar trace of an arbitrary block endomorphism is the sum of its diagonal traces. -/
theorem trace_product_diagonal {k V W : Type*} [Field k]
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (T : Module.End k (V × W)) :
    LinearMap.trace k (V × W) T =
      LinearMap.trace k V ((LinearMap.fst k V W).comp (T.comp (LinearMap.inl k V W))) +
        LinearMap.trace k W ((LinearMap.snd k V W).comp (T.comp (LinearMap.inr k V W))) := by
  have hT : T = (LinearMap.inl k V W).comp ((LinearMap.fst k V W).comp T) +
      (LinearMap.inr k V W).comp ((LinearMap.snd k V W).comp T) := by
    apply LinearMap.ext
    intro v
    change T v = ((T v).1, 0) + (0, (T v).2)
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  calc
    LinearMap.trace k (V × W) T =
        LinearMap.trace k (V × W) ((LinearMap.inl k V W).comp ((LinearMap.fst k V W).comp T)) +
          LinearMap.trace k (V × W) ((LinearMap.inr k V W).comp ((LinearMap.snd k V W).comp T)) := by
      conv_lhs => rw [hT]
      rw [map_add]
    _ = _ := by
      rw [LinearMap.trace_comp_comm' ((LinearMap.fst k V W).comp T) (LinearMap.inl k V W),
        LinearMap.trace_comp_comm' ((LinearMap.snd k V W).comp T) (LinearMap.inr k V W)]
      rfl

variable (k G : Type u) [Field k] [CommGroup G] [Fintype G]

omit [Fintype G] in
/-- A pair of regular representations is projective over every coefficient field. -/
theorem cyclicRegularPair_projective : Projective (Rep.of (cyclicRegularPairRepresentation k G)) :=
  representation_product_projective (Rep.leftRegular k G) (Rep.leftRegular k G)

/-- Every endomorphism of the regular pair is traceless when the group order vanishes. -/
theorem cyclicRegularPair_endomorphism_trace (hcard : (Fintype.card G : k) = 0)
    (T : Rep.of (cyclicRegularPairRepresentation k G) ⟶ Rep.of (cyclicRegularPairRepresentation k G)) :
    LinearMap.trace k (CyclicDetector k G) T.hom.toLinearMap = 0 := by
  let A : Rep.leftRegular k G ⟶ Rep.leftRegular k G :=
    Rep.ofHom (Representation.IntertwiningMap.inl k (Rep.leftRegular k G).ρ (Rep.leftRegular k G).ρ) ≫
      T ≫ Rep.ofHom (Representation.IntertwiningMap.fst k (Rep.leftRegular k G).ρ (Rep.leftRegular k G).ρ)
  let B : Rep.leftRegular k G ⟶ Rep.leftRegular k G :=
    Rep.ofHom (Representation.IntertwiningMap.inr k (Rep.leftRegular k G).ρ (Rep.leftRegular k G).ρ) ≫
      T ≫ Rep.ofHom (Representation.IntertwiningMap.snd k (Rep.leftRegular k G).ρ (Rep.leftRegular k G).ρ)
  have hA := transitivePermutationEndomorphism_trace A (1 : G)
  have hB := transitivePermutationEndomorphism_trace B (1 : G)
  rw [hcard, zero_mul] at hA hB
  rw [trace_product_diagonal]
  change LinearMap.trace k (CyclicRegular k G) A.hom.toLinearMap +
    LinearMap.trace k (CyclicRegular k G) B.hom.toLinearMap = 0
  rw [hA, hB, add_zero]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicRegularPair_projective
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicRegularPair_endomorphism_trace
