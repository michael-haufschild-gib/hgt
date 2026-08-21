import GaloisForLFunctions.HTGeometry.RelativeSingularHomology

/-!
# Functoriality of the singular chain complex

Postcomposition with a continuous map sends singular simplices to singular simplices and commutes
with the faces, so it induces a map of singular chain complexes, functorially.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X Y Z : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The map on singular chains induced by a continuous map. -/
noncomputable def singMapHom (f : C(Y, X)) (k : ℕ) :
    (C(topSimplex k, Y) →₀ R) →ₗ[R] (C(topSimplex k, X) →₀ R) :=
  Finsupp.lmapDomain R R (fun σ => f.comp σ)

theorem singMapHom_single (f : C(Y, X)) (k : ℕ) (σ : C(topSimplex k, Y)) (r : R) :
    singMapHom R f k (Finsupp.single σ r) = Finsupp.single (f.comp σ) r :=
  Finsupp.mapDomain_single

theorem singBd_singMapHom (f : C(Y, X)) (k : ℕ) (c : C(topSimplex (k + 1), Y) →₀ R) :
    singBd R X k (singMapHom R f (k + 1) c) = singMapHom R f k (singBd R Y k c) := by
  have hmap : (singBd R X k).comp (singMapHom R f (k + 1))
      = (singMapHom R f k).comp (singBd R Y k) := by
    refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
    show singBd R X k (singMapHom R f (k + 1) (Finsupp.single σ (1 : R)))
        = singMapHom R f k (singBd R Y k (Finsupp.single σ (1 : R)))
    rw [singMapHom_single, singBd_single, singBd_single, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [singMapHom_single, ContinuousMap.comp_assoc]
  exact LinearMap.congr_fun hmap c

/-- The chain map induced by a continuous map. -/
noncomputable def singMap (f : C(Y, X)) : singChainComplex R Y ⟶ singChainComplex R X where
  f k := ModuleCat.ofHom (singMapHom R f k)
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    exact ModuleCat.hom_ext (LinearMap.ext fun c => singBd_singMapHom R f j c)

theorem singMap_f (f : C(Y, X)) (k : ℕ) :
    (singMap R f).f k = ModuleCat.ofHom (singMapHom R f k) := rfl

theorem singMap_id : singMap R (ContinuousMap.id X) = 𝟙 (singChainComplex R X) := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_)
  show singMapHom R (ContinuousMap.id X) k (Finsupp.single σ (1 : R)) = Finsupp.single σ 1
  rw [singMapHom_single]
  rfl

theorem singMap_comp (f : C(Z, Y)) (g : C(Y, X)) :
    singMap R (g.comp f) = singMap R f ≫ singMap R g := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_)
  show singMapHom R (g.comp f) k (Finsupp.single σ (1 : R))
      = singMapHom R g k (singMapHom R f k (Finsupp.single σ (1 : R)))
  rw [singMapHom_single, singMapHom_single, singMapHom_single, ContinuousMap.comp_assoc]

end GaloisForLFunctions.HTGeometry
