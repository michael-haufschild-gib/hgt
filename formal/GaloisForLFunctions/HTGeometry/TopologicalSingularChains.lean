import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Topology.ContinuousMap.Basic

/-!
# The singular chain complex in the free module model

The singular `n`-simplices of a space are the continuous maps from the topological `n`-simplex, and
the singular chains are the free module on them.  The faces are precomposition with the affine
inclusions of the faces of the topological simplex, so the singular chains are the alternating face
map complex of the free module simplicial object on the singular simplices, and `∂ ∘ ∂ = 0` is
inherited from the simplicial identities.

This is the concrete model needed for barycentric subdivision: the subdivision operator is defined
by pushing forward affine chains along a singular simplex, which requires the chains to be presented
as formal combinations of actual maps.
-/

open CategoryTheory Simplicial AlgebraicTopology Opposite

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- The topological `n`-simplex. -/
abbrev topSimplex (n : ℕ) : Type := stdSimplex ℝ (Fin (n + 1))

/-- The continuous map of topological simplices induced by a map of vertex sets. -/
noncomputable def topMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    C(topSimplex m, topSimplex n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

@[simp]
theorem topMap_apply {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (x : topSimplex m) (j : Fin (n + 1)) :
    (topMap f x : Fin (n + 1) → ℝ) j = ∑ i ∈ Finset.univ.filter (fun i => f i = j), (x : Fin (m + 1) → ℝ) i := by
  classical
  show FunOnFinite.linearMap ℝ ℝ f (x : Fin (m + 1) → ℝ) j = _
  rw [FunOnFinite.linearMap_apply_apply]

theorem topMap_id {n : ℕ} : topMap (id : Fin (n + 1) → Fin (n + 1)) = ContinuousMap.id _ :=
  ContinuousMap.ext fun x => stdSimplex.map_id_apply x

theorem topMap_comp {m n k : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (g : Fin (n + 1) → Fin (k + 1)) :
    (topMap g).comp (topMap f) = topMap (g ∘ f) :=
  ContinuousMap.ext fun x => stdSimplex.map_comp_apply f g x

variable (R : Type u) [CommRing R] (X : Type v) [TopologicalSpace X]

/-- The free `R`-module simplicial object on the singular simplices of a space. -/
noncomputable def singSimplicial : SimplicialObject (ModuleCat.{max u v} R) where
  obj n := ModuleCat.of R ((C(topSimplex n.unop.len, X)) →₀ R)
  map f := ModuleCat.ofHom
    (Finsupp.lmapDomain R R
      (fun σ => σ.comp (topMap (SimplexCategory.Hom.toOrderHom f.unop))))
  map_id := by
    intro n
    have hcm : topMap (⇑(SimplexCategory.Hom.toOrderHom (𝟙 n).unop))
        = ContinuousMap.id (topSimplex n.unop.len) := topMap_id
    have hfun : (fun τ : C(topSimplex n.unop.len, X) =>
        τ.comp (topMap ⇑(SimplexCategory.Hom.toOrderHom (𝟙 n).unop))) = _root_.id := by
      funext τ
      rw [hcm, ContinuousMap.comp_id]
      rfl
    refine ModuleCat.hom_ext ?_
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    rw [hfun]
    exact Finsupp.lmapDomain_id R R
  map_comp := by
    intro a b c f g
    have hord : (⇑(SimplexCategory.Hom.toOrderHom (f ≫ g).unop) :
          Fin (c.unop.len + 1) → Fin (a.unop.len + 1))
        = (⇑(SimplexCategory.Hom.toOrderHom f.unop)) ∘
            (⇑(SimplexCategory.Hom.toOrderHom g.unop)) := by
      funext i
      rfl
    have hcm : topMap (⇑(SimplexCategory.Hom.toOrderHom (f ≫ g).unop))
        = (topMap ⇑(SimplexCategory.Hom.toOrderHom f.unop)).comp
            (topMap ⇑(SimplexCategory.Hom.toOrderHom g.unop)) := by
      rw [hord, topMap_comp]
    have hfun : ∀ τ : C(topSimplex a.unop.len, X),
        τ.comp (topMap ⇑(SimplexCategory.Hom.toOrderHom (f ≫ g).unop))
          = (τ.comp (topMap ⇑(SimplexCategory.Hom.toOrderHom f.unop))).comp
              (topMap ⇑(SimplexCategory.Hom.toOrderHom g.unop)) := by
      intro τ
      rw [ContinuousMap.comp_assoc, hcm]
    refine ModuleCat.hom_ext ?_
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    rw [show (fun τ : C(topSimplex a.unop.len, X) =>
          τ.comp (topMap ⇑(SimplexCategory.Hom.toOrderHom (f ≫ g).unop)))
        = (fun τ : C(topSimplex b.unop.len, X) =>
            τ.comp (topMap ⇑(SimplexCategory.Hom.toOrderHom g.unop)))
          ∘ (fun τ : C(topSimplex a.unop.len, X) =>
            τ.comp (topMap ⇑(SimplexCategory.Hom.toOrderHom f.unop)))
        from funext hfun]
    exact Finsupp.lmapDomain_comp R R _ _

/-- The singular chain complex of a space with coefficients in `R`. -/
noncomputable def singChainComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  AlternatingFaceMapComplex.obj (singSimplicial R X)

theorem singChainComplex_X (n : ℕ) :
    (singChainComplex R X).X n = ModuleCat.of R ((C(topSimplex n, X)) →₀ R) := rfl

/-- The `i`-th face of a singular simplex is its restriction to the `i`-th face of the simplex. -/
theorem singSimplicial_δ {n : ℕ} (i : Fin (n + 2)) (σ : C(topSimplex (n + 1), X)) :
    (singSimplicial R X).δ i (Finsupp.single σ (1 : R))
      = Finsupp.single (σ.comp (topMap i.succAbove)) (1 : R) := by
  show Finsupp.mapDomain _ (Finsupp.single σ (1 : R)) = _
  rw [Finsupp.mapDomain_single]
  congr 1

/-- The boundary of a singular simplex is the alternating sum of its faces. -/
theorem sing_d_single {n : ℕ} (σ : C(topSimplex (n + 1), X)) :
    ((singChainComplex R X).d (n + 1) n).hom (Finsupp.single σ (1 : R))
      = ∑ i : Fin (n + 2), Finsupp.single (σ.comp (topMap i.succAbove)) ((-1 : R) ^ (i : ℕ)) := by
  show ((AlternatingFaceMapComplex.obj (singSimplicial R X)).d (n + 1) n).hom _ = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  show ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (singSimplicial R X).δ i :
      (singSimplicial R X) _⦋n + 1⦌ ⟶ (singSimplicial R X) _⦋n⦌)).hom (Finsupp.single σ 1) = _
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, singSimplicial_δ]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((-1 : ℤ) ^ (i : ℕ)) • (Finsupp.single (σ.comp (topMap i.succAbove)) (1 : R))
      = Finsupp.single (σ.comp (topMap i.succAbove)) ((-1 : R) ^ (i : ℕ))
  rw [Finsupp.smul_single]
  congr 1
  simp

/-- The singular boundary as a plain linear map. -/
noncomputable def singBd (k : ℕ) :
    (C(topSimplex (k + 1), X) →₀ R) →ₗ[R] (C(topSimplex k, X) →₀ R) :=
  ((singChainComplex R X).d (k + 1) k).hom

theorem singBd_single {k : ℕ} (σ : C(topSimplex (k + 1), X)) :
    singBd R X k (Finsupp.single σ (1 : R))
      = ∑ i : Fin (k + 2), Finsupp.single (σ.comp (topMap i.succAbove)) ((-1 : R) ^ (i : ℕ)) :=
  sing_d_single R X σ

theorem singBd_singBd {k : ℕ} (c : (C(topSimplex (k + 2), X) →₀ R)) :
    singBd R X k (singBd R X (k + 1) c) = 0 := by
  have h := (singChainComplex R X).d_comp_d (k + 2) (k + 1) k
  have h2 := congrArg
    (fun φ : (singChainComplex R X).X (k + 2) ⟶ (singChainComplex R X).X k =>
      ModuleCat.Hom.hom φ c) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h2
  exact h2

end GaloisForLFunctions.HTGeometry
