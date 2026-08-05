import GaloisForLFunctions.HTGeometry.ShilovSimplicialJoinSystem
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Cohomology of the simplicial boundary-join coefficient system

The ambient coefficients, the boundary-join subsystem, and their quotient are cosimplicial modules
over the nerve of the diagram.  Their alternating coface complexes form a short exact sequence of
cochain complexes, and therefore fit into a long exact cohomology sequence.

Main results:

* `ambientCosimplicial`, `joinCosimplicial`, `quotientCosimplicial`: the three coefficient
  systems as cosimplicial modules;
* `simplicialJoinCochainShortComplex_shortExact`: the short exact sequence of cochain complexes;
* `simplicialJoinConnecting`, `simplicialJoin_homology_exact₁`,
  `simplicialJoin_homology_exact₂`, `simplicialJoin_homology_exact₃`: the long exact cohomology
  sequence of the boundary-join coefficient system.
-/

open CategoryTheory Opposite Simplicial AlgebraicTopology

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {C : Type v} [Category.{v} C]
variable (F : C ⥤ ModuleCat.{v} 𝕜)

/-- Cochains of simplicial degree `p`: the product over `p`-simplices of the coefficient at the
terminal vertex. -/
abbrev SimplexCochain (p : ℕ) : Type v :=
  ∀ σ : ComposableArrows C p, F.obj (simplexTip σ)

/-- Action of a simplex map on cochains. -/
noncomputable def cochainTransport {n m : SimplexCategory} (θ : n ⟶ m) :
    SimplexCochain F n.len →ₗ[𝕜] SimplexCochain F m.len where
  toFun c τ := simplexTransport F θ τ (c ((nerve C).map θ.op τ))
  map_add' x y := by
    funext τ
    exact map_add (simplexTransport F θ τ) _ _
  map_smul' a x := by
    funext τ
    exact map_smul (simplexTransport F θ τ) a _

@[simp] theorem cochainTransport_apply {n m : SimplexCategory} (θ : n ⟶ m)
    (c : SimplexCochain F n.len) (τ : ComposableArrows C m.len) :
    cochainTransport F θ c τ = simplexTransport F θ τ (c ((nerve C).map θ.op τ)) :=
  rfl

theorem cochainTransport_id (n : SimplexCategory) :
    cochainTransport F (𝟙 n) = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  funext τ
  rw [cochainTransport_apply, simplexTransport_id]
  rfl

theorem cochainTransport_comp {n m k : SimplexCategory} (θ : n ⟶ m) (ψ : m ⟶ k) :
    (cochainTransport F ψ).comp (cochainTransport F θ) = cochainTransport F (θ ≫ ψ) := by
  refine LinearMap.ext fun c => ?_
  funext υ
  show simplexTransport F ψ υ
      (simplexTransport F θ ((nerve C).map ψ.op υ)
        (c ((nerve C).map θ.op ((nerve C).map ψ.op υ)))) =
    simplexTransport F (θ ≫ ψ) υ (c ((nerve C).map (θ ≫ ψ).op υ))
  rw [← simplexTransport_comp]
  rfl

/-- Ambient coefficients as a cosimplicial module over the nerve of the diagram. -/
noncomputable def ambientCosimplicial : CosimplicialObject (ModuleCat.{v} 𝕜) where
  obj n := ModuleCat.of 𝕜 (SimplexCochain F n.len)
  map θ := ModuleCat.ofHom (cochainTransport F θ)
  map_id n := by rw [cochainTransport_id]; rfl
  map_comp θ ψ := by rw [← cochainTransport_comp, ModuleCat.ofHom_comp]

variable (J : ∀ X : C, Submodule 𝕜 (F.obj X))

/-- Boundary-join cochains at a given simplicial degree. -/
noncomputable def joinCochain (p : ℕ) : Submodule 𝕜 (SimplexCochain F p) :=
  Submodule.pi Set.univ (fun σ => simplexJoin F J σ)

theorem mem_joinCochain {p : ℕ} (c : SimplexCochain F p) :
    c ∈ joinCochain F J p ↔ ∀ σ, c σ ∈ simplexJoin F J σ := by
  rw [joinCochain, Submodule.mem_pi]
  exact ⟨fun h σ => h σ (Set.mem_univ σ), fun h σ _ => h σ⟩

theorem joinCochain_le_comap {n m : SimplexCategory} (θ : n ⟶ m) :
    joinCochain F J n.len ≤
      Submodule.comap (cochainTransport F θ) (joinCochain F J m.len) := by
  intro c hc
  have hc' : ∀ σ, c σ ∈ simplexJoin F J σ := (mem_joinCochain F J c).mp hc
  refine Submodule.mem_comap.mpr ((mem_joinCochain F J _).mpr fun τ => ?_)
  rw [cochainTransport_apply]
  exact simplexJoin_map_le F J θ τ (Submodule.mem_map_of_mem (hc' _))

/-- The boundary-join subsystem as a cosimplicial module. -/
noncomputable def joinCosimplicial : CosimplicialObject (ModuleCat.{v} 𝕜) where
  obj n := ModuleCat.of 𝕜 (joinCochain F J n.len)
  map θ := ModuleCat.ofHom
    (LinearMap.restrict (cochainTransport F θ) (fun _ hx => joinCochain_le_comap F J θ hx))
  map_id n := by
    ext c x
    show cochainTransport F (𝟙 n) c.1 x = c.1 x
    rw [cochainTransport_id]
    rfl
  map_comp θ ψ := by
    ext c x
    show cochainTransport F (θ ≫ ψ) c.1 x =
      cochainTransport F ψ (cochainTransport F θ c.1) x
    rw [← cochainTransport_comp]
    rfl

/-- The quotient coefficient system as a cosimplicial module. -/
noncomputable def quotientCosimplicial : CosimplicialObject (ModuleCat.{v} 𝕜) where
  obj n := ModuleCat.of 𝕜 (SimplexCochain F n.len ⧸ joinCochain F J n.len)
  map θ := ModuleCat.ofHom
    (Submodule.mapQ _ _ (cochainTransport F θ) (joinCochain_le_comap F J θ))
  map_id n := by
    ext x
    show (Submodule.Quotient.mk (cochainTransport F (𝟙 n) x) :
      SimplexCochain F n.len ⧸ joinCochain F J n.len) = Submodule.Quotient.mk x
    rw [cochainTransport_id]
    rfl
  map_comp {_ _ k} θ ψ := by
    ext x
    show (Submodule.Quotient.mk (cochainTransport F (θ ≫ ψ) x) :
      SimplexCochain F k.len ⧸ joinCochain F J k.len) =
      Submodule.Quotient.mk (cochainTransport F ψ (cochainTransport F θ x))
    rw [← cochainTransport_comp]
    rfl

/-- Inclusion of the boundary-join subsystem into the ambient system. -/
noncomputable def joinInclusion : joinCosimplicial F J ⟶ ambientCosimplicial F where
  app n := ModuleCat.ofHom (joinCochain F J n.len).subtype
  naturality _ _ _ := rfl

/-- Projection of the ambient system onto the quotient system. -/
noncomputable def ambientProjection : ambientCosimplicial F ⟶ quotientCosimplicial F J where
  app n := ModuleCat.ofHom (joinCochain F J n.len).mkQ
  naturality _ _ _ := rfl

/-- The short complex of alternating coface cochain complexes attached to the boundary-join
coefficient system. -/
noncomputable def simplicialJoinCochainShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{v} 𝕜) ℕ) :=
  ShortComplex.mk
    ((alternatingCofaceMapComplex (ModuleCat.{v} 𝕜)).map (joinInclusion F J))
    ((alternatingCofaceMapComplex (ModuleCat.{v} 𝕜)).map (ambientProjection F J)) (by
      ext n c
      exact (Submodule.Quotient.mk_eq_zero _).mpr c.2)

theorem simplicialJoinCochainShortComplex_shortExact :
    (simplicialJoinCochainShortComplex F J).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro c
    constructor
    · intro hc
      exact ⟨⟨c, (Submodule.Quotient.mk_eq_zero _).mp hc⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).mpr y.2
  · exact Subtype.val_injective
  · exact Submodule.mkQ_surjective _

/-- Connecting homomorphism of the boundary-join long exact cohomology sequence. -/
noncomputable def simplicialJoinConnecting (n : ℕ) :
    (simplicialJoinCochainShortComplex F J).X₃.homology n ⟶
      (simplicialJoinCochainShortComplex F J).X₁.homology (n + 1) :=
  (simplicialJoinCochainShortComplex_shortExact F J).δ n (n + 1) rfl

theorem simplicialJoin_homology_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _
      (ShortComplex.ShortExact.δ_comp
        (simplicialJoinCochainShortComplex_shortExact F J) n (n + 1) rfl)).Exact :=
  ShortComplex.ShortExact.homology_exact₁ _ _ _ _

theorem simplicialJoin_homology_exact₂ (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (simplicialJoinCochainShortComplex F J).f n)
      (HomologicalComplex.homologyMap (simplicialJoinCochainShortComplex F J).g n)
      (by rw [← HomologicalComplex.homologyMap_comp,
        (simplicialJoinCochainShortComplex F J).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  ShortComplex.ShortExact.homology_exact₂ (simplicialJoinCochainShortComplex_shortExact F J) n

theorem simplicialJoin_homology_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _
      (ShortComplex.ShortExact.comp_δ
        (simplicialJoinCochainShortComplex_shortExact F J) n (n + 1) rfl)).Exact :=
  ShortComplex.ShortExact.homology_exact₃ _ _ _ _

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
