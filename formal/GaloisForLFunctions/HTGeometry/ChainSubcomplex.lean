import GaloisForLFunctions.HTGeometry.SubspaceChains
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Subcomplexes of a chain complex of modules

A degreewise submodule of a chain complex of modules, stable under the differential, is again a
chain complex, and the inclusions assemble into a map of chain complexes.  Three families of
examples are used throughout: the chains supported in a subset of a space, the chains that are small
for a family of subsets, and — inside one of those — the chains supported in a smaller subset.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

universe v

/-- A degreewise submodule of a chain complex of modules, stable under the differential. -/
structure ModuleSubcomplex (R : Type) [CommRing R] (K : ChainComplex (ModuleCat.{v} R) ℕ) where
  /-- The submodule in each degree. -/
  carrier : ∀ k, Submodule R (K.X k)
  /-- The differential of an element of the submodule stays in the submodule. -/
  bd_mem : ∀ (k : ℕ) (x : K.X (k + 1)), x ∈ carrier (k + 1) → (K.d (k + 1) k) x ∈ carrier k

variable {R : Type} [CommRing R]

theorem chain_d_d_apply (K : ChainComplex (ModuleCat.{v} R) ℕ) (k : ℕ) (x : K.X (k + 2)) :
    (K.d (k + 1) k) ((K.d (k + 2) (k + 1)) x) = 0 := by
  have h := K.d_comp_d (k + 2) (k + 1) k
  have h2 := congrArg (fun φ : K.X (k + 2) ⟶ K.X k => ModuleCat.Hom.hom φ x) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h2
  exact h2

namespace ModuleSubcomplex

variable {K : ChainComplex (ModuleCat.{v} R) ℕ}

/-- The differential, restricted to the subcomplex. -/
noncomputable def d (P : ModuleSubcomplex R K) (k : ℕ) :
    ModuleCat.of R (P.carrier (k + 1)) ⟶ ModuleCat.of R (P.carrier k) :=
  ModuleCat.ofHom (((K.d (k + 1) k).hom).restrict (fun x hx => P.bd_mem k x hx))

/-- The chain complex of a differential-stable degreewise submodule. -/
noncomputable def complex (P : ModuleSubcomplex R K) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of R (P.carrier k)) P.d (by
    intro k
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact chain_d_d_apply K k _)

theorem complex_d (P : ModuleSubcomplex R K) (k : ℕ) : P.complex.d (k + 1) k = P.d k :=
  ChainComplex.of_d (fun k => ModuleCat.of R (P.carrier k)) P.d k

/-- The inclusion of a subcomplex. -/
noncomputable def incl (P : ModuleSubcomplex R K) : P.complex ⟶ K where
  f k := ModuleCat.ofHom (P.carrier k).subtype
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    rw [complex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

end ModuleSubcomplex

/-! ### Subcomplexes of the singular chain complex -/

variable {X : Type v} [TopologicalSpace X]

/-- The chains supported in a subset. -/
noncomputable def subcomplexOfSubset (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]
    (S : Set X) : ModuleSubcomplex R (singChainComplex R X) where
  carrier k := subChains R S k
  bd_mem _ _ hc := singBd_mem_subChains R hc

/-- The chains that are small for a family of subsets. -/
def smallSubmodule (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]
    (𝒰 : Set (Set X)) (k : ℕ) : Submodule R (C(topSimplex k, X) →₀ R) where
  carrier := {c | SmallChain R 𝒰 c}
  add_mem' hc hd := smallChain_add R hc hd
  zero_mem' := smallChain_zero R 𝒰
  smul_mem' r _ hc := smallChain_smul R r hc

theorem mem_smallSubmodule {𝒰 : Set (Set X)} {k : ℕ} {c : C(topSimplex k, X) →₀ R} :
    c ∈ smallSubmodule R 𝒰 k ↔ SmallChain R 𝒰 c := Iff.rfl

/-- The chains small for a family of subsets. -/
noncomputable def subcomplexOfFamily (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]
    (𝒰 : Set (Set X)) : ModuleSubcomplex R (singChainComplex R X) where
  carrier k := smallSubmodule R 𝒰 k
  bd_mem _ _ hc := smallChain_singBd R hc

theorem subcomplexOfFamily_pair_carrier (R : Type) [CommRing R] (A B : Set X) (k : ℕ) :
    (subcomplexOfFamily R ({A, B} : Set (Set X))).carrier k
      = subChains R A k ⊔ subChains R B k := by
  ext c
  exact smallChain_pair_iff R A B c

end GaloisForLFunctions.HTGeometry
