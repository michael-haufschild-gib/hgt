import GaloisForLFunctions.HTGeometry.SubdivisionHomotopy
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Chains supported in a subset, and chains of a subspace

The chains of `X` whose simplices all have image in a subset `S` form a submodule stable under the
boundary.  Composing with the inclusion identifies the chains of the subspace `S` with exactly that
submodule: the map on simplices is injective, and a simplex of `X` with image in `S` is the
composite of the inclusion with a simplex of `S` because the corestriction of a continuous map to a
subset containing its image is continuous.

Two subsets give the decomposition used by Mayer–Vietoris: a chain is small for the pair `{A, B}`
exactly when it lies in the sum of the two submodules, and the intersection of the two submodules is
the submodule for `A ∩ B`.
-/

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- The chains of `X` supported in a subset. -/
def subChains (S : Set X) (k : ℕ) : Submodule R (C(topSimplex k, X) →₀ R) :=
  Finsupp.supported R R {σ : C(topSimplex k, X) | Set.range σ ⊆ S}

theorem mem_subChains {S : Set X} {k : ℕ} (c : C(topSimplex k, X) →₀ R) :
    c ∈ subChains R S k ↔ ∀ σ ∈ c.support, Set.range σ ⊆ S := by
  rw [subChains, Finsupp.mem_supported]
  exact ⟨fun h σ hσ => h (Finset.mem_coe.mpr hσ), fun h σ hσ => h σ (Finset.mem_coe.mp hσ)⟩

theorem smallChain_singleton_iff {S : Set X} {k : ℕ} (c : C(topSimplex k, X) →₀ R) :
    SmallChain R {S} c ↔ c ∈ subChains R S k := by
  rw [mem_subChains]
  constructor
  · intro h σ hσ
    obtain ⟨U, hU, hsub⟩ := h σ hσ
    rw [Set.mem_singleton_iff] at hU
    exact hU ▸ hsub
  · exact fun h σ hσ => ⟨S, rfl, h σ hσ⟩

theorem smallChain_pair_iff (A B : Set X) {k : ℕ} (c : C(topSimplex k, X) →₀ R) :
    SmallChain R {A, B} c ↔ c ∈ subChains R A k ⊔ subChains R B k := by
  rw [subChains, subChains, ← Finsupp.supported_union, Finsupp.mem_supported]
  constructor
  · intro h σ hσ
    obtain ⟨U, hU, hsub⟩ := h σ (Finset.mem_coe.mp hσ)
    rcases hU with rfl | rfl
    · exact Or.inl hsub
    · exact Or.inr hsub
  · intro h σ hσ
    rcases h (Finset.mem_coe.mpr hσ) with hA | hB
    · exact ⟨A, Or.inl rfl, hA⟩
    · exact ⟨B, Or.inr rfl, hB⟩

theorem subChains_inter (A B : Set X) (k : ℕ) :
    subChains R (A ∩ B) k = subChains R A k ⊓ subChains R B k := by
  rw [subChains, subChains, subChains, ← Finsupp.supported_inter]
  congr 1
  ext σ
  simp [Set.subset_inter_iff]

theorem subChains_mono {S T : Set X} (h : S ⊆ T) (k : ℕ) :
    subChains R S k ≤ subChains R T k := by
  intro c hc
  rw [mem_subChains] at hc ⊢
  exact fun σ hσ => (hc σ hσ).trans h

theorem singBd_mem_subChains {S : Set X} {k : ℕ} {c : C(topSimplex (k + 1), X) →₀ R}
    (hc : c ∈ subChains R S (k + 1)) : singBd R X k c ∈ subChains R S k := by
  rw [← smallChain_singleton_iff] at hc ⊢
  exact smallChain_singBd R hc

/-! ### Chains of a subspace -/

/-- A singular simplex of a subspace, read in the ambient space. -/
noncomputable def inclSimplex (S : Set X) {k : ℕ} (σ : C(topSimplex k, ↥S)) :
    C(topSimplex k, X) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, X)).comp σ

theorem inclSimplex_injective (S : Set X) {k : ℕ} :
    Function.Injective (inclSimplex S (k := k)) := by
  intro σ τ h
  refine ContinuousMap.ext fun x => ?_
  exact Subtype.ext (congrArg (fun f : C(topSimplex k, X) => f x) h)

theorem range_inclSimplex (S : Set X) {k : ℕ} (σ : C(topSimplex k, ↥S)) :
    Set.range (inclSimplex S σ) ⊆ S := by
  rintro _ ⟨x, rfl⟩
  exact (σ x).2

theorem exists_inclSimplex (S : Set X) {k : ℕ} {τ : C(topSimplex k, X)}
    (h : Set.range τ ⊆ S) : ∃ σ : C(topSimplex k, ↥S), inclSimplex S σ = τ :=
  ⟨⟨fun x => ⟨τ x, h ⟨x, rfl⟩⟩, Continuous.subtype_mk τ.continuous _⟩,
    ContinuousMap.ext fun _ => rfl⟩

theorem inclSimplex_comp (S : Set X) {k m : ℕ} (σ : C(topSimplex m, ↥S))
    (f : Fin (k + 1) → Fin (m + 1)) :
    inclSimplex S (σ.comp (topMap f)) = (inclSimplex S σ).comp (topMap f) := rfl

/-- The map on chains induced by the inclusion of a subspace. -/
noncomputable def subChainIncl (S : Set X) (k : ℕ) :
    (C(topSimplex k, ↥S) →₀ R) →ₗ[R] (C(topSimplex k, X) →₀ R) :=
  Finsupp.lmapDomain R R (inclSimplex S)

theorem subChainIncl_single (S : Set X) {k : ℕ} (σ : C(topSimplex k, ↥S)) (r : R) :
    subChainIncl R S k (Finsupp.single σ r) = Finsupp.single (inclSimplex S σ) r :=
  Finsupp.mapDomain_single

theorem subChainIncl_injective (S : Set X) (k : ℕ) :
    Function.Injective (subChainIncl R S k) :=
  Finsupp.mapDomain_injective (inclSimplex_injective S)

/-- The inclusion of a subspace is a chain map. -/
theorem subChainIncl_singBd (S : Set X) {k : ℕ} (c : C(topSimplex (k + 1), ↥S) →₀ R) :
    subChainIncl R S k (singBd R (↥S) k c) = singBd R X k (subChainIncl R S (k + 1) c) := by
  have hmap : (subChainIncl R S k).comp (singBd R (↥S) k)
      = (singBd R X k).comp (subChainIncl R S (k + 1)) := by
    refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
    show subChainIncl R S k (singBd R (↥S) k (Finsupp.single σ (1 : R)))
        = singBd R X k (subChainIncl R S (k + 1) (Finsupp.single σ (1 : R)))
    rw [singBd_single, map_sum, subChainIncl_single, singBd_single]
    exact Finset.sum_congr rfl fun i _ => by rw [subChainIncl_single, inclSimplex_comp]
  exact LinearMap.congr_fun hmap c

/-- **The chains of a subspace are exactly the chains supported in it.** -/
theorem range_subChainIncl (S : Set X) (k : ℕ) :
    LinearMap.range (subChainIncl R S k) = subChains R S k := by
  refine le_antisymm ?_ ?_
  · rintro c ⟨d, rfl⟩
    rw [mem_subChains]
    intro τ hτ
    obtain ⟨σ, _, hσ⟩ := support_linear_apply_subset R (subChainIncl R S k) d hτ
    rw [subChainIncl_single] at hσ
    have hτσ : τ = inclSimplex S σ := Finset.mem_singleton.mp (Finsupp.support_single_subset hσ)
    rw [hτσ]
    exact range_inclSimplex S σ
  · rw [subChains, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨σ, rfl⟩ := exists_inclSimplex S hτ
    exact ⟨Finsupp.single σ 1, Finsupp.mapDomain_single⟩

end GaloisForLFunctions.HTGeometry
