import GaloisForLFunctions.HTGeometry.ShilovIdealCommutative
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.ContinuousMap.Star

/-!
# The commutative C*-envelope

Restriction to a closed boundary is a surjective `*`-homomorphism `C(X, ℂ) → C(F, ℂ)` whose kernel
is the vanishing ideal of `F` and which is isometric on `S`.  Taking `F` to be the Shilov boundary
gives the commutative C*-envelope of a function system: the smallest algebra of continuous
functions on which `S` keeps its norms.

* `norm_restrict_eq_of_isBoundarySet` — restriction is isometric on `S` exactly because `F` sees
  the whole norm;
* `restrictStarAlgHom_surjective` — surjectivity is Tietze extension;
* `ker_restrict` — the kernel is the vanishing ideal, so for the Shilov boundary it is the Shilov
  ideal;
* `shilovBoundary_subset_of_isBoundarySet` — and the Shilov boundary is contained in every closed
  boundary, so its algebra of functions is the smallest one.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Restriction to a subset, as a `*`-homomorphism. -/
noncomputable def restrictStarAlgHom (F : Set X) : C(X, ℂ) →⋆ₐ[ℂ] C(F, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ ⟨(Subtype.val : F → X), continuous_subtype_val⟩

omit [CompactSpace X] [T2Space X] in
@[simp]
theorem restrictStarAlgHom_apply (F : Set X) (f : C(X, ℂ)) (y : F) :
    restrictStarAlgHom F f y = f (y : X) := rfl

omit [T2Space X] in
theorem norm_restrictStarAlgHom_le (F : Set X) [CompactSpace F] (f : C(X, ℂ)) :
    ‖restrictStarAlgHom F f‖ ≤ ‖f‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg f)]
  intro y
  exact f.norm_coe_le_norm (y : X)

omit [T2Space X] in
/-- **Restriction to a boundary is isometric on `S`.** -/
theorem norm_restrictStarAlgHom_eq_of_isBoundarySet {S : Submodule ℂ C(X, ℂ)} {F : Set X}
    [CompactSpace F] (hFb : IsBoundarySet S F) {f : C(X, ℂ)} (hf : f ∈ S) :
    ‖restrictStarAlgHom F f‖ = ‖f‖ := by
  refine le_antisymm (norm_restrictStarAlgHom_le F f) ?_
  refine hFb f hf _ (norm_nonneg _) fun x hx => ?_
  exact (restrictStarAlgHom F f).norm_coe_le_norm ⟨x, hx⟩

omit [CompactSpace X] [T2Space X] in
/-- The kernel of restriction is the vanishing ideal. -/
theorem restrictStarAlgHom_eq_zero_iff {F : Set X} (f : C(X, ℂ)) :
    restrictStarAlgHom F f = 0 ↔ f ∈ vanishingIdeal F := by
  rw [mem_vanishingIdeal]
  constructor
  · intro h x hx
    have := congrFun (congrArg (fun g : C(F, ℂ) => (g : F → ℂ)) h) ⟨x, hx⟩
    simpa using this
  · intro h
    ext y
    simpa using h (y : X) y.2

/-- **Restriction to a closed subset is surjective**, by Tietze extension. -/
theorem restrictStarAlgHom_surjective {F : Set X} (hFc : IsClosed F) :
    Function.Surjective (restrictStarAlgHom F) := by
  intro g
  obtain ⟨f, hf⟩ := ContinuousMap.exists_restrict_eq hFc g
  exact ⟨f, by ext y; simpa using congrFun (congrArg (fun h : C(F, ℂ) => (h : F → ℂ)) hf) y⟩

/-! ## The envelope at the Shilov boundary -/

instance instCompactSpaceShilovBoundary (S : Submodule ℂ C(X, ℂ)) :
    CompactSpace (shilovBoundary S) :=
  isCompact_iff_compactSpace.mp (isClosed_shilovBoundary S).isCompact

/-- The canonical map onto the commutative C*-envelope. -/
noncomputable def envelopeMap (S : Submodule ℂ C(X, ℂ)) : C(X, ℂ) →⋆ₐ[ℂ] C(shilovBoundary S, ℂ) :=
  restrictStarAlgHom (shilovBoundary S)

theorem envelopeMap_surjective (S : Submodule ℂ C(X, ℂ)) :
    Function.Surjective (envelopeMap S) :=
  restrictStarAlgHom_surjective (isClosed_shilovBoundary S)

omit [T2Space X] in
/-- The kernel of the envelope map is the Shilov ideal. -/
theorem envelopeMap_eq_zero_iff (S : Submodule ℂ C(X, ℂ)) (f : C(X, ℂ)) :
    envelopeMap S f = 0 ↔ f ∈ shilovIdeal S := by
  rw [envelopeMap, restrictStarAlgHom_eq_zero_iff, shilovIdeal_eq_vanishingIdeal]

/-- **The commutative C*-envelope.**  For a function system the envelope map is a surjective
`*`-homomorphism, isometric on `S`, whose kernel is the Shilov ideal; and the Shilov boundary is
contained in every closed boundary, so no smaller closed set works. -/
theorem envelope_isometric_surjective_kernel (S : Submodule ℂ C(X, ℂ)) (hone : (1 : C(X, ℂ)) ∈ S)
    (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y) :
    Function.Surjective (envelopeMap S) ∧
      (∀ f ∈ S, ‖envelopeMap S f‖ = ‖f‖) ∧
      (∀ f : C(X, ℂ), envelopeMap S f = 0 ↔ f ∈ shilovIdeal S) ∧
      (∀ F : Set X, IsClosed F → IsBoundarySet S F → shilovBoundary S ⊆ F) := by
  refine ⟨envelopeMap_surjective S, fun f hf => ?_, envelopeMap_eq_zero_iff S,
    fun _ hFc hFb => shilovBoundary_subset hFc hFb⟩
  exact norm_restrictStarAlgHom_eq_of_isBoundarySet
    (isLeast_shilovBoundary_of_functionSystem S hone hstar hsep).1.2 hf

end ShilovLocal

end GaloisForLFunctions.HTGeometry
