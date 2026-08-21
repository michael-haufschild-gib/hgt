import GaloisForLFunctions.HTGeometry.SmallQuasiIso
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Excision

If the closure of `Z` lies in the interior of `A`, then the interiors of `A` and of the complement
of `Z` cover the space, so the chains small for the pair `{A, Zᶜ}` compute singular homology.  The
comparison of the two short exact sequences

  `0 → C(A) → C^{A,Zᶜ} → C^{A,Zᶜ}/C(A) → 0`
  `0 → C(A) → C(X)    → C(X)/C(A)     → 0`

has an isomorphism on the left and a quasi-isomorphism in the middle, so the map on the right is a
quasi-isomorphism: the relative homology of the pair may be computed with chains that avoid `Z`.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X] (A Z : Set X)

theorem subChains_le_smallPair (k : ℕ) :
    subChains R A k ≤ (subcomplexOfFamily R ({A, Zᶜ} : Set (Set X))).carrier k := by
  intro c hc
  rw [subcomplexOfFamily_pair_carrier]
  exact Submodule.mem_sup_left hc

/-- The chains supported in `A`, viewed inside the chains small for `{A, Zᶜ}`. -/
noncomputable def excSub : ModuleSubcomplex R
    (subcomplexOfFamily R ({A, Zᶜ} : Set (Set X))).complex :=
  ModuleSubcomplex.restrictTo _ _ (subChains_le_smallPair R A Z)

/-- The comparison of the two pairs. -/
noncomputable def excHom :
    ModuleSubcomplex.Hom (excSub R A Z) (subcomplexOfSubset R A) :=
  ModuleSubcomplex.restrictHom _ _ (subChains_le_smallPair R A Z)

theorem excision_cover (hZ : closure Z ⊆ interior A) :
    (Set.univ : Set X) ⊆ ⋃₀ ({interior A, interior (Zᶜ)} : Set (Set X)) := by
  intro x _
  by_cases hx : x ∈ closure Z
  · exact ⟨interior A, Or.inl rfl, hZ hx⟩
  · refine ⟨interior (Zᶜ), Or.inr rfl, ?_⟩
    rw [interior_compl]
    exact hx

theorem excision_open :
    ∀ U ∈ ({interior A, interior (Zᶜ)} : Set (Set X)), IsOpen U := by
  rintro U (rfl | rfl)
  · exact isOpen_interior
  · exact isOpen_interior

theorem excision_refine :
    ∀ U ∈ ({interior A, interior (Zᶜ)} : Set (Set X)),
      ∃ V ∈ ({A, Zᶜ} : Set (Set X)), U ⊆ V := by
  rintro U (rfl | rfl)
  · exact ⟨A, Or.inl rfl, interior_subset⟩
  · exact ⟨Zᶜ, Or.inr rfl, interior_subset⟩

theorem quasiIso_smallPairIncl (hZ : closure Z ⊆ interior A) :
    QuasiIso (subcomplexOfFamily R ({A, Zᶜ} : Set (Set X))).incl := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_smallIncl R ({A, Zᶜ} : Set (Set X))
    ({interior A, interior (Zᶜ)} : Set (Set X)) (excision_open A Z)
    (excision_cover A Z hZ) (excision_refine A Z) n

/-- **Excision.**  Chains avoiding `Z` compute the relative homology of the pair `(X, A)` whenever
the closure of `Z` lies in the interior of `A`. -/
theorem quasiIso_excHom_quotMap (hZ : closure Z ⊆ interior A) :
    QuasiIso (excHom R A Z).quotMap := by
  have h₁ : QuasiIso ((excHom R A Z).shortComplexHom).τ₁ := by
    have : IsIso ((excHom R A Z).shortComplexHom).τ₁ :=
      ModuleSubcomplex.isIso_restrictHom_subMap' _ _ (subChains_le_smallPair R A Z)
    infer_instance
  have h₂ : QuasiIso ((excHom R A Z).shortComplexHom).τ₂ := quasiIso_smallPairIncl R A Z hZ
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ ((excHom R A Z).shortComplexHom)
    (ModuleSubcomplex.shortExact _) (ModuleSubcomplex.shortExact _) h₁ h₂

end GaloisForLFunctions.HTGeometry
