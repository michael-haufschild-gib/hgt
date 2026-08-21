import GaloisForLFunctions.HTGeometry.SmallQuasiIso
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Excision

If the closure of `Z` lies in the interior of `A`, then the interiors of `A` and of the complement
of `Z` cover the space, so the chains small for the pair `{A, U}` compute singular homology.  The
comparison of the two short exact sequences

  `0 → C(A) → C^{A,U} → C^{A,U}/C(A) → 0`
  `0 → C(A) → C(X)    → C(X)/C(A)     → 0`

has an isomorphism on the left and a quasi-isomorphism in the middle, so the map on the right is a
quasi-isomorphism: the relative homology of the pair may be computed with chains that avoid `Z`.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X] (A U : Set X)

theorem subChains_le_smallPair (k : ℕ) :
    subChains R A k ≤ (subcomplexOfFamily R ({A, U} : Set (Set X))).carrier k := by
  intro c hc
  rw [subcomplexOfFamily_pair_carrier]
  exact Submodule.mem_sup_left hc

/-- The chains supported in `A`, viewed inside the chains small for `{A, U}`. -/
noncomputable def excSub : ModuleSubcomplex R
    (subcomplexOfFamily R ({A, U} : Set (Set X))).complex :=
  ModuleSubcomplex.restrictTo (subcomplexOfFamily R ({A, U} : Set (Set X)))
    (subcomplexOfSubset R A) (subChains_le_smallPair R A U)

/-- The comparison of the two pairs. -/
noncomputable def excHom :
    ModuleSubcomplex.Hom (excSub R A U) (subcomplexOfSubset R A) :=
  ModuleSubcomplex.restrictHom (subcomplexOfFamily R ({A, U} : Set (Set X)))
    (subcomplexOfSubset R A) (subChains_le_smallPair R A U)

theorem excision_cover (hZ : closure (Uᶜ) ⊆ interior A) :
    (Set.univ : Set X) ⊆ ⋃₀ ({interior A, interior U} : Set (Set X)) := by
  intro x _
  by_cases hx : x ∈ closure (Uᶜ)
  · exact ⟨interior A, Or.inl rfl, hZ hx⟩
  · refine ⟨interior U, Or.inr rfl, ?_⟩
    have hU : interior U = (closure (Uᶜ))ᶜ := by rw [← interior_compl, compl_compl]
    rw [hU]
    exact hx

theorem excision_open :
    ∀ V ∈ ({interior A, interior U} : Set (Set X)), IsOpen V := by
  rintro V (rfl | rfl)
  · exact isOpen_interior
  · exact isOpen_interior

theorem excision_refine :
    ∀ V ∈ ({interior A, interior U} : Set (Set X)),
      ∃ V' ∈ ({A, U} : Set (Set X)), V ⊆ V' := by
  rintro V (rfl | rfl)
  · exact ⟨A, Or.inl rfl, interior_subset⟩
  · exact ⟨U, Or.inr rfl, interior_subset⟩

theorem quasiIso_smallPairIncl (hZ : closure (Uᶜ) ⊆ interior A) :
    QuasiIso (subcomplexOfFamily R ({A, U} : Set (Set X))).incl := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_smallIncl R ({A, U} : Set (Set X))
    ({interior A, interior U} : Set (Set X)) (excision_open A U)
    (excision_cover A U hZ) (excision_refine A U) n

/-- **Excision.**  Chains avoiding `Z` compute the relative homology of the pair `(X, A)` whenever
the closure of `Z` lies in the interior of `A`. -/
theorem quasiIso_excHom_quotMap (hZ : closure (Uᶜ) ⊆ interior A) :
    QuasiIso (excHom R A U).quotMap := by
  have h₁ : QuasiIso ((excHom R A U).shortComplexHom).τ₁ := by
    have : IsIso ((excHom R A U).shortComplexHom).τ₁ :=
      ModuleSubcomplex.isIso_restrictHom_subMap'
        (subcomplexOfFamily R ({A, U} : Set (Set X)))
        (subcomplexOfSubset R A) (subChains_le_smallPair R A U)
    infer_instance
  have h₂ : QuasiIso ((excHom R A U).shortComplexHom).τ₂ := by
    show QuasiIso (subcomplexOfFamily R ({A, U} : Set (Set X))).incl
    exact quasiIso_smallPairIncl R A U hZ
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ ((excHom R A U).shortComplexHom)
    (ModuleSubcomplex.shortExact _) (ModuleSubcomplex.shortExact _) h₁ h₂

end GaloisForLFunctions.HTGeometry
