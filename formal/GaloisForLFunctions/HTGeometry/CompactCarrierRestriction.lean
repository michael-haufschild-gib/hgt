import GaloisForLFunctions.HTGeometry.CompactCarrierExistence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Every continuous functional on the compact-open space comes from one on a compact set

The compact bound of the carrier lemma says a continuous functional on `C(X, ℂ)` is dominated by
the supremum over a single compact `K`.  Consequently it kills every function vanishing on `K`, so
it descends to the range of the restriction map, where the same bound makes it a bounded functional
on a subspace of the Banach space `C(K, ℂ)`; Hahn–Banach then extends it to all of `C(K, ℂ)`.

The resulting functional reproduces the original one on every restriction.  Any statement proved
for functionals on a compact carrier therefore applies to an arbitrary element of the dual of the
compact-open space — in particular to the dual of a space of holomorphic functions on an open set.

* `HTGeometry.exists_compactCarrier_functional`.
-/

open Filter Metric
open scoped Topology

namespace HTGeometry

variable {X : Type*} [TopologicalSpace X]

/-- The restriction map to a subset, as a linear map. -/
noncomputable def restrictLinearMap (K : Set X) : C(X, ℂ) →ₗ[ℂ] C(K, ℂ) where
  toFun f := f.restrict K
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrictLinearMap_apply (K : Set X) (f : C(X, ℂ)) :
    restrictLinearMap K f = f.restrict K := rfl

/-- **A continuous functional on the compact-open space is the restriction of one carried by a
compact set.** -/
theorem exists_compactCarrier_functional (L : C(X, ℂ) →L[ℂ] ℂ) :
    ∃ (K : Set X), IsCompact K ∧
      ∃ L' : C(K, ℂ) →L[ℂ] ℂ, ∀ f : C(X, ℂ), L' (f.restrict K) = L f := by
  classical
  obtain ⟨K, C, hK, hC, hbound⟩ := exists_compact_bound_of_continuousLinearMap L
  haveI : CompactSpace (K : Type _) := isCompact_iff_compactSpace.mp hK
  set R : C(X, ℂ) →ₗ[ℂ] C(K, ℂ) := restrictLinearMap K with hR
  -- the supremum bound over `K` in terms of the norm of the restriction
  have hle : ∀ (f : C(X, ℂ)) (x : X) (hx : x ∈ K), ‖f x‖ ≤ ‖R f‖ := by
    intro f x hx
    have : (R f) ⟨x, hx⟩ = f x := rfl
    rw [← this]
    exact (R f).norm_coe_le_norm _
  have hLbound : ∀ f : C(X, ℂ), ‖L f‖ ≤ C * ‖R f‖ := by
    intro f
    exact hbound f ‖R f‖ (norm_nonneg _) fun x hx => hle f x hx
  -- `L` kills the kernel of the restriction, hence descends to its range
  have hker : LinearMap.ker R ≤ LinearMap.ker (L : C(X, ℂ) →ₗ[ℂ] ℂ) := by
    intro f hf
    have hf0 : R f = 0 := by simpa [LinearMap.mem_ker] using hf
    have := hLbound f
    rw [hf0, norm_zero, mul_zero] at this
    have hz : ‖L f‖ = 0 := le_antisymm this (norm_nonneg _)
    simpa [LinearMap.mem_ker] using norm_eq_zero.1 hz
  set φ : (LinearMap.range R) →ₗ[ℂ] ℂ :=
    ((LinearMap.ker R).liftQ (L : C(X, ℂ) →ₗ[ℂ] ℂ) hker).comp
      (R.quotKerEquivRange.symm : (LinearMap.range R) →ₗ[ℂ] _) with hφ
  have hφapp : ∀ f : C(X, ℂ), φ ⟨R f, ⟨f, rfl⟩⟩ = L f := by
    intro f
    have hmk : R.quotKerEquivRange (Submodule.Quotient.mk f) = ⟨R f, ⟨f, rfl⟩⟩ := rfl
    rw [hφ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hmk, LinearEquiv.symm_apply_apply]
    rfl
  have hφbound : ∀ y : (LinearMap.range R), ‖φ y‖ ≤ C * ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨f, hf⟩ := hy
    have hyeq : (⟨y, ⟨f, hf⟩⟩ : (LinearMap.range R)) = ⟨R f, ⟨f, rfl⟩⟩ := by
      simp [hf]
    rw [hyeq, hφapp f]
    have hnorm : ‖(⟨R f, ⟨f, rfl⟩⟩ : (LinearMap.range R))‖ = ‖R f‖ := rfl
    rw [hnorm]
    exact hLbound f
  set φc : (LinearMap.range R) →L[ℂ] ℂ := φ.mkContinuous C hφbound with hφc
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range R) φc
  refine ⟨K, hK, g, fun f => ?_⟩
  have hval := hg ⟨R f, ⟨f, rfl⟩⟩
  have : φc ⟨R f, ⟨f, rfl⟩⟩ = L f := hφapp f
  rw [this] at hval
  exact hval

end HTGeometry
