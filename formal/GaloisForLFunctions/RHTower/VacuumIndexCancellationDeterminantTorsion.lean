import GaloisForLFunctions.HTGeometry.LawHistoryTransgressionPages

/-!
# Vacuum-index cancellation determinant torsion

Canonical cokernel exactness and dimension law for composition with an injective completion map.
The formal statement retains the full kernel identity and all three exactness clauses.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x

variable {k : Type u} {X : Type v} {Y : Type w} {Z : Type x}
variable [Field k]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]
variable [AddCommGroup Z] [Module k Z]

theorem ker_comp_eq_of_injective (A : X →ₗ[k] Y) (S : Y →ₗ[k] Z)
    (hS : Function.Injective S) : LinearMap.ker (S.comp A) = LinearMap.ker A := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro h
    exact hS (h.trans (map_zero S).symm)
  · intro h
    rw [h, map_zero]

theorem earlierCokerToCompositeCoker_injective_of_injective
    (A : X →ₗ[k] Y) (S : Y →ₗ[k] Z) (hS : Function.Injective S) :
    Function.Injective (earlierCokerToCompositeCoker A S) := by
  rw [← LinearMap.ker_eq_bot]
  rw [← range_lawHistoryDifferential_eq_ker]
  rw [range_lawHistoryDifferential_eq_map, LinearMap.ker_eq_bot.mpr hS]
  simp

/-- Exact CIT-1 cokernel package for an injective second map, including unchanged kernel. -/
theorem injectiveComposition_cokernel_exact
    (A : X →ₗ[k] Y) (S : Y →ₗ[k] Z) (hS : Function.Injective S) :
    Function.Injective (earlierCokerToCompositeCoker A S) ∧
      LinearMap.range (earlierCokerToCompositeCoker A S) =
        LinearMap.ker (compositeToOuter A S) ∧
      Function.Surjective (compositeToOuter A S) ∧
      LinearMap.ker (S.comp A) = LinearMap.ker A := by
  exact ⟨earlierCokerToCompositeCoker_injective_of_injective A S hS,
    range_earlierCokerToCompositeCoker_eq_ker A S,
    compositeToOuter_surjective A S,
    ker_comp_eq_of_injective A S hS⟩

/-- Finite-dimensional CIT-1 dimension formula. -/
theorem finrank_coker_comp_eq_of_injective
    [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]
    (A : X →ₗ[k] Y) (S : Y →ₗ[k] Z) (hS : Function.Injective S) :
    Module.finrank k (Z ⧸ LinearMap.range (S.comp A)) =
      Module.finrank k (Y ⧸ LinearMap.range A) +
        Module.finrank k (Z ⧸ LinearMap.range S) := by
  have hrange : LinearMap.range (lawHistoryDifferential A S) = ⊥ := by
    rw [range_lawHistoryDifferential_eq_map, LinearMap.ker_eq_bot.mpr hS]
    simp
  have h := finrank_quotient_range_comp_eq A S
  rw [hrange] at h
  have hbot := Submodule.finrank_quotient_add_finrank
    (⊥ : Submodule k (Y ⧸ LinearMap.range A))
  simp only [finrank_bot, add_zero] at hbot
  omega

end

end GaloisForLFunctions.HTGeometry
