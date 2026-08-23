import GaloisForLFunctions.RHTower.DeningerQuotientProjection

/-!
# Hasse quotients for Deninger seminorm projections

The seminorm-space projection induced by a module quotient is surjective.  Its target is therefore
the source seminorm space modulo precisely the invisible source classes.  This gives the
functional-analytic quotient interface needed to track which local or divisor directions survive
in Deninger completions before any nuclearity argument.
-/

namespace RHTower

noncomputable section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The quotient seminorm space is the original seminorm space modulo the projection kernel. -/
noncomputable def deningerQuotientProjectionHasseQuotientEquiv
    (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    (DeningerSeminormSpace p ⧸
      LinearMap.ker (deningerQuotientProjection N p).toLinearMap) ≃ₗ[𝕜]
      DeningerSeminormSpace (deningerQuotientSeminorm N p) :=
  LinearMap.quotKerEquivOfSurjective (deningerQuotientProjection N p).toLinearMap
    (deningerQuotientProjection_surjective N p)

/-- The seminorm Hasse equivalence is induced by the quotient projection. -/
@[simp] theorem deningerQuotientProjectionHasseQuotientEquiv_mk
    (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : DeningerSeminormSpace p) :
    deningerQuotientProjectionHasseQuotientEquiv N p (Submodule.Quotient.mk x) =
      deningerQuotientProjection N p x := by
  rfl

/-- Two seminorm classes have the same quotient image exactly when their difference is invisible. -/
theorem deningerQuotientProjection_congr_hasse_iff
    (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x y : DeningerSeminormSpace p) :
    x - y ∈ LinearMap.ker (deningerQuotientProjection N p).toLinearMap ↔
      deningerQuotientProjection N p x = deningerQuotientProjection N p y := by
  rw [LinearMap.mem_ker]
  change deningerQuotientProjection N p (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- A represented source class is invisible exactly when its module-quotient class has zero
quotient seminorm. -/
theorem deningerSeminormMk_mem_ker_quotientProjection_iff
    (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : E) :
    deningerSeminormMk p x ∈
        LinearMap.ker (deningerQuotientProjection N p).toLinearMap ↔
      deningerQuotientSeminorm N p (Submodule.Quotient.mk x) = 0 := by
  rw [LinearMap.mem_ker]
  have hproj : (deningerQuotientProjection N p).toLinearMap (deningerSeminormMk p x) =
      deningerSeminormMk (deningerQuotientSeminorm N p) (Submodule.Quotient.mk x) :=
    deningerQuotientProjection_mk N p x
  rw [hproj]
  change (deningerSeminormKer (deningerQuotientSeminorm N p)).mkQ
      (Submodule.Quotient.mk x) = 0 ↔ _
  change (Submodule.Quotient.mk (Submodule.Quotient.mk x) :
      (E ⧸ N) ⧸ deningerSeminormKer (deningerQuotientSeminorm N p)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact deningerSeminormKer_mem

/-- Every quotient-seminorm class has a source representative, unique modulo invisible source
classes. -/
theorem deningerQuotientProjection_exists_unique_mod_kernel
    (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E)
    (z : DeningerSeminormSpace (deningerQuotientSeminorm N p)) :
    ∃ x : DeningerSeminormSpace p, deningerQuotientProjection N p x = z ∧
      ∀ y, deningerQuotientProjection N p y = z ↔
        y - x ∈ LinearMap.ker (deningerQuotientProjection N p).toLinearMap := by
  obtain ⟨x, hx⟩ := deningerQuotientProjection_surjective N p z
  refine ⟨x, hx, fun y => ?_⟩
  rw [← hx]
  exact (deningerQuotientProjection_congr_hasse_iff N p y x).symm

end

end RHTower
