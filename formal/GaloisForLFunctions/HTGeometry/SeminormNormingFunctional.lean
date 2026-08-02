import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# A seminorm is attained by a functional it dominates

On the line spanned by a vector the assignment `c • y ↦ c · q(y)` is a functional dominated by `q`,
and Hahn–Banach extends it to the whole space.  So every seminorm is the supremum of the
functionals it dominates, attained at each vector.

* `exists_dual_le_seminorm_eq` : **for every `y` there is `ψ` with `‖ψ‖ ≤ q` and `‖ψ y‖ = q y`.**
-/

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 F : Type*} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F]

/-- **A seminorm is attained by a functional it dominates.** -/
theorem exists_dual_le_seminorm_eq (q : Seminorm 𝕜 F) (y : F) :
    ∃ ψ : F →ₗ[𝕜] 𝕜, (∀ z, ‖ψ z‖ ≤ q z) ∧ ‖ψ y‖ = q y := by
  rcases eq_or_ne y 0 with rfl | hy
  · refine ⟨0, fun z => ?_, ?_⟩
    · rw [LinearMap.zero_apply, norm_zero]
      exact apply_nonneg q z
    · rw [LinearMap.zero_apply, norm_zero, map_zero]
  · set e := LinearEquiv.toSpanNonzeroSingleton 𝕜 F y hy with he
    set ψ₀ : Module.Dual 𝕜 (𝕜 ∙ y) := ((q y : 𝕜)) • (e.symm : (𝕜 ∙ y) →ₗ[𝕜] 𝕜) with hψ₀
    have hval : ∀ v : (𝕜 ∙ y), ψ₀ v = ((q y : 𝕜)) * e.symm v := fun _ => rfl
    have hdom : ∀ v : (𝕜 ∙ y), ‖ψ₀ v‖ ≤ q (v : F) := by
      intro v
      have hv : (e.symm v) • y = (v : F) :=
        LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul 𝕜 F y hy v
      have hq : q (v : F) = ‖e.symm v‖ * q y := by
        rw [← hv, map_smul_eq_mul q]
      refine le_of_eq ?_
      calc ‖ψ₀ v‖ = q y * ‖e.symm v‖ := by
            rw [hval, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg q y)]
        _ = ‖e.symm v‖ * q y := by ring
        _ = q (v : F) := hq.symm
    obtain ⟨ψ, hψ, hψle⟩ := Module.Dual.exists_extension_of_le_seminorm (𝕜 ∙ y) ψ₀ hdom
    refine ⟨ψ, hψle, ?_⟩
    have hymem : y ∈ (𝕜 ∙ y) := Submodule.mem_span_singleton_self y
    have hy1 : ψ y = ψ₀ ⟨y, hymem⟩ := hψ ⟨y, hymem⟩
    have hcoeff : e.symm ⟨y, hymem⟩ = 1 := by
      have h := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul 𝕜 F y hy ⟨y, hymem⟩
      have h2 : (e.symm ⟨y, hymem⟩ - 1) • y = 0 := by
        rw [sub_smul, one_smul, h, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 hy
    rw [hy1, hval, hcoeff, mul_one, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg q y)]

end GaloisForLFunctions

end
