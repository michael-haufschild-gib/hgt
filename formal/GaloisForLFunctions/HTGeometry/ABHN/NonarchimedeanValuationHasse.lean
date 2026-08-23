import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence

/-!
# Hasse classification by the nonarchimedean valuation

The normalized valuation classifies nonzero elements of a nonarchimedean local field modulo
valuation-zero units.  This file exposes the quotient, congruence, and representative forms used
by local norm quotients and local reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- The valuation quotient equivalence is induced by the normalized valuation. -/
@[simp] theorem nonarchimedeanLocalFieldQuotientKerValuationEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    nonarchimedeanLocalFieldQuotientKerValuationEquiv K (QuotientGroup.mk x) =
      (nonarchimedeanLocalFieldResidueData K).val x := by
  rfl

/-- Two nonzero local-field elements have equal valuation exactly when their quotient is a
valuation-zero unit. -/
theorem nonarchimedeanLocalFieldValuation_congr_hasse_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    x * y⁻¹ ∈ (nonarchimedeanLocalFieldResidueData K).val.ker ↔
      (nonarchimedeanLocalFieldResidueData K).val x =
        (nonarchimedeanLocalFieldResidueData K).val y := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

/-- Every integral valuation is realized, uniquely modulo valuation-zero units. -/
theorem nonarchimedeanLocalFieldValuation_exists_unique_mod_kernel
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Multiplicative ℤ) :
    ∃ x : Kˣ,
      (nonarchimedeanLocalFieldResidueData K).val x = n ∧
      ∀ y : Kˣ,
        (nonarchimedeanLocalFieldResidueData K).val y = n ↔
          y * x⁻¹ ∈ (nonarchimedeanLocalFieldResidueData K).val.ker := by
  obtain ⟨x, hx⟩ := nonarchimedeanLocalFieldValuation_surjective K n
  refine ⟨x, hx, fun y => ?_⟩
  rw [nonarchimedeanLocalFieldValuation_congr_hasse_iff K y x, hx]

end GaloisForLFunctions.HTGeometry.ABHN
