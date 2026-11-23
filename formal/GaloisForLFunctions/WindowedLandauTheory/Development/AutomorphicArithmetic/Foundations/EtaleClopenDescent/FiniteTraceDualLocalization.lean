import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteLinearMapDenominator
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TracePairingLocalization
import Mathlib.Algebra.Algebra.Bilinear

/-! The trace dual of a finite order localizes with the order. -/

noncomputable section

namespace GlobalTheory.PD

variable {A B R T F E : Type*}
  [CommRing A] [CommRing B] [CommRing R] [CommRing T] [Field F] [Field E]
  [Algebra A B] [Algebra A R] [Algebra A F] [Algebra R F] [IsScalarTower A R F]
  [Algebra F E] [Algebra A E] [Algebra B E] [IsScalarTower A F E] [IsScalarTower A B E]
  [Algebra B T] [Algebra T E] [IsScalarTower B T E] [Module.Finite A B]

/-- Integrality against the localized order is equivalent to integrality
against the original order after a single rescaling by a denominator. -/
theorem finite_trace_dual_localization (M : Submonoid A) [IsLocalization M R]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) T] (z : E) :
    (∀ t : T, Algebra.trace F E (z * algebraMap T E t) ∈ (algebraMap R F).range) ↔
      ∃ s : M, ∀ b : B, Algebra.trace F E
        ((algebraMap A E (s : A) * z) * algebraMap B E b) ∈ (algebraMap A F).range := by
  rw [← trace_pairing_localization (T := T) M z]
  let f : B →ₗ[A] F :=
    (((Algebra.trace F E).comp (LinearMap.mul F E z)).restrictScalars A).comp
      ((Algebra.linearMap B E).restrictScalars A)
  have hscale (s : A) (b : B) :
      Algebra.trace F E ((algebraMap A E s * z) * algebraMap B E b) = algebraMap A F s * f b := by
    change _ = algebraMap A F s * Algebra.trace F E (z * algebraMap B E b)
    rw [mul_assoc, IsScalarTower.algebraMap_apply A F E, ← Algebra.smul_def, map_smul, smul_eq_mul]
  simp only [hscale]
  change (∀ b, f b ∈ (algebraMap R F).range) ↔ _
  refine ⟨exists_common_denominator M f, ?_⟩
  rintro ⟨s, h⟩ b
  obtain ⟨a, ha⟩ := h b
  let u := (IsLocalization.map_units R s).unit
  have hu : (u : R) = algebraMap A R (s : A) := (IsLocalization.map_units R s).unit_spec
  have he : algebraMap R F (↑u⁻¹ : R) * algebraMap A F (s : A) = 1 := by
    rw [IsScalarTower.algebraMap_apply A R F, ← hu, ← map_mul, Units.inv_mul, map_one]
  refine ⟨(↑u⁻¹ : R) * algebraMap A R a, ?_⟩
  rw [map_mul, ← IsScalarTower.algebraMap_apply A R F, ha, ← mul_assoc, he, one_mul]

end GlobalTheory.PD
