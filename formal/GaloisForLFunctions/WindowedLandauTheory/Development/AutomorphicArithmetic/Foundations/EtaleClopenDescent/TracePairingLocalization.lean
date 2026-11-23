import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Localization.Integral

/-! Integrality of a field trace pairing extends from the original
order to its localization. -/

noncomputable section

namespace GlobalTheory.PD

variable {A B R T F E : Type*}
  [CommRing A] [CommRing B] [CommRing R] [CommRing T] [Field F] [Field E]
  [Algebra A B] [Algebra A R] [Algebra A F] [Algebra R F] [IsScalarTower A R F]
  [Algebra F E] [Algebra A E] [Algebra B E] [IsScalarTower A F E] [IsScalarTower A B E]
  [Algebra B T] [Algebra T E] [IsScalarTower B T E]

/-- In the localized base ring, testing the trace pairing against the
original order is equivalent to testing against the localized order. -/
theorem trace_pairing_localization (M : Submonoid A) [IsLocalization M R]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) T] (z : E) :
    (∀ b : B, Algebra.trace F E (z * algebraMap B E b) ∈ (algebraMap R F).range) ↔
      ∀ t : T, Algebra.trace F E (z * algebraMap T E t) ∈ (algebraMap R F).range := by
  constructor
  · intro h t
    obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B M) t
    obtain ⟨s, hs, hsB⟩ := m.property
    have hm' : algebraMap T E t * algebraMap B E (m : B) = algebraMap B E b := by
      simpa only [map_mul, ← IsScalarTower.algebraMap_apply B T E] using
        congrArg (algebraMap T E) hm
    have hmul : algebraMap T E t * algebraMap F E (algebraMap A F s) = algebraMap B E b := by
      rwa [← hsB, ← IsScalarTower.algebraMap_apply A B E,
        IsScalarTower.algebraMap_apply A F E] at hm'
    have htr : algebraMap A F s * Algebra.trace F E (z * algebraMap T E t) =
        Algebra.trace F E (z * algebraMap B E b) := by
      calc
        _ = Algebra.trace F E ((algebraMap A F s) • (z * algebraMap T E t)) :=
          (map_smul (Algebra.trace F E) (algebraMap A F s) (z * algebraMap T E t)).symm
        _ = _ := congrArg (Algebra.trace F E) (by
          rw [Algebra.smul_def, ← hmul]
          ac_rfl)
    obtain ⟨a, ha⟩ := h b
    let u := (IsLocalization.map_units R (⟨s, hs⟩ : M)).unit
    have hu : (u : R) = algebraMap A R s :=
      (IsLocalization.map_units R (⟨s, hs⟩ : M)).unit_spec
    have hu' : algebraMap R F (↑u⁻¹ : R) * algebraMap A F s = 1 := by
      rw [IsScalarTower.algebraMap_apply A R F, ← hu, ← map_mul, Units.inv_mul, map_one]
    refine ⟨(↑u⁻¹ : R) * a, ?_⟩
    rw [map_mul, ha, ← htr, ← mul_assoc, hu', one_mul]
  · intro h b
    have hb := h (algebraMap B T b)
    rwa [← IsScalarTower.algebraMap_apply B T E] at hb

end GlobalTheory.PD
