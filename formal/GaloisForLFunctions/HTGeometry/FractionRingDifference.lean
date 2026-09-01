import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative

/-!
# Difference automorphisms on differential fraction fields

An automorphism of a differential domain extends canonically to its fraction field.  The extended
automorphism still commutes with the quotient-rule derivation.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [Algebra ℚ R] [Differential R]

/-- Canonical extension of a domain automorphism to its fraction field. -/
def fractionRingEquiv (σ : R ≃+* R) : FractionRing R ≃+* FractionRing R :=
  IsFractionRing.ringEquivOfRingEquiv σ

omit [IsDomain R] [Algebra ℚ R] [Differential R] in
@[simp] theorem fractionRingEquiv_algebraMap (σ : R ≃+* R) (x : R) :
    fractionRingEquiv σ (algebraMap R (FractionRing R) x) =
      algebraMap R (FractionRing R) (σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x

/-- The extended fraction-field automorphism commutes with the extended derivation. -/
theorem fractionRingEquiv_commutesDeriv (σ : R ≃+* R) (hσ : CommutesDeriv σ) :
    letI : Differential (FractionRing R) := fractionRingDifferential R
    CommutesDeriv (fractionRingEquiv σ) := by
  letI : Differential (FractionRing R) := fractionRingDifferential R
  intro z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R z
  have hbR : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap R (FractionRing R) b ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff (R := R) (K := FractionRing R)).not.mpr hbR
  rw [← hab, differential_deriv_div _ _ hbF]
  simp_rw [fractionRingDifferential_algebraMap]
  rw [map_div₀, map_sub, map_mul, map_mul, map_pow]
  simp_rw [fractionRingEquiv_algebraMap]
  rw [hσ a, hσ b]
  rw [map_div₀, fractionRingEquiv_algebraMap, fractionRingEquiv_algebraMap,
    differential_deriv_div]
  · simp_rw [fractionRingDifferential_algebraMap]
  have hσb : σ b ≠ 0 := by simpa using σ.injective.ne hbR
  exact (IsFractionRing.to_map_eq_zero_iff
    (R := R) (K := FractionRing R)).not.mpr hσb

end

end GaloisForLFunctions.HTGeometry
