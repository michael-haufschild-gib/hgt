import GaloisForLFunctions.HTGeometry.PaperLocallyNilpotentMultipliers
import GaloisForLFunctions.HTGeometry.CascadeLaurentLevelJacobian

/-!
# Exact termination boundary of the native Laurent Euler clock

Source divisibility rigidity forces every locally nilpotent derivation of
a characteristic-zero field to vanish. For the native Laurent Euler
operator this excludes every nonzero multiplier. Its invariant and
terminating inputs are exactly the coefficient-field constants.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate LaurentDerivation

noncomputable section

/-- On a characteristic-zero field, source divisibility rigidity kills every terminating derivation. -/
theorem paperLND_field_iff_eq_zero {k F : Type*} [CommRing k] [Field F]
    [CharZero F] [Algebra k F] (D : Derivation k F F) :
    IsLocallyNilpotent D ↔ D = 0 := by
  constructor
  · intro h
    ext a
    by_cases ha : a = 0
    · simp [ha]
    exact paperLND_fixed_of_dvd_apply D h a
      ⟨a⁻¹ * D a, by simp [ha]⟩
  · rintro rfl
    intro a
    exact ⟨1, rfl⟩

/-- Rescaling cannot turn a nonzero field derivation into a terminating one. -/
theorem paperLND_field_multiplier_iff {k F : Type*} [CommRing k] [Field F]
    [CharZero F] [Algebra k F] (D : Derivation k F F) (q : F) :
    IsLocallyNilpotent (q • D) ↔ q = 0 ∨ D = 0 := by
  rw [paperLND_field_iff_eq_zero]
  constructor
  · intro h
    by_cases hq : q = 0
    · exact Or.inl hq
    right
    ext a
    have he := congrArg (fun d : Derivation k F F => d a) h
    exact (mul_eq_zero.mp he).resolve_left hq
  · rintro (rfl | rfl) <;> simp

variable {K : Type*} [Field K] [Algebra ℂ K]

attribute [local instance 2000] Algebra.toModule

/-- Every Euler iterate acts by the corresponding power of the Laurent exponent. -/
theorem paperLaurentEuler_iterate_coeff (f : LaurentSeries K) (m : ℕ) (n : ℤ) :
    (((eulerDerivation (K := K) : LaurentSeries K → LaurentSeries K)^[m]) f).coeff n =
      (n : K) ^ m * f.coeff n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', coeff_eulerDerivation, ih, pow_succ]
    ring

/-- The complete Euler kernel is the embedded coefficient field. -/
theorem paperLaurentEuler_kernel_iff (f : LaurentSeries K) :
    eulerDerivation f = 0 ↔ f = HahnSeries.C (f.coeff 0) := by
  letI : CharZero K := Algebra.charZero_of_charZero ℂ K
  constructor
  · intro h
    apply HahnSeries.ext
    funext n
    by_cases hn : n = 0
    · subst n
      simp [HahnSeries.C_apply]
    · have he := congrArg (fun g : LaurentSeries K => g.coeff n) h
      rw [coeff_eulerDerivation, HahnSeries.coeff_zero] at he
      have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
      rw [(mul_eq_zero.mp he).resolve_left hnK]
      simp [HahnSeries.C_apply, hn]
  · intro h
    rw [h, eulerDerivation_C]

/-- Eventual Euler annihilation is equivalent to already being a coefficient-field constant. -/
theorem paperLaurentEuler_terminates_iff (f : LaurentSeries K) :
    (∃ m, (eulerDerivation (K := K) : LaurentSeries K → LaurentSeries K)^[m] f = 0) ↔
      f = HahnSeries.C (f.coeff 0) := by
  letI : CharZero K := Algebra.charZero_of_charZero ℂ K
  constructor
  · rintro ⟨m, hm⟩
    apply (paperLaurentEuler_kernel_iff f).mp
    apply HahnSeries.ext
    funext n
    rw [coeff_eulerDerivation, HahnSeries.coeff_zero]
    by_cases hn : n = 0
    · simp [hn]
    · have he := congrArg (fun g : LaurentSeries K => g.coeff n) hm
      rw [paperLaurentEuler_iterate_coeff, HahnSeries.coeff_zero] at he
      have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
      rw [(mul_eq_zero.mp he).resolve_left (pow_ne_zero m hnK), mul_zero]
  · intro h
    exact ⟨1, (paperLaurentEuler_kernel_iff f).mpr h⟩

/-- The native Euler derivation is nonzero, detected by the degree-one monomial. -/
theorem paperLaurentEuler_ne_zero : eulerDerivation (K := K) ≠ 0 := by
  intro h
  have he := congrArg
    (fun D : LaurentComplexDerivation K => (D (HahnSeries.single 1 1)).coeff 1) h
  simp [coeff_eulerDerivation, HahnSeries.coeff_single_same] at he

/-- No nonzero Laurent-series speed produces a locally nilpotent Euler clock. -/
theorem paperLaurentEuler_multiplier_iff (q : LaurentSeries K) :
    IsLocallyNilpotent (q • eulerDerivation (K := K)) ↔ q = 0 := by
  letI : CharZero (LaurentSeries K) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (LaurentSeries K)).injective
  rw [paperLND_field_multiplier_iff]
  exact or_iff_left paperLaurentEuler_ne_zero

/-- Rescaling preserves precisely the same constants unless the speed itself is zero. -/
theorem paperLaurentEuler_multiplier_kernel_iff (q f : LaurentSeries K) :
    (q • eulerDerivation (K := K)) f = 0 ↔
      q = 0 ∨ f = HahnSeries.C (f.coeff 0) := by
  change q * eulerDerivation f = 0 ↔ _
  rw [mul_eq_zero, paperLaurentEuler_kernel_iff]

end

end GaloisForLFunctions.HTGeometry
