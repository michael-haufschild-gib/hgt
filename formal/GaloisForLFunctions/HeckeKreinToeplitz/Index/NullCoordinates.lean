import GaloisForLFunctions.HeckeKreinToeplitz.Index.OneNegativeDirection

/-!
# Null coordinates in an index-one space

A unit vector `z` gives two null vectors `(z,1)` and `(z/2,-1/2)` with
pairing one. Their common orthogonal complement is the Hilbert space `z⊥`.
The resulting coordinates isolate the unitary quotient of an isometry
preserving the first null line.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The positive Hilbert component perpendicular to a chosen vector. -/
def nullComplement (z : H) : Submodule ℂ H := (innerSL ℂ z).ker

instance [CompleteSpace H] (z : H) : CompleteSpace (nullComplement z) :=
  (innerSL ℂ z).isClosed_ker.completeSpace_coe

/-- The normalized null vector determined by a unit vector. -/
def nullVector (z : H) : H × ℂ := (z, 1)

/-- Its canonical null dual, with pairing one. -/
def nullDual (z : H) : H × ℂ := ((2 : ℂ)⁻¹ • z, -(2 : ℂ)⁻¹)

/-- Inclusion of the positive complement into the index-one space. -/
def nullInclusion (z : H) : nullComplement z →ₗ[ℂ] (H × ℂ) where
  toFun u := (u.val, 0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- Coordinate along the first null vector. -/
def nullFirst (z : H) : (H × ℂ) →ₗ[ℂ] ℂ where
  toFun v := (inner ℂ z v.1 + v.2) / 2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
    ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- Coordinate along the dual null vector, equal to pairing with the first. -/
def nullSecond (z : H) : (H × ℂ) →ₗ[ℂ] ℂ where
  toFun v := inner ℂ z v.1 - v.2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
    ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul,
      RingHom.id_apply]
    ring

variable {z : H} (hz : ‖z‖ = 1)

include hz in
theorem inner_unit_self : inner ℂ z z = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hz]
  norm_num

/-- Positive coordinate in the null decomposition. -/
def nullPositive : (H × ℂ) →ₗ[ℂ] nullComplement z where
  toFun v := ⟨v.1 - inner ℂ z v.1 • z, by
    change inner ℂ z (v.1 - inner ℂ z v.1 • z) = 0
    rw [inner_sub_right, inner_smul_right, inner_unit_self hz, mul_one, sub_self]⟩
  map_add' v w := by
    apply Subtype.ext
    change (v.1 + w.1) - inner ℂ z (v.1 + w.1) • z =
      (v.1 - inner ℂ z v.1 • z) + (w.1 - inner ℂ z w.1 • z)
    rw [inner_add_right, add_smul]
    abel
  map_smul' c v := by
    apply Subtype.ext
    change c • v.1 - inner ℂ z (c • v.1) • z = c • (v.1 - inner ℂ z v.1 • z)
    rw [inner_smul_right, smul_sub, smul_smul]

theorem null_reconstruction (v : H × ℂ) :
    nullInclusion z (nullPositive hz v) + nullFirst z v • nullVector z +
      nullSecond z v • nullDual z = v := by
  apply Prod.ext
  · change (v.1 - inner ℂ z v.1 • z) + ((inner ℂ z v.1 + v.2) / 2) • z +
      (inner ℂ z v.1 - v.2) • ((2 : ℂ)⁻¹ • z) = v.1
    module
  · change 0 + ((inner ℂ z v.1 + v.2) / 2) * 1 +
      (inner ℂ z v.1 - v.2) * (-(2 : ℂ)⁻¹) = v.2
    ring

theorem pairing_nullVector (v : H × ℂ) : pairing (nullVector z) v = nullSecond z v := by
  change inner ℂ z v.1 - conj (1 : ℂ) * v.2 = inner ℂ z v.1 - v.2
  rw [map_one, one_mul]

theorem pairing_nullDual (v : H × ℂ) : pairing (nullDual z) v = nullFirst z v := by
  change inner ℂ ((2 : ℂ)⁻¹ • z) v.1 - conj (-(2 : ℂ)⁻¹) * v.2 =
    (inner ℂ z v.1 + v.2) / 2
  rw [inner_smul_left]
  simp only [map_neg, map_inv₀, map_ofNat]
  ring

include hz in
theorem nullVector_square : pairing (nullVector z) (nullVector z) = 0 := by
  rw [pairing_nullVector]
  change inner ℂ z z - 1 = 0
  rw [inner_unit_self hz, sub_self]

include hz in
theorem nullVector_nullDual : pairing (nullVector z) (nullDual z) = 1 := by
  rw [pairing_nullVector]
  change inner ℂ z ((2 : ℂ)⁻¹ • z) - (-(2 : ℂ)⁻¹) = 1
  rw [inner_smul_right, inner_unit_self hz]
  norm_num

include hz in
theorem nullDual_square : pairing (nullDual z) (nullDual z) = 0 := by
  rw [pairing_nullDual]
  change (inner ℂ z ((2 : ℂ)⁻¹ • z) + (-(2 : ℂ)⁻¹)) / 2 = 0
  rw [inner_smul_right, inner_unit_self hz]
  norm_num

theorem nullPositive_nullVector : nullPositive hz (nullVector z) = 0 := by
  apply Subtype.ext
  change z - inner ℂ z z • z = 0
  rw [inner_unit_self hz, one_smul, sub_self]

theorem nullPositive_nullDual : nullPositive hz (nullDual z) = 0 := by
  apply Subtype.ext
  change (2 : ℂ)⁻¹ • z - inner ℂ z ((2 : ℂ)⁻¹ • z) • z = 0
  rw [inner_smul_right, inner_unit_self hz, mul_one, sub_self]

theorem nullPositive_inclusion (u : nullComplement z) :
    nullPositive hz (nullInclusion z u) = u := by
  apply Subtype.ext
  have hu : inner ℂ z (u : H) = 0 := u.property
  change (u : H) - inner ℂ z (u : H) • z = u
  rw [hu, zero_smul, sub_zero]

theorem nullSecond_inclusion (u : nullComplement z) : nullSecond z (nullInclusion z u) = 0 := by
  have hu : inner ℂ z (u : H) = 0 := u.property
  change inner ℂ z (u : H) - 0 = 0
  rw [hu, sub_self]

theorem pairing_nullInclusion (u v : nullComplement z) :
    pairing (nullInclusion z u) (nullInclusion z v) = inner ℂ u v := by
  change inner ℂ (u : H) (v : H) - conj (0 : ℂ) * 0 = inner ℂ u v
  rw [map_zero, zero_mul, sub_zero]
  rfl

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
