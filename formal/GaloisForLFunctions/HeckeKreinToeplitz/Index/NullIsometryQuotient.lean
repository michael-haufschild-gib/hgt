import GaloisForLFunctions.HeckeKreinToeplitz.Index.NullCoordinates

/-!
# The unitary quotient of an invariant null line

An invertible form-isometry preserving a null line induces a unitary map on
its positive quotient. Null coordinates realize this quotient as an actual
Hilbert subspace, so the off-circle unitary resolvent can be applied there.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {z : H} (hz : ‖z‖ = 1)

/-- The positive-coordinate map induced by an operator. -/
def nullQuotient (T : (H × ℂ) →ₗ[ℂ] (H × ℂ)) :
    nullComplement z →ₗ[ℂ] nullComplement z :=
  (nullPositive hz).comp (T.comp (nullInclusion z))

theorem nullQuotient_projection (T : (H × ℂ) →ₗ[ℂ] (H × ℂ))
    {a : ℂ} (hw : T (nullVector z) = a • nullVector z)
    {v : H × ℂ} (hv : nullSecond z v = 0) :
    nullQuotient hz T (nullPositive hz v) = nullPositive hz (T v) := by
  have he := congrArg (fun y => nullPositive hz (T y)) (null_reconstruction hz v)
  simp only [map_add, map_smul, hw, nullPositive_nullVector, hv,
    smul_zero, zero_smul, add_zero] at he
  exact he

theorem nullSecond_action (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ u v, pairing (T u) (T v) = pairing u v)
    {a : ℂ} (ha : a ≠ 0) (hw : T (nullVector z) = a • nullVector z) (v : H × ℂ) :
    nullSecond z (T v) = (conj a)⁻¹ * nullSecond z v := by
  have he := hT (nullVector z) v
  rw [hw, pairing_smul_left, pairing_nullVector, pairing_nullVector] at he
  have ha' : conj a ≠ 0 := star_ne_zero.mpr ha
  calc
    nullSecond z (T v) = (conj a)⁻¹ * (conj a * nullSecond z (T v)) := by
      rw [← mul_assoc, inv_mul_cancel₀ ha', one_mul]
    _ = _ := by rw [he]

theorem nullVector_inverse_eigen (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    {a : ℂ} (ha : a ≠ 0) (hw : T (nullVector z) = a • nullVector z) :
    T.symm (nullVector z) = a⁻¹ • nullVector z := by
  apply T.injective
  rw [LinearEquiv.apply_symm_apply, map_smul, hw, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem inverse_pairing (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ u v, pairing (T u) (T v) = pairing u v) (u v : H × ℂ) :
    pairing (T.symm u) (T.symm v) = pairing u v := by
  simpa only [LinearEquiv.apply_symm_apply] using (hT (T.symm u) (T.symm v)).symm

theorem nullQuotient_inverse_apply (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ u v, pairing (T u) (T v) = pairing u v)
    {a : ℂ} (ha : a ≠ 0) (hw : T (nullVector z) = a • nullVector z)
    (u : nullComplement z) :
    nullQuotient hz T.symm.toLinearMap (nullQuotient hz T.toLinearMap u) = u := by
  have hb : nullSecond z (T (nullInclusion z u)) = 0 := by
    rw [nullSecond_action T hT ha hw, nullSecond_inclusion, mul_zero]
  have hinv := nullVector_inverse_eigen T ha hw
  change nullQuotient hz T.symm.toLinearMap
    (nullPositive hz (T (nullInclusion z u))) = u
  rw [nullQuotient_projection hz T.symm.toLinearMap hinv hb]
  change nullPositive hz (T.symm (T (nullInclusion z u))) = u
  rw [LinearEquiv.symm_apply_apply, nullPositive_inclusion]

/-- Algebraic equivalence on the quotient by the invariant null line. -/
def nullQuotientEquiv (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ u v, pairing (T u) (T v) = pairing u v)
    {a : ℂ} (ha : a ≠ 0) (hw : T (nullVector z) = a • nullVector z) :
    nullComplement z ≃ₗ[ℂ] nullComplement z where
  toLinearMap := nullQuotient hz T.toLinearMap
  invFun := nullQuotient hz T.symm.toLinearMap
  left_inv := nullQuotient_inverse_apply hz T hT ha hw
  right_inv := nullQuotient_inverse_apply hz T.symm (inverse_pairing T hT)
    (inv_ne_zero ha) (nullVector_inverse_eigen T ha hw)

theorem nullQuotient_inner (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ u v, pairing (T u) (T v) = pairing u v)
    {a : ℂ} (ha : a ≠ 0) (hw : T (nullVector z) = a • nullVector z)
    (u v : nullComplement z) :
    inner ℂ (nullQuotient hz T.toLinearMap u) (nullQuotient hz T.toLinearMap v) =
      inner ℂ u v := by
  have hsplit (q : nullComplement z) : T (nullInclusion z q) =
      nullInclusion z (nullQuotient hz T.toLinearMap q) +
        nullFirst z (T (nullInclusion z q)) • nullVector z := by
    have he := null_reconstruction hz (T (nullInclusion z q))
    rw [nullSecond_action T hT ha hw, nullSecond_inclusion, mul_zero,
      zero_smul, add_zero] at he
    exact he.symm
  have hleft (q : nullComplement z) : pairing (nullVector z) (nullInclusion z q) = 0 := by
    rw [pairing_nullVector, nullSecond_inclusion]
  have hright (q : nullComplement z) : pairing (nullInclusion z q) (nullVector z) = 0 := by
    rw [← pairing_conj_symm, hleft, map_zero]
  have he := hT (nullInclusion z u) (nullInclusion z v)
  rw [hsplit u, hsplit v] at he
  simpa only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right,
    pairing_nullInclusion, hleft, hright, nullVector_square hz, mul_zero,
    add_zero, zero_add] using he

/-- A form-isometry induces a unitary operator on the positive quotient. -/
def nullQuotientUnitary (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ u v, pairing (T u) (T v) = pairing u v)
    {a : ℂ} (ha : a ≠ 0) (hw : T (nullVector z) = a • nullVector z) :
    nullComplement z ≃ₗᵢ[ℂ] nullComplement z where
  toLinearEquiv := nullQuotientEquiv hz T hT ha hw
  norm_map' u := by
    have he := congrArg Complex.re (nullQuotient_inner hz T hT ha hw u u)
    change RCLike.re (inner ℂ (nullQuotient hz T.toLinearMap u)
      (nullQuotient hz T.toLinearMap u)) = RCLike.re (inner ℂ u u) at he
    rw [inner_self_eq_norm_sq (𝕜 := ℂ), inner_self_eq_norm_sq (𝕜 := ℂ)] at he
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
