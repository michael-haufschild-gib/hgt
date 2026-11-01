import GaloisForLFunctions.HeckeKreinToeplitz.Index.NullIsometryQuotient
import GaloisForLFunctions.RHTower.UnitaryResolventOffCircle

/-!
# The reflected companion of a nonunit null eigenvector

For an index-one isometry, an eigenvalue off the unit circle has a companion
at its inverse conjugate. The unitary resolvent on the positive quotient
solves the positive coordinate; the remaining scalar equation separates the
two eigenvalues. The two null eigenvectors have pairing one.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A normalized eigenvector off the unit circle has a reflected null companion. -/
theorem exists_reflected_null_eigenvector (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ u v, pairing (T u) (T v) = pairing u v)
    {z : H} {a : ℂ} (ha : ‖a‖ ≠ 1)
    (hw : T (nullVector z) = a • nullVector z) :
    ∃ v : H × ℂ, pairing (nullVector z) v = 1 ∧
      T v = (conj a)⁻¹ • v ∧ pairing v v = 0 := by
  have hw0 : nullVector z ≠ 0 := by
    intro he
    exact one_ne_zero (congrArg Prod.snd he)
  have ha0 : a ≠ 0 := by
    intro he
    have hz0 : T (nullVector z) = T 0 := by rw [hw, he, zero_smul, map_zero]
    exact hw0 (T.injective hz0)
  have hwq := pairing_self_eq_zero_of_nonunit_eigenvalue T.toLinearMap hT ha hw
  have hz : ‖z‖ = 1 := by
    have hr := congrArg Complex.re hwq
    rw [pairing_self_re] at hr
    change ‖z‖ ^ 2 - ‖(1 : ℂ)‖ ^ 2 = 0 at hr
    rw [norm_one] at hr
    nlinarith only [hr, norm_nonneg z]
  let μ : ℂ := (conj a)⁻¹
  have hμ : ‖μ‖ ≠ 1 := by
    have hn : ‖a‖⁻¹ ≠ 1 := fun h => ha (_root_.inv_eq_one.mp h)
    simpa only [μ, norm_inv, norm_conj] using hn
  have hden : a - μ ≠ 0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    change ‖a‖ = ‖(conj a)⁻¹‖ at hn
    rw [norm_inv, norm_conj] at hn
    have hs : ‖a‖ ^ 2 = 1 := by
      calc
        ‖a‖ ^ 2 = ‖a‖ * ‖a‖⁻¹ := by rw [pow_two]; exact congrArg (fun r => ‖a‖ * r) hn
        _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha0)
    exact ha (by nlinarith only [hs, norm_nonneg a])
  let U := nullQuotientUnitary hz T hT ha0 hw
  let q : nullComplement z := nullPositive hz (T (nullDual z))
  obtain ⟨x, hx⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp
    (RHTower.isUnit_unitaryOp_sub_smul U hμ)).2 (-q)
  change U x - μ • x = -q at hx
  have hx' : q + nullQuotient hz T.toLinearMap x = μ • x := by
    change q + U x = μ • x
    calc
      q + U x = (U x - μ • x) + q + μ • x := by abel
      _ = μ • x := by rw [hx]; abel
  have hdual : nullSecond z (nullDual z) = 1 := by
    rw [← pairing_nullVector, nullVector_nullDual hz]
  have hTd : T (nullDual z) = nullInclusion z q +
      nullFirst z (T (nullDual z)) • nullVector z + μ • nullDual z := by
    have he := null_reconstruction hz (T (nullDual z))
    rw [nullSecond_action T hT ha0 hw, hdual, mul_one] at he
    exact he.symm
  have hTx : T (nullInclusion z x) =
      nullInclusion z (nullQuotient hz T.toLinearMap x) +
        nullFirst z (T (nullInclusion z x)) • nullVector z := by
    have he := null_reconstruction hz (T (nullInclusion z x))
    rw [nullSecond_action T hT ha0 hw, nullSecond_inclusion,
      mul_zero, zero_smul, add_zero] at he
    exact he.symm
  let γ : ℂ := nullFirst z (T (nullDual z)) + nullFirst z (T (nullInclusion z x))
  let b : H × ℂ := nullDual z + nullInclusion z x
  have hR : nullInclusion z q + nullInclusion z (nullQuotient hz T.toLinearMap x) =
      μ • nullInclusion z x := by
    rw [← map_add, hx', map_smul]
  have hb : T b = μ • b + γ • nullVector z := by
    change T (nullDual z + nullInclusion z x) = _
    rw [map_add, hTd, hTx]
    calc
      nullInclusion z q + nullFirst z (T (nullDual z)) • nullVector z + μ • nullDual z +
          (nullInclusion z (nullQuotient hz T.toLinearMap x) +
            nullFirst z (T (nullInclusion z x)) • nullVector z) =
          (nullInclusion z q + nullInclusion z (nullQuotient hz T.toLinearMap x)) +
            γ • nullVector z + μ • nullDual z := by dsimp [γ]; module
      _ = μ • b + γ • nullVector z := by rw [hR]; dsimp [b]; module
  let c : ℂ := -γ / (a - μ)
  have hc : γ + c * a = μ * c := by
    dsimp [c]
    field_simp [hden] <;> ring
  let v : H × ℂ := b + c • nullVector z
  have hv : T v = μ • v := by
    calc
      T v = (μ • b + γ • nullVector z) + c • (a • nullVector z) := by
        change T (b + c • nullVector z) = _
        rw [map_add, map_smul, hb, hw]
      _ = μ • b + (γ + c * a) • nullVector z := by module
      _ = μ • v := by rw [hc]; dsimp [v]; module
  have hpair : pairing (nullVector z) v = 1 := by
    change pairing (nullVector z) ((nullDual z + nullInclusion z x) + c • nullVector z) = 1
    rw [pairing_add_right, pairing_add_right, pairing_smul_right,
      nullVector_nullDual hz, nullVector_square hz,
      pairing_nullVector, nullSecond_inclusion, mul_zero, add_zero, add_zero]
  exact ⟨v, hpair, hv,
    pairing_self_eq_zero_of_nonunit_eigenvalue T.toLinearMap hT hμ hv⟩

#print axioms exists_reflected_null_eigenvector

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
