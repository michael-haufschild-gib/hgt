import GaloisForLFunctions.HTGeometry.ArithmeticWindowPhase

/-!
# Liouville separation for an algebraic integer with bounded conjugates

The field norm of a nonzero algebraic integer is a nonzero rational integer, so the product of the
moduli of all its complex embeddings is at least one.  If every embedding but one has modulus at
most `B`, the remaining one is therefore at least `B^{-(n-1)}`, where `n` is the number of
embeddings.

This is the arithmetic input of a spectral-action separation: an integral spectral form that does
not vanish cannot be small unless its conjugates are large.
-/

open NumberField

namespace GaloisForLFunctions.HTGeometry

section Separation

variable {K : Type*} [Field K] [NumberField K]

/-- **The product of the embedding moduli of a nonzero algebraic integer is at least one.** -/
theorem one_le_prod_norm_embeddings (β : 𝓞 K) (hβ : β ≠ 0) :
    1 ≤ ∏ σ : K →+* ℂ, ‖σ (β : K)‖ := by
  classical
  have hnorm : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
  have hone : 1 ≤ |(Algebra.norm ℤ β : ℤ)| := Int.one_le_abs hnorm
  have hcast : ((Algebra.norm ℤ β : ℤ) : ℚ) = Algebra.norm ℚ (β : K) := Algebra.coe_norm_int β
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (β : K)) = ∏ σ : K →+* ℂ, σ (β : K) := by
    have h := Algebra.norm_eq_prod_embeddings (L := K) ℚ ℂ (β : K)
    refine h.trans ?_
    exact Fintype.prod_equiv
      (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun σ => rfl
  have hnormprod : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ (β : K))‖ = ∏ σ : K →+* ℂ, ‖σ (β : K)‖ := by
    rw [hprod, norm_prod]
  have hcast2 : (algebraMap ℚ ℂ) (Algebra.norm ℚ (β : K)) = ((Algebra.norm ℤ β : ℤ) : ℂ) := by
    rw [← hcast]
    simp
  rw [← hnormprod, hcast2, Complex.norm_intCast]
  exact_mod_cast hone

/-- **`(9)`, the Liouville separation.**  If every embedding but one of a nonzero algebraic integer
has modulus at most `B`, the remaining embedding is at least `B^{-(n-1)}`. -/
theorem inv_pow_le_norm_embedding (β : 𝓞 K) (hβ : β ≠ 0) (σ₀ : K →+* ℂ) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ σ : K →+* ℂ, σ ≠ σ₀ → ‖σ (β : K)‖ ≤ B) :
    (B ^ (Fintype.card (K →+* ℂ) - 1))⁻¹ ≤ ‖σ₀ (β : K)‖ := by
  classical
  have hprod : 1 ≤ ∏ σ : K →+* ℂ, ‖σ (β : K)‖ := one_le_prod_norm_embeddings β hβ
  have hsplit : (∏ σ : K →+* ℂ, ‖σ (β : K)‖)
      = ‖σ₀ (β : K)‖ * ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (β : K)‖ :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ σ₀)).symm
  have hrest : (∏ σ ∈ Finset.univ.erase σ₀, ‖σ (β : K)‖)
      ≤ B ^ (Fintype.card (K →+* ℂ) - 1) := by
    have hcard : (Finset.univ.erase σ₀).card = Fintype.card (K →+* ℂ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ σ₀), Finset.card_univ]
    calc (∏ σ ∈ Finset.univ.erase σ₀, ‖σ (β : K)‖)
        ≤ ∏ _σ ∈ Finset.univ.erase σ₀, B := by
          refine Finset.prod_le_prod (fun σ _ => norm_nonneg _) fun σ hσ => ?_
          exact hbound σ (Finset.ne_of_mem_erase hσ)
      _ = B ^ (Fintype.card (K →+* ℂ) - 1) := by rw [Finset.prod_const, hcard]
  have hpow : (0 : ℝ) < B ^ (Fintype.card (K →+* ℂ) - 1) := by positivity
  have hkey : 1 ≤ B ^ (Fintype.card (K →+* ℂ) - 1) * ‖σ₀ (β : K)‖ := by
    have hnn : 0 ≤ ‖σ₀ (β : K)‖ := norm_nonneg _
    calc (1 : ℝ) ≤ ‖σ₀ (β : K)‖ * ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (β : K)‖ := by
          rw [← hsplit]
          exact hprod
      _ ≤ ‖σ₀ (β : K)‖ * B ^ (Fintype.card (K →+* ℂ) - 1) :=
          mul_le_mul_of_nonneg_left hrest hnn
      _ = B ^ (Fintype.card (K →+* ℂ) - 1) * ‖σ₀ (β : K)‖ := by ring
  rw [inv_le_iff_one_le_mul₀ hpow]
  linarith [hkey]

end Separation

end GaloisForLFunctions.HTGeometry
