import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation

/-!
# Logarithmic product formula for number-ring units

The product of the complex-embedding moduli of every number-ring unit is one.  Its logarithmic
profile is therefore an additive homomorphism into the exact norm-zero hyperplane.  These are the
first structural inputs for Dirichlet-unit reduction; no product-formula or hyperplane premise is
retained.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Product of the moduli of all complex embeddings of a number-ring unit. -/
def numberFieldUnitEmbeddingProduct (u : (𝓞 K)ˣ) : ℝ :=
  ∏ σ : K →+* ℂ, ‖σ ((u : 𝓞 K) : K)‖

theorem numberFieldUnitEmbeddingProduct_pos (u : (𝓞 K)ˣ) :
    0 < numberFieldUnitEmbeddingProduct u := by
  apply Finset.prod_pos
  intro σ _
  rw [norm_pos_iff]
  intro h
  have h' : σ (((u : 𝓞 K) : K)) = σ 0 := h.trans (map_zero σ).symm
  have hz : (((u : 𝓞 K) : K)) = 0 := σ.injective h'
  have huK : (((u : 𝓞 K) : K)) ≠ 0 := by
    norm_cast
    exact u.ne_zero
  exact huK hz

theorem numberFieldUnitEmbeddingProduct_mul_inv (u : (𝓞 K)ˣ) :
    numberFieldUnitEmbeddingProduct u * numberFieldUnitEmbeddingProduct u⁻¹ = 1 := by
  rw [numberFieldUnitEmbeddingProduct, numberFieldUnitEmbeddingProduct,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro σ _
  rw [← norm_mul]
  have hu : (((u : 𝓞 K) : K) * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) = 1 := by
    norm_cast
    simp
  rw [← map_mul, hu, map_one, norm_one]

/-- The embedding-modulus product of every number-ring unit is exactly one. -/
theorem numberFieldUnitEmbeddingProduct_eq_one (u : (𝓞 K)ˣ) :
    numberFieldUnitEmbeddingProduct u = 1 := by
  have h1 : 1 ≤ numberFieldUnitEmbeddingProduct u :=
    one_le_prod_norm_embeddings (u : 𝓞 K) u.ne_zero
  have h2 : 1 ≤ numberFieldUnitEmbeddingProduct u⁻¹ :=
    one_le_prod_norm_embeddings (K := K) (↑(u⁻¹) : 𝓞 K) (u⁻¹).ne_zero
  have hp := numberFieldUnitEmbeddingProduct_mul_inv u
  nlinarith [numberFieldUnitEmbeddingProduct_pos u,
    numberFieldUnitEmbeddingProduct_pos u⁻¹]

/-- Log-modulus profile over every complex embedding. -/
def numberFieldUnitLogEmbeddings (u : (𝓞 K)ˣ) : (K →+* ℂ) → ℝ :=
  fun σ => Real.log ‖σ ((u : 𝓞 K) : K)‖

omit [NumberField K] in
theorem numberFieldUnitLogEmbeddings_mul (u v : (𝓞 K)ˣ) :
    numberFieldUnitLogEmbeddings (u * v) =
      numberFieldUnitLogEmbeddings u + numberFieldUnitLogEmbeddings v := by
  funext σ
  rw [Pi.add_apply]
  simp only [numberFieldUnitLogEmbeddings, Units.val_mul]
  have huv : ((((u : 𝓞 K) * (v : 𝓞 K) : 𝓞 K) : K)) =
      (((u : 𝓞 K) : K)) * (((v : 𝓞 K) : K)) := by norm_cast
  rw [huv, map_mul, norm_mul, Real.log_mul]
  · exact norm_ne_zero_iff.mpr
      (by
        intro h
        have h' : σ (((u : 𝓞 K) : K)) = σ 0 := h.trans (map_zero σ).symm
        have hz : (((u : 𝓞 K) : K)) = 0 := σ.injective h'
        have huK : (((u : 𝓞 K) : K)) ≠ 0 := by
          norm_cast
          exact u.ne_zero
        exact huK hz)
  · exact norm_ne_zero_iff.mpr
      (by
        intro h
        have h' : σ (((v : 𝓞 K) : K)) = σ 0 := h.trans (map_zero σ).symm
        have hz : (((v : 𝓞 K) : K)) = 0 := σ.injective h'
        have hvK : (((v : 𝓞 K) : K)) ≠ 0 := by
          norm_cast
          exact v.ne_zero
        exact hvK hz)

/-- The logarithmic profile of every number-ring unit has coordinate sum zero. -/
theorem sum_numberFieldUnitLogEmbeddings (u : (𝓞 K)ˣ) :
    ∑ σ : K →+* ℂ, numberFieldUnitLogEmbeddings u σ = 0 := by
  change (∑ σ : K →+* ℂ, Real.log ‖σ ((u : 𝓞 K) : K)‖) = 0
  rw [← Real.log_prod]
  · rw [← numberFieldUnitEmbeddingProduct,
      numberFieldUnitEmbeddingProduct_eq_one, Real.log_one]
  · intro σ _
    exact norm_ne_zero_iff.mpr
      (by
        intro h
        have h' : σ (((u : 𝓞 K) : K)) = σ 0 := h.trans (map_zero σ).symm
        have hz : (((u : 𝓞 K) : K)) = 0 := σ.injective h'
        have huK : (((u : 𝓞 K) : K)) ≠ 0 := by
          norm_cast
          exact u.ne_zero
        exact huK hz)

/-- The logarithmic profile as an additive homomorphism from the additive presentation of units. -/
def numberFieldUnitLog : Additive (𝓞 K)ˣ →+ ((K →+* ℂ) → ℝ) where
  toFun u := numberFieldUnitLogEmbeddings (Additive.toMul u)
  map_zero' := by
    funext σ
    simp [numberFieldUnitLogEmbeddings]
  map_add' u v := by
    exact numberFieldUnitLogEmbeddings_mul (Additive.toMul u) (Additive.toMul v)

/-- Norm-zero hyperplane containing every logarithmic unit profile. -/
def numberFieldUnitLogHyperplane : Submodule ℝ ((K →+* ℂ) → ℝ) where
  carrier := {x | ∑ σ, x σ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ σ, (x σ + y σ) = 0
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change ∑ σ, c * x σ = 0
    rw [← Finset.mul_sum, hx, mul_zero]

@[simp]
theorem mem_numberFieldUnitLogHyperplane_iff (x : (K →+* ℂ) → ℝ) :
    x ∈ numberFieldUnitLogHyperplane (K := K) ↔ ∑ σ, x σ = 0 := Iff.rfl

theorem numberFieldUnitLog_mem_hyperplane (u : Additive (𝓞 K)ˣ) :
    numberFieldUnitLog u ∈ numberFieldUnitLogHyperplane (K := K) := by
  exact sum_numberFieldUnitLogEmbeddings (Additive.toMul u)

theorem range_numberFieldUnitLog_le_hyperplane :
    (numberFieldUnitLog (K := K)).range ≤
      (numberFieldUnitLogHyperplane (K := K)).toAddSubgroup := by
  rintro x ⟨u, rfl⟩
  exact numberFieldUnitLog_mem_hyperplane u

end

end GaloisForLFunctions.HTGeometry
