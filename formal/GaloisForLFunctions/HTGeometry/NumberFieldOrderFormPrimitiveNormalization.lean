import GaloisForLFunctions.HTGeometry.OrderRepVectorCoordinates

/-!
# Primitive normalization of number-field order forms

A shortest primitive algebraic-integer vector is completed to a determinant-one basis and moved to
the literal first order coordinate.  The congruent form stays in the order cone, regular-
representation coordinates agree with the mixed-embedding coordinates, and the first-coordinate
energy is exactly the original primitive minimum.  No coordinate, invertibility, positivity, or
normalization premise remains in the result.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical NumberField

noncomputable section

variable {n d : ℕ} {R : Type*} [CommRing R]

noncomputable def orderConeCongrDetOne (ω : Module.Basis (Fin d) ℤ R)
    (β : Matrix (Fin n) (Fin n) R) (hdet : β.det = 1)
    (A : ↥(orderCone (nb := n) ω)) : ↥(orderCone (nb := n) ω) := by
  let P := orderRepR ω β
  have hβu : IsUnit β := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  have hPu : IsUnit P := orderRepR_isUnit ω hβu
  let B := Pᵀ * (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) * P
  have hsymm : B ∈ symmMatrices (n * d) := by
    rw [mem_symmMatrices_iff]
    change (Pᵀ * (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) * P)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      mem_symmMatrices_iff.mp A.1.2.1]
    change Pᵀ * ((A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) * P) =
      (Pᵀ * (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ)) * P
    exact (Matrix.mul_assoc _ _ _).symm
  have hbal : B ∈ balancedSubspace ω := balancedSubspace_congr A.1.2.2 β
  have hpos : B.PosDef := by
    refine posDef_congr A.2 fun x hx => ?_
    exact Matrix.mulVec_injective_of_isUnit hPu (by rw [hx, Matrix.mulVec_zero])
  exact ⟨⟨B, ⟨hsymm, hbal⟩⟩, hpos⟩

@[simp]
theorem orderConeCongrDetOne_coe (ω : Module.Basis (Fin d) ℤ R)
    (β : Matrix (Fin n) (Fin n) R) (hdet : β.det = 1)
    (A : ↥(orderCone (nb := n) ω)) :
    ((orderConeCongrDetOne ω β hdet A : ↥(orderForms (nb := n) ω)) :
        Matrix (Fin (n * d)) (Fin (n * d)) ℝ) =
      (orderRepR ω β)ᵀ *
        (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) * orderRepR ω β := rfl

def orderBasisZero (n : ℕ) (hn : 0 < n) : Fin n → R :=
  Pi.single (⟨0, hn⟩ : Fin n) 1

theorem mulVec_orderBasisZero {n : ℕ} (hn : 0 < n)
    (β : Matrix (Fin n) (Fin n) R) :
    β *ᵥ orderBasisZero (R := R) n hn = fun i => β i ⟨0, hn⟩ := by
  funext i
  rw [orderBasisZero, Matrix.mulVec_single]
  simp

structure NumberFieldOrderPrimitiveNormalization
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (A : ↥(orderCone (nb := n) (numberFieldIntegerBasis K))) where
  rank_pos : 0 < n
  a : Fin n → 𝓞 K
  primitive : ∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1
  β : Matrix (Fin n) (Fin n) (𝓞 K)
  det_β : β.det = 1
  firstCol_β : ∀ i, β i ⟨0, rank_pos⟩ = a i
  minimal : ∀ b : Fin n → 𝓞 K,
    (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
    let c := numberFieldMixedVectorContinuousLinearEquiv K n
    let M := ((A : orderForms (nb := n) (numberFieldIntegerBasis K)) :
      Matrix (Fin (n * Module.finrank ℚ K)) (Fin (n * Module.finrank ℚ K)) ℝ)
    c (numberFieldIntegerVectorEmbedding K a) ⬝ᵥ
        M.mulVec (c (numberFieldIntegerVectorEmbedding K a)) ≤
      c (numberFieldIntegerVectorEmbedding K b) ⬝ᵥ
        M.mulVec (c (numberFieldIntegerVectorEmbedding K b))
  normalized_coords :
    let e0 := orderBasisZero (R := 𝓞 K) n rank_pos
    orderRepR (numberFieldIntegerBasis K) β *ᵥ
        numberFieldMixedVectorContinuousLinearEquiv K n
          (numberFieldIntegerVectorEmbedding K e0) =
      numberFieldMixedVectorContinuousLinearEquiv K n
        (numberFieldIntegerVectorEmbedding K a)
  normalized_energy :
    let e0 := orderBasisZero (R := 𝓞 K) n rank_pos
    let c := numberFieldMixedVectorContinuousLinearEquiv K n
    let B := orderConeCongrDetOne (numberFieldIntegerBasis K) β det_β A
    c (numberFieldIntegerVectorEmbedding K e0) ⬝ᵥ
        (((B : orderForms (nb := n) (numberFieldIntegerBasis K)) :
          Matrix (Fin (n * Module.finrank ℚ K)) (Fin (n * Module.finrank ℚ K)) ℝ).mulVec
            (c (numberFieldIntegerVectorEmbedding K e0))) =
      c (numberFieldIntegerVectorEmbedding K a) ⬝ᵥ
        (((A : orderForms (nb := n) (numberFieldIntegerBasis K)) :
          Matrix (Fin (n * Module.finrank ℚ K)) (Fin (n * Module.finrank ℚ K)) ℝ).mulVec
            (c (numberFieldIntegerVectorEmbedding K a)))

theorem exists_numberFieldOrderPrimitiveNormalization
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n)
    (A : ↥(orderCone (nb := n) (numberFieldIntegerBasis K))) :
    Nonempty (NumberFieldOrderPrimitiveNormalization K n A) := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, β, hprim, hmin, hdet, hcol⟩ :=
    exists_numberFieldInteger_minimalPrimitiveVector_orderForm K n hn A
  have hβe : β *ᵥ orderBasisZero (R := 𝓞 K) n hn0 = a := by
    rw [mulVec_orderBasisZero hn0]
    funext i
    exact hcol i
  have hcoords := numberField_orderRepR_mulVec_mixedCoordinates K β
    (orderBasisZero (R := 𝓞 K) n hn0)
  rw [hβe] at hcoords
  refine ⟨⟨hn0, a, hprim, β, hdet, fun i => hcol i, hmin, hcoords, ?_⟩⟩
  dsimp only
  rw [orderConeCongrDetOne_coe, quadForm_congr, hcoords]

end

end GaloisForLFunctions.HTGeometry
