import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# The relative contraction is a congruence normalization

For a positive definite form `M = L Lᴴ` and a Hermitian form `R`, the relative operator

`K = L⁻¹ (-R) (L⁻¹)ᴴ`

satisfies the exact congruence identity

`M + R = L (1 - K) Lᴴ`.

Congruence by an invertible matrix preserves the quadratic form up to the change of variable
`v ↦ Lᴴ v`, hence preserves positive semidefiniteness, positive definiteness, and the whole family
of negative-definite subspaces.  So `M + R ≥ 0`, `-R ≤ M`, and `K ≤ I` are literally the same
statement, and the negative index of `M + R` equals that of `1 - K`.
-/

noncomputable section

namespace RHTower

open scoped Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The relative contraction attached to a congruence factor. -/
def relativeContraction (R L : Matrix n n ℂ) : Matrix n n ℂ := L⁻¹ * (-R) * (L⁻¹)ᴴ

/-- **Congruence identity.**  The Loewner sum is the congruence of `1 - K`. -/
theorem loewner_congruence_identity (M R L : Matrix n n ℂ) (hL : IsUnit L.det)
    (hM : M = L * Lᴴ) :
    M + R = L * (1 - relativeContraction R L) * Lᴴ := by
  have hinv : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hL
  have hinvH : (L⁻¹)ᴴ * Lᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  rw [relativeContraction, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [show L * (L⁻¹ * (-R) * (L⁻¹)ᴴ) * Lᴴ = (L * L⁻¹) * (-R) * ((L⁻¹)ᴴ * Lᴴ) by
    simp only [Matrix.mul_assoc]]
  rw [hinv, hinvH, Matrix.one_mul, Matrix.mul_one, hM]
  simp

omit [DecidableEq n] in
/-- The quadratic form of a congruence is the quadratic form after the change of variable. -/
theorem dotProduct_mulVec_congruence (A L : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ ((L * A * Lᴴ) *ᵥ v) = star (Lᴴ *ᵥ v) ⬝ᵥ (A *ᵥ (Lᴴ *ᵥ v)) := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [show (L * A * Lᴴ) *ᵥ v = L *ᵥ (A *ᵥ (Lᴴ *ᵥ v)) by
    simp only [← Matrix.mulVec_mulVec]]
  rw [Matrix.dotProduct_mulVec]

omit [DecidableEq n] in
/-- Congruence preserves Hermitian symmetry. -/
theorem isHermitian_congruence {A : Matrix n n ℂ} (hA : A.IsHermitian) (L : Matrix n n ℂ) :
    (L * A * Lᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, Matrix.mul_assoc]

/-- **Congruence invariance of positive semidefiniteness.** -/
theorem posSemidef_congruence_iff {A : Matrix n n ℂ} (hA : A.IsHermitian) {L : Matrix n n ℂ}
    (hL : IsUnit L.det) :
    (L * A * Lᴴ).PosSemidef ↔ A.PosSemidef := by
  have hinvH : Lᴴ * (L⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul L hL, Matrix.conjTranspose_one]
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x => ?_
    have hx := h.dotProduct_mulVec_nonneg ((L⁻¹)ᴴ *ᵥ x)
    rw [dotProduct_mulVec_congruence] at hx
    rwa [show Lᴴ *ᵥ ((L⁻¹)ᴴ *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, hinvH, Matrix.one_mulVec]] at hx
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_congruence hA L) fun x => ?_
    rw [dotProduct_mulVec_congruence]
    exact h.dotProduct_mulVec_nonneg _

/-- **Congruence invariance of positive definiteness.** -/
theorem posDef_congruence_iff {A : Matrix n n ℂ} (hA : A.IsHermitian) {L : Matrix n n ℂ}
    (hL : IsUnit L.det) :
    (L * A * Lᴴ).PosDef ↔ A.PosDef := by
  have hinvH : Lᴴ * (L⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul L hL, Matrix.conjTranspose_one]
  have hLH : IsUnit (Lᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hL.star
  constructor
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hA fun x hx => ?_
    have hne : ((L⁻¹)ᴴ *ᵥ x) ≠ 0 := by
      intro hzero
      apply hx
      have := congrArg (fun w => Lᴴ *ᵥ w) hzero
      simpa [Matrix.mulVec_mulVec, hinvH] using this
    have hpos := h.dotProduct_mulVec_pos hne
    rw [dotProduct_mulVec_congruence] at hpos
    rwa [show Lᴴ *ᵥ ((L⁻¹)ᴴ *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, hinvH, Matrix.one_mulVec]] at hpos
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_congruence hA L) fun x hx => ?_
    rw [dotProduct_mulVec_congruence]
    refine h.dotProduct_mulVec_pos ?_
    intro hzero
    apply hx
    have hLHinj : Function.Injective (fun w : n → ℂ => Lᴴ *ᵥ w) :=
      Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_iff_isUnit_det _ |>.mpr hLH)
    exact hLHinj (by simpa using hzero)

/-- **Loewner normalization.**  The Loewner inequality `M + R ≥ 0` and the contraction inequality
`K ≤ I` are the same statement. -/
theorem loewner_posSemidef_iff_contraction (M R L : Matrix n n ℂ) (hL : IsUnit L.det)
    (hM : M = L * Lᴴ) (hR : R.IsHermitian) :
    (M + R).PosSemidef ↔ (1 - relativeContraction R L).PosSemidef := by
  have hK : (1 - relativeContraction R L).IsHermitian := by
    unfold Matrix.IsHermitian relativeContraction
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg,
      hR.eq, Matrix.mul_assoc]
  rw [loewner_congruence_identity M R L hL hM]
  exact posSemidef_congruence_iff hK hL

/-- The positive definite form of the same normalization. -/
theorem loewner_posDef_iff_contraction (M R L : Matrix n n ℂ) (hL : IsUnit L.det)
    (hM : M = L * Lᴴ) (hR : R.IsHermitian) :
    (M + R).PosDef ↔ (1 - relativeContraction R L).PosDef := by
  have hK : (1 - relativeContraction R L).IsHermitian := by
    unfold Matrix.IsHermitian relativeContraction
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg,
      hR.eq, Matrix.mul_assoc]
  rw [loewner_congruence_identity M R L hL hM]
  exact posDef_congruence_iff hK hL

/-- A subspace on which a Hermitian form is negative definite. -/
def IsNegativeSubspace (A : Matrix n n ℂ) (W : Submodule ℂ (n → ℂ)) : Prop :=
  ∀ v ∈ W, v ≠ 0 → (star v ⬝ᵥ (A *ᵥ v)).re < 0

/-- **Congruence invariance of the negative index.**  The negative-definite subspaces of the
Loewner sum and of `1 - K` correspond bijectively, with equal dimensions. -/
theorem negativeSubspace_congruence (M R L : Matrix n n ℂ) (hL : IsUnit L.det)
    (hM : M = L * Lᴴ) (W : Submodule ℂ (n → ℂ)) :
    IsNegativeSubspace (M + R) W ↔
      IsNegativeSubspace (1 - relativeContraction R L)
        (W.map (Matrix.mulVecLin (Lᴴ))) := by
  have hLH : IsUnit (Lᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hL.star
  have hLHinj : Function.Injective (fun w : n → ℂ => Lᴴ *ᵥ w) :=
    Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_iff_isUnit_det _ |>.mpr hLH)
  rw [loewner_congruence_identity M R L hL hM]
  constructor
  · rintro h w ⟨v, hv, rfl⟩ hne
    have hvne : v ≠ 0 := by
      intro hzero
      apply hne
      simp [hzero]
    have := h v hv hvne
    rwa [dotProduct_mulVec_congruence] at this
  · intro h v hv hvne
    rw [dotProduct_mulVec_congruence]
    refine h _ ⟨v, hv, rfl⟩ ?_
    intro hzero
    apply hvne
    exact hLHinj (by simpa using hzero)

end RHTower
