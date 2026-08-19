import GaloisForLFunctions.HTGeometry.PositiveMapTraceNormContraction

/-!
# The Kadison--Schwarz inequality for two-positive unital maps

For a unital completely positive map `Θ` of matrices,

`Θ(X)ᴴ Θ(X) ≤ Θ(Xᴴ X)`.

The proof is the two-by-two dilation: the block matrix `[[XᴴX, Xᴴ], [X, 1]]` is `CᴴC` for
`C = [[X, 1], [0, 0]]` and hence positive; two-positivity carries it to
`[[Θ(XᴴX), Θ(X)ᴴ], [Θ(X), 1]]`, and a block matrix of that shape is positive exactly when its
corner dominates `Θ(X)ᴴΘ(X)`.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Quadratic forms of two-by-two block matrices -/

/-- A vector with a two-dimensional ancilla index, assembled from its two halves. -/
def blockVec2 (v₀ v₁ : n → ℂ) : n × Fin 2 → ℂ := fun p => ![v₀, v₁] p.2 p.1

omit [DecidableEq n] in
theorem dotProduct_blockMat_two (B : Fin 2 → Fin 2 → Matrix n n ℂ) (v₀ v₁ : n → ℂ) :
    star (blockVec2 v₀ v₁) ⬝ᵥ (blockMat B) *ᵥ (blockVec2 v₀ v₁)
      = star v₀ ⬝ᵥ (B 0 0) *ᵥ v₀ + star v₀ ⬝ᵥ (B 0 1) *ᵥ v₁
        + (star v₁ ⬝ᵥ (B 1 0) *ᵥ v₀ + star v₁ ⬝ᵥ (B 1 1) *ᵥ v₁) := by
  simp only [dotProduct, Matrix.mulVec, blockMat_apply, blockVec2, Pi.star_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring

/-- **The two-by-two positivity criterion.**  If `[[A, Bᴴ], [B, 1]]` is positive then
`BᴴB ≤ A`. -/
theorem sub_conjTranspose_mul_posSemidef {A B : Matrix n n ℂ}
    (h : (blockMat ![![A, Bᴴ], ![B, 1]]).PosSemidef) : (A - Bᴴ * B).PosSemidef := by
  have hAherm : A.IsHermitian := by
    have hb := h.isHermitian
    show Aᴴ = A
    ext i j
    have hij := congrFun (congrFun hb (i, 0)) (j, 0)
    simpa [blockMat, Matrix.conjTranspose_apply] using hij
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · show (A - Bᴴ * B)ᴴ = A - Bᴴ * B
    rw [Matrix.conjTranspose_sub, hAherm.eq, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  · intro v
    have hq := h.dotProduct_mulVec_nonneg (blockVec2 v (-(B *ᵥ v)))
    rw [dotProduct_blockMat_two] at hq
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hq
    have e1 : star v ⬝ᵥ Bᴴ *ᵥ (-(B *ᵥ v)) = -(star v ⬝ᵥ (Bᴴ * B) *ᵥ v) := by
      rw [Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec]
    have e2 : star (-(B *ᵥ v)) ⬝ᵥ B *ᵥ v + star (-(B *ᵥ v)) ⬝ᵥ (1 : Matrix n n ℂ) *ᵥ
        (-(B *ᵥ v)) = 0 := by
      rw [Matrix.one_mulVec, star_neg, neg_dotProduct, neg_dotProduct, dotProduct_neg]
      ring
    rw [e1, e2, add_zero] at hq
    have e3 : star v ⬝ᵥ (A - Bᴴ * B) *ᵥ v
        = star v ⬝ᵥ A *ᵥ v + -(star v ⬝ᵥ (Bᴴ * B) *ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      ring
    rw [e3]
    exact hq

/-- The source of the Schwarz inequality: `[[XᴴX, Xᴴ], [X, 1]]` is positive. -/
theorem posSemidef_schwarzBlock (X : Matrix n n ℂ) :
    (blockMat ![![Xᴴ * X, Xᴴ], ![X, (1 : Matrix n n ℂ)]]).PosSemidef := by
  have hfac : blockMat ![![Xᴴ * X, Xᴴ], ![X, (1 : Matrix n n ℂ)]]
      = (blockMat ![![X, (1 : Matrix n n ℂ)], ![0, 0]])ᴴ
        * blockMat ![![X, (1 : Matrix n n ℂ)], ![0, 0]] := by
    rw [blockMat_conjTranspose, blockMat_mul]
    congr 1
    funext a b
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]
  rw [hfac]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ## Completely positive maps -/

/-- A completely positive linear map of matrices. -/
structure IsCP (Φ : Matrix n n ℂ → Matrix n n ℂ) : Prop where
  /-- Additivity. -/
  map_add : ∀ X Y, Φ (X + Y) = Φ X + Φ Y
  /-- Complex homogeneity. -/
  map_smul : ∀ (c : ℂ) (X), Φ (c • X) = c • Φ X
  /-- Every ancilla amplification is positive. -/
  cp : ∀ (m : Type) [Fintype m] [DecidableEq m] (X : Matrix (n × m) (n × m) ℂ),
      X.PosSemidef → (amplify Φ m X).PosSemidef

namespace IsCP

variable {Φ : Matrix n n ℂ → Matrix n n ℂ}

omit [Fintype n] [DecidableEq n] in
theorem posSemidef_blockMat_fin_one' (X : Matrix n n ℂ) :
    (blockMat (fun _ _ : Fin 1 => X)).PosSemidef ↔ X.PosSemidef := by
  have he : blockMat (fun _ _ : Fin 1 => X)
      = X.submatrix (Equiv.prodUnique n (Fin 1)) (Equiv.prodUnique n (Fin 1)) := rfl
  rw [he]
  exact Matrix.posSemidef_submatrix_equiv _

/-- A completely positive map is positive. -/
theorem pos (hΦ : IsCP Φ) {X : Matrix n n ℂ} (hX : X.PosSemidef) : (Φ X).PosSemidef := by
  have h1 : (blockMat (fun _ _ : Fin 1 => X)).PosSemidef :=
    (posSemidef_blockMat_fin_one' X).mpr hX
  have h2 := hΦ.cp (Fin 1) _ h1
  rw [amplify_blockMat] at h2
  exact (posSemidef_blockMat_fin_one' (Φ X)).mp h2

omit [Fintype n] [DecidableEq n] in
theorem map_zero (hΦ : IsCP Φ) : Φ 0 = 0 := positiveLinear_map_zero hΦ.map_smul

omit [Fintype n] [DecidableEq n] in
theorem map_sub (hΦ : IsCP Φ) (X Y : Matrix n n ℂ) : Φ (X - Y) = Φ X - Φ Y :=
  positiveLinear_map_sub hΦ.map_add hΦ.map_smul X Y

theorem map_conjTranspose (hΦ : IsCP Φ) (X : Matrix n n ℂ) : Φ Xᴴ = (Φ X)ᴴ :=
  positiveLinear_map_conjTranspose hΦ.map_add hΦ.map_smul (fun _ h => hΦ.pos h) X

/-- **The Kadison--Schwarz inequality.** -/
theorem schwarz (hΦ : IsCP Φ) (hunit : Φ 1 = 1) (X : Matrix n n ℂ) :
    (Φ X)ᴴ * Φ X ≤ Φ (Xᴴ * X) := by
  have hsrc := hΦ.cp (Fin 2) _ (posSemidef_schwarzBlock X)
  rw [amplify_blockMat] at hsrc
  have himg : (fun a b => Φ (![![Xᴴ * X, Xᴴ], ![X, (1 : Matrix n n ℂ)]] a b))
      = ![![Φ (Xᴴ * X), (Φ X)ᴴ], ![Φ X, (1 : Matrix n n ℂ)]] := by
    funext a b
    fin_cases a <;> fin_cases b <;>
      simp [hunit, hΦ.map_conjTranspose]
  rw [himg] at hsrc
  rw [Matrix.le_iff]
  exact sub_conjTranspose_mul_posSemidef hsrc

end IsCP

end

end GaloisForLFunctions.HTGeometry
