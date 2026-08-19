import GaloisForLFunctions.HTGeometry.SiegelWeightedGram

/-!
# Domination of congruate determinants

A form that dominates a multiple of its own diagonal dominates it after any congruence, and the
comparison passes to determinants factor by factor: each Jacobi diagonal entry of a congruate is the
value of the form on an explicit vector, and the same vector bounds the corresponding entry for the
diagonal form from above.

* `dotProduct_congr_mulVec` : a congruate evaluates the original form at the image vector.
* `posDef_congr` : congruence by an injective frame preserves positive definiteness.
* `JacobiData.det_form` : the determinant of a Jacobi form is the product of its diagonal.
* `det_congr_ge` : **the determinant comparison.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n k : ℕ}

/-- A congruate evaluates the original form at the image vector. -/
theorem dotProduct_congr_mulVec (M : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin k) ℝ) (x : Fin k → ℝ) :
    x ⬝ᵥ ((Cᵀ * M * C) *ᵥ x) = (C *ᵥ x) ⬝ᵥ (M *ᵥ (C *ᵥ x)) := by
  have h1 : (Cᵀ * M * C) *ᵥ x = Cᵀ *ᵥ (M *ᵥ (C *ᵥ x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **Congruence by an injective frame preserves positive definiteness.** -/
theorem posDef_congr {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    {C : Matrix (Fin n) (Fin k) ℝ} (hC : ∀ x : Fin k → ℝ, C *ᵥ x = 0 → x = 0) :
    (Cᵀ * M * C).PosDef := by
  have hMh : Mᵀ = M := by
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).1
    have h2 : Mᴴ = M := h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · show (Cᵀ * M * C)ᴴ = Cᵀ * M * C
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp [Matrix.transpose_mul, hMh, Matrix.mul_assoc]
  · intro x hx
    have hCx : C *ᵥ x ≠ 0 := fun hcon => hx (hC x hcon)
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hCx
    have hval : x ⬝ᵥ ((Cᵀ * M * C) *ᵥ x) = (C *ᵥ x) ⬝ᵥ (M *ᵥ (C *ᵥ x)) :=
      dotProduct_congr_mulVec M C x
    simpa [hval] using hpos

/-- The determinant of a Jacobi form is the product of its diagonal. -/
theorem JacobiData.det_form (J : JacobiData k) : J.form.det = ∏ m, J.d m := by
  show (J.Uᵀ * Matrix.diagonal J.d * J.U).det = _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    det_eq_one_of_unipotent J.upper J.unit]
  ring

/-- **A pointwise domination of forms gives a domination of congruate determinants.**  Each Jacobi
diagonal entry of the congruate is attained on an explicit vector, and that same vector bounds the
corresponding entry of the dominated congruate from above. -/
theorem det_congr_ge {A D₀ : Matrix (Fin n) (Fin n) ℝ} {c : ℝ} (hc : 0 < c)
    (hcmp : ∀ v : Fin n → ℝ, c * (v ⬝ᵥ (D₀ *ᵥ v)) ≤ v ⬝ᵥ (A *ᵥ v))
    {C : Matrix (Fin n) (Fin k) ℝ} {JG JG₀ : JacobiData k}
    (hJG : JG.form = Cᵀ * A * C) (hJG₀ : JG₀.form = Cᵀ * D₀ * C) :
    c ^ k * (Cᵀ * D₀ * C).det ≤ (Cᵀ * A * C).det := by
  have hstep : ∀ l : Fin k, c * JG₀.d l ≤ JG.d l := by
    intro l
    obtain ⟨w, hw, hval⟩ := JG.projNorm_eq_form_sub l (Pi.single l 1)
    have hdl : JG.d l
        = (Pi.single l (1 : ℝ) - w) ⬝ᵥ (JG.form *ᵥ (Pi.single l (1 : ℝ) - w)) := by
      rw [← hval, JG.projNorm_self l]
    have h0 : JG₀.d l
        ≤ (Pi.single l (1 : ℝ) - w) ⬝ᵥ (JG₀.form *ᵥ (Pi.single l (1 : ℝ) - w)) := by
      have h := JG₀.projNorm_le_form_sub l (Pi.single l 1) hw
      rwa [JG₀.projNorm_self l] at h
    set x : Fin k → ℝ := Pi.single l (1 : ℝ) - w with hx
    have hA : x ⬝ᵥ (JG.form *ᵥ x) = (C *ᵥ x) ⬝ᵥ (A *ᵥ (C *ᵥ x)) := by
      rw [hJG]; exact dotProduct_congr_mulVec A C x
    have hD : x ⬝ᵥ (JG₀.form *ᵥ x) = (C *ᵥ x) ⬝ᵥ (D₀ *ᵥ (C *ᵥ x)) := by
      rw [hJG₀]; exact dotProduct_congr_mulVec D₀ C x
    have hkey := hcmp (C *ᵥ x)
    rw [← hA, ← hD] at hkey
    calc c * JG₀.d l ≤ c * (x ⬝ᵥ (JG₀.form *ᵥ x)) := mul_le_mul_of_nonneg_left h0 hc.le
      _ ≤ x ⬝ᵥ (JG.form *ᵥ x) := hkey
      _ = JG.d l := hdl.symm
  have hdet : (Cᵀ * A * C).det = ∏ l, JG.d l := by rw [← hJG, JG.det_form]
  have hdet₀ : (Cᵀ * D₀ * C).det = ∏ l, JG₀.d l := by rw [← hJG₀, JG₀.det_form]
  have hprod : (∏ l : Fin k, (c * JG₀.d l)) = c ^ k * ∏ l, JG₀.d l := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdet, hdet₀, ← hprod]
  exact Finset.prod_le_prod (fun l _ => (mul_pos hc (JG₀.pos l)).le) (fun l _ => hstep l)

end GaloisForLFunctions.HTGeometry
