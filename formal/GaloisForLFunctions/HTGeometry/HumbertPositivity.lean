import GaloisForLFunctions.HTGeometry.HumbertAmbientJacobi

/-!
# Positivity in Humbert coordinates

Congruence by the block diagonal matrix of copies of `Ω⁻¹` strips the embedding matrix from a Humbert
form, leaving the matrix whose blocks are the diagonal matrices of the coordinates.  Restricting that
to the indices of a single embedding is a principal submatrix, so positive definiteness of the form
passes to each of its `d` place components.

With the converse — a Humbert form built from positive definite place components is the form of a
Jacobi datum — this identifies the symmetric space of `SL_n(R)` with `d` copies of the cone of
positive definite real `n × n` forms.

* `humbertUnscale` : the block diagonal of copies of `Ω⁻¹`.
* `posDef_humbert_place` : **positivity passes to the place components.**
* `exists_humbert_jacobi` : **every point of the symmetric space has Gram–Schmidt data at every
  embedding.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- The block diagonal matrix of copies of `Ω⁻¹`. -/
noncomputable def humbertUnscale (T : RealOrderData R d) :
    Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ :=
  blockEmbed (Matrix.diagonal fun _ : Fin nb => T.embMatrix⁻¹)

theorem humbertUnscale_isUnit (T : RealOrderData R d) :
    IsUnit (humbertUnscale (nb := nb) T) := by
  classical
  have hu : IsUnit T.embMatrix.det := T.invertible
  have hone : (Matrix.diagonal fun _ : Fin nb => T.embMatrix⁻¹)
      * (Matrix.diagonal fun _ : Fin nb => T.embMatrix) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun _ : Fin nb => T.embMatrix⁻¹ * T.embMatrix) = fun _ : Fin nb =>
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
      funext m
      rw [Matrix.nonsing_inv_mul _ hu]
    rw [this, Matrix.diagonal_one]
  have hone' : (Matrix.diagonal fun _ : Fin nb => T.embMatrix)
      * (Matrix.diagonal fun _ : Fin nb => T.embMatrix⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun _ : Fin nb => T.embMatrix * T.embMatrix⁻¹) = fun _ : Fin nb =>
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
      funext m
      rw [Matrix.mul_nonsing_inv _ hu]
    rw [this, Matrix.diagonal_one]
  refine ⟨⟨humbertUnscale T, blockEmbed (Matrix.diagonal fun _ : Fin nb => T.embMatrix), ?_, ?_⟩,
    rfl⟩
  · rw [humbertUnscale, ← blockEmbed_mul, hone, blockEmbed_one]
  · rw [humbertUnscale, ← blockEmbed_mul, hone', blockEmbed_one]

/-- **Stripping the embedding matrix from a Humbert form.** -/
theorem humbertUnscale_congr (T : RealOrderData R d)
    (H : Matrix (Fin nb) (Fin nb) (Fin d → ℝ)) :
    (humbertUnscale (nb := nb) T)ᵀ * humbertForm T H * humbertUnscale T
      = blockEmbed (Matrix.of fun i j => Matrix.diagonal (H i j)) := by
  classical
  have hu : IsUnit T.embMatrix.det := T.invertible
  have huT : IsUnit (T.embMatrixᵀ).det := by rw [Matrix.det_transpose]; exact hu
  have htr : (Matrix.of fun a b => ((Matrix.diagonal fun _ : Fin nb => T.embMatrix⁻¹) b a)ᵀ)
      = Matrix.diagonal fun _ : Fin nb => (T.embMatrix⁻¹)ᵀ := by
    refine funext fun a => funext fun b => ?_
    show ((Matrix.diagonal fun _ : Fin nb => T.embMatrix⁻¹) b a)ᵀ = _
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hab), Matrix.diagonal_apply_ne _ hab,
        Matrix.transpose_zero]
  rw [humbertUnscale, humbertForm, blockEmbed_transpose, htr, ← blockEmbed_mul, ← blockEmbed_mul]
  congr 1
  refine funext fun i => funext fun j => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_nonsing_inv]
  show (T.embMatrixᵀ)⁻¹ * (T.embMatrixᵀ * Matrix.diagonal (H i j) * T.embMatrix)
      * T.embMatrix⁻¹ = _
  calc (T.embMatrixᵀ)⁻¹ * (T.embMatrixᵀ * Matrix.diagonal (H i j) * T.embMatrix)
        * T.embMatrix⁻¹
      = ((T.embMatrixᵀ)⁻¹ * T.embMatrixᵀ) * Matrix.diagonal (H i j)
          * (T.embMatrix * T.embMatrix⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal (H i j) := by
        rw [Matrix.nonsing_inv_mul _ huT, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
          Matrix.mul_one]

/-- **Positive definiteness of a Humbert form passes to its place components.** -/
theorem posDef_humbert_place (T : RealOrderData R d)
    {H : Matrix (Fin nb) (Fin nb) (Fin d → ℝ)} (hA : (humbertForm T H).PosDef) (v : Fin d) :
    (Matrix.of fun i j => H i j v : Matrix (Fin nb) (Fin nb) ℝ).PosDef := by
  classical
  have hC : (blockEmbed (Matrix.of fun i j => Matrix.diagonal (H i j))).PosDef := by
    rw [← humbertUnscale_congr T H]
    refine posDef_congr hA fun x hx => ?_
    exact Matrix.mulVec_injective_of_isUnit (humbertUnscale_isUnit T)
      (by rw [hx, Matrix.mulVec_zero])
  have hf : Function.Injective (fun i : Fin nb => finProdFinEquiv (i, v)) := by
    intro a b hab
    have := finProdFinEquiv.injective hab
    exact congrArg Prod.fst this
  have hsub := hC.submatrix hf
  have heq : (Matrix.of fun i j => H i j v : Matrix (Fin nb) (Fin nb) ℝ)
      = (blockEmbed (Matrix.of fun i j => Matrix.diagonal (H i j))).submatrix
        (fun i : Fin nb => finProdFinEquiv (i, v)) (fun i : Fin nb => finProdFinEquiv (i, v)) := by
    ext i j
    rw [Matrix.submatrix_apply, blockEmbed_apply]
    show H i j v = (Matrix.diagonal (H i j)) v v
    rw [Matrix.diagonal_apply_eq]
  rw [heq]
  exact hsub

/-- **Every symmetric balanced positive definite form has Gram–Schmidt data at every embedding.** -/
theorem exists_humbert_jacobi (T : RealOrderData R d)
    {A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ}
    (hbal : A ∈ balancedSubspace (nb := nb) T.basis) (hpos : A.PosDef) :
    ∃ Jv : Fin d → JacobiData nb,
      A = humbertForm T (Matrix.of fun i j => fun v => (Jv v).form i j) := by
  classical
  obtain ⟨H, hH⟩ := exists_humbert_of_mem_balancedSubspace T hbal
  subst hH
  have hplace : ∀ v : Fin d,
      (Matrix.of fun i j => H i j v : Matrix (Fin nb) (Fin nb) ℝ).PosDef :=
    fun v => posDef_humbert_place T hpos v
  choose Jv hJv using fun v : Fin d => exists_jacobiData (hplace v)
  refine ⟨Jv, ?_⟩
  congr 1
  refine funext fun i => funext fun j => funext fun v => ?_
  show H i j v = (Jv v).form i j
  rw [hJv v]
  rfl

end GaloisForLFunctions.HTGeometry
