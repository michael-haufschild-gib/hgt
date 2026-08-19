import GaloisForLFunctions.HTGeometry.OrderSiegelFiniteness

/-!
# Jacobi data of a block form

A block diagonal form has block diagonal Jacobi data: its unipotent factor is the block diagonal
matrix of the blocks' unipotent factors, and its diagonal is the concatenation of the blocks'
diagonals.  Congruence by a unipotent upper triangular matrix then multiplies the unipotent factor
and leaves the diagonal alone.

Together these compute the Jacobi data of `Wᵀ E W` with `E` block diagonal and `W` unipotent upper
triangular — the shape in which a form over an order presents itself once its Gram–Schmidt over the
order has been carried out.

* `JacobiData.twist` : congruence by a unipotent upper triangular matrix.
* `blockJacobi` : **the Jacobi data of a block diagonal form.**
* `blockJacobi_twist_form` : **the Jacobi data of `Wᵀ E W`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n nb d : ℕ}

/-- Congruence by a unipotent upper triangular matrix. -/
def JacobiData.twist (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsUnipotentUpper γ) : JacobiData n where
  U := J.U * γ
  d := J.d
  pos := J.pos
  upper := (J.isUnipotentUpper.mul hγ).1
  unit := (J.isUnipotentUpper.mul hγ).2

@[simp]
theorem JacobiData.twist_d (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsUnipotentUpper γ) : (J.twist hγ).d = J.d := rfl

@[simp]
theorem JacobiData.twist_U (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsUnipotentUpper γ) : (J.twist hγ).U = J.U * γ := rfl

/-- **A twist is a congruence of the form.** -/
theorem JacobiData.twist_form (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsUnipotentUpper γ) : (J.twist hγ).form = γᵀ * J.form * γ := by
  show (J.U * γ)ᵀ * Matrix.diagonal J.d * (J.U * γ)
    = γᵀ * (J.Uᵀ * Matrix.diagonal J.d * J.U) * γ
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem blockEmbed_transpose {S : Type*}
    (M : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S)) :
    (blockEmbed M)ᵀ = blockEmbed (Matrix.of fun i j => (M j i)ᵀ) := by
  ext p q
  rfl

theorem lt_of_divNat_eq {p q : Fin (nb * d)} (hdiv : (Fin.divNat p : Fin nb) = Fin.divNat q)
    (hlt : q < p) : (Fin.modNat q : Fin d) < Fin.modNat p := by
  have hp : (p : ℕ) = ((Fin.modNat p : Fin d) : ℕ) + d * ((Fin.divNat p : Fin nb) : ℕ) := by
    have := val_finProdFinEquiv (Fin.divNat p) (Fin.modNat p)
    rw [finProdFinEquiv_divNat_modNat p] at this
    exact this
  have hq : (q : ℕ) = ((Fin.modNat q : Fin d) : ℕ) + d * ((Fin.divNat q : Fin nb) : ℕ) := by
    have := val_finProdFinEquiv (Fin.divNat q) (Fin.modNat q)
    rw [finProdFinEquiv_divNat_modNat q] at this
    exact this
  rw [hdiv] at hp
  have hlt' : (q : ℕ) < (p : ℕ) := Fin.lt_def.1 hlt
  refine Fin.lt_def.2 ?_
  omega

theorem eq_of_divNat_modNat_eq {p q : Fin (nb * d)}
    (hdiv : (Fin.divNat p : Fin nb) = Fin.divNat q)
    (hmod : (Fin.modNat p : Fin d) = Fin.modNat q) : p = q := by
  rw [← finProdFinEquiv_divNat_modNat p, ← finProdFinEquiv_divNat_modNat q, hdiv, hmod]

/-- The Jacobi data of a block diagonal form. -/
def blockJacobi (Jm : Fin nb → JacobiData d) : JacobiData (nb * d) where
  U := blockEmbed (Matrix.diagonal fun m => (Jm m).U)
  d := fun p => (Jm (Fin.divNat p)).d (Fin.modNat p)
  pos := fun p => (Jm _).pos _
  upper := by
    intro p q hqp
    show (Matrix.diagonal fun m => (Jm m).U) (Fin.divNat p) (Fin.divNat q)
      (Fin.modNat p) (Fin.modNat q) = 0
    by_cases hdiv : (Fin.divNat p : Fin nb) = Fin.divNat q
    · rw [hdiv, Matrix.diagonal_apply_eq]
      exact (Jm _).upper _ _ (lt_of_divNat_eq hdiv hqp)
    · rw [Matrix.diagonal_apply_ne _ hdiv, Matrix.zero_apply]
  unit := by
    intro p
    show (Matrix.diagonal fun m => (Jm m).U) (Fin.divNat p) (Fin.divNat p)
      (Fin.modNat p) (Fin.modNat p) = 1
    rw [Matrix.diagonal_apply_eq]
    exact (Jm _).unit _

@[simp]
theorem blockJacobi_d (Jm : Fin nb → JacobiData d) (p : Fin (nb * d)) :
    (blockJacobi Jm).d p = (Jm (Fin.divNat p)).d (Fin.modNat p) := rfl

theorem diagonal_blockJacobi_d (Jm : Fin nb → JacobiData d) :
    Matrix.diagonal (blockJacobi Jm).d
      = blockEmbed (Matrix.diagonal fun m => Matrix.diagonal (Jm m).d) := by
  classical
  ext p q
  show (Matrix.diagonal (blockJacobi Jm).d) p q
    = (Matrix.diagonal fun m => Matrix.diagonal (Jm m).d) (Fin.divNat p) (Fin.divNat q)
      (Fin.modNat p) (Fin.modNat q)
  by_cases hpq : p = q
  · subst hpq
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hpq]
    by_cases hdiv : (Fin.divNat p : Fin nb) = Fin.divNat q
    · rw [hdiv, Matrix.diagonal_apply_eq]
      refine (Matrix.diagonal_apply_ne _ fun hmod => ?_).symm
      exact hpq (eq_of_divNat_modNat_eq hdiv hmod)
    · rw [Matrix.diagonal_apply_ne _ hdiv, Matrix.zero_apply]

/-- **The form of the block diagonal Jacobi data is the block diagonal of the forms.** -/
theorem blockJacobi_form (Jm : Fin nb → JacobiData d) :
    (blockJacobi Jm).form = blockEmbed (Matrix.diagonal fun m => (Jm m).form) := by
  classical
  show (blockEmbed (Matrix.diagonal fun m => (Jm m).U))ᵀ
      * Matrix.diagonal (blockJacobi Jm).d * blockEmbed (Matrix.diagonal fun m => (Jm m).U)
    = _
  rw [blockEmbed_transpose, diagonal_blockJacobi_d, ← blockEmbed_mul, ← blockEmbed_mul]
  congr 1
  have htr : (Matrix.of fun i j => ((Matrix.diagonal fun m => (Jm m).U) j i)ᵀ)
      = Matrix.diagonal fun m => ((Jm m).U)ᵀ := by
    refine funext fun i => funext fun j => ?_
    by_cases hij : i = j
    · subst hij
      show ((Matrix.diagonal fun m => (Jm m).U) i i)ᵀ = _
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · show ((Matrix.diagonal fun m => (Jm m).U) j i)ᵀ = _
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), Matrix.diagonal_apply_ne _ hij,
        Matrix.transpose_zero]
  rw [htr, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  rfl

/-- **The Jacobi data of `Wᵀ E W` with `E` block diagonal and `W` unipotent upper triangular.** -/
theorem blockJacobi_twist_form (Jm : Fin nb → JacobiData d)
    {W : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ} (hW : IsUnipotentUpper W) :
    ((blockJacobi Jm).twist hW).form
      = Wᵀ * blockEmbed (Matrix.diagonal fun m => (Jm m).form) * W := by
  rw [JacobiData.twist_form, blockJacobi_form]

end GaloisForLFunctions.HTGeometry
