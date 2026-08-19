import GaloisForLFunctions.HTGeometry.OrderRoundingPotential

/-!
# The action in Humbert coordinates

Congruence of a Humbert form by the regular representation of a matrix over the order is, place by
place, congruence of the corresponding real form by the matrix of embeddings.  So the action of
`SL_n(R)` on its symmetric space is the diagonal action on `d` copies of the cone of positive
definite real `n × n` forms.

This is what lets the reduction be carried out in Humbert coordinates, with `R`-shears and `R`-swaps
acting simultaneously at every embedding.

* `placeMatrix` : the matrix of embeddings of a matrix over the order.
* `embConj_diagonal` : the one-block computation.
* `humbertForm_congr` : **congruence is placewise congruence.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- The matrix of embeddings of a matrix over the order. -/
def placeMatrix (T : RealOrderData R d) (v : Fin d) (N : Matrix (Fin nb) (Fin nb) R) :
    Matrix (Fin nb) (Fin nb) ℝ :=
  Matrix.of fun i j => T.emb v (N i j)

theorem sum_embConj (T : RealOrderData R d) {ι : Type*} [Fintype ι] (c : ι → Fin d → ℝ) :
    (∑ x : ι, T.embMatrixᵀ * Matrix.diagonal (c x) * T.embMatrix)
      = T.embMatrixᵀ * Matrix.diagonal (fun v => ∑ x : ι, c x v) * T.embMatrix := by
  classical
  have hdiag : Matrix.diagonal (fun v => ∑ x : ι, c x v)
      = ∑ x : ι, Matrix.diagonal (c x) := by
    ext v w
    by_cases hvw : v = w
    · subst hvw
      rw [Matrix.diagonal_apply_eq, Matrix.sum_apply]
      exact Finset.sum_congr rfl fun x _ => (Matrix.diagonal_apply_eq (c x) v).symm
    · rw [Matrix.diagonal_apply_ne _ hvw, Matrix.sum_apply]
      exact (Finset.sum_eq_zero fun x _ => Matrix.diagonal_apply_ne _ hvw).symm
  rw [hdiag, Finset.mul_sum, Finset.sum_mul]

/-- **The one-block computation**: conjugating a pullback of a diagonal form by regular
representations multiplies the diagonal by the corresponding embeddings. -/
theorem embConj_diagonal (T : RealOrderData R d) (α β : R) (c : Fin d → ℝ) :
    (T.entryRep α)ᵀ * (T.embMatrixᵀ * Matrix.diagonal c * T.embMatrix) * T.entryRep β
      = T.embMatrixᵀ
        * Matrix.diagonal (fun v => T.emb v α * c v * T.emb v β) * T.embMatrix := by
  have hcomm := T.embMatrix_mul_entryRep β
  have hT : (T.entryRep α)ᵀ * T.embMatrixᵀ
      = T.embMatrixᵀ * Matrix.diagonal (fun v => T.emb v α) := by
    rw [← Matrix.transpose_mul, T.embMatrix_mul_entryRep α, Matrix.transpose_mul,
      Matrix.diagonal_transpose]
  have hd : Matrix.diagonal (fun v => T.emb v α) * Matrix.diagonal c
      * Matrix.diagonal (fun v => T.emb v β)
      = Matrix.diagonal (fun v => T.emb v α * c v * T.emb v β) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  calc (T.entryRep α)ᵀ * (T.embMatrixᵀ * Matrix.diagonal c * T.embMatrix) * T.entryRep β
      = ((T.entryRep α)ᵀ * T.embMatrixᵀ) * Matrix.diagonal c
          * (T.embMatrix * T.entryRep β) := by simp only [Matrix.mul_assoc]
    _ = (T.embMatrixᵀ * Matrix.diagonal (fun v => T.emb v α)) * Matrix.diagonal c
          * (Matrix.diagonal (fun v => T.emb v β) * T.embMatrix) := by rw [hT, hcomm]
    _ = T.embMatrixᵀ * (Matrix.diagonal (fun v => T.emb v α) * Matrix.diagonal c
          * Matrix.diagonal (fun v => T.emb v β)) * T.embMatrix := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hd]

theorem orderRepR_eq_blockEmbed (T : RealOrderData R d) (N : Matrix (Fin nb) (Fin nb) R) :
    orderRepR T.basis N = blockEmbed (Matrix.of fun i j => T.entryRep (N i j)) := rfl

/-- **Congruence of a Humbert form is placewise congruence.** -/
theorem humbertForm_congr (T : RealOrderData R d)
    (H : Matrix (Fin nb) (Fin nb) (Fin d → ℝ)) (N : Matrix (Fin nb) (Fin nb) R) :
    (orderRepR T.basis N)ᵀ * humbertForm T H * orderRepR T.basis N
      = humbertForm T (Matrix.of fun i j => fun v =>
          ((placeMatrix T v N)ᵀ * (Matrix.of fun a b => H a b v) * placeMatrix T v N) i j) := by
  classical
  rw [orderRepR_eq_blockEmbed, blockEmbed_transpose, humbertForm, ← blockEmbed_mul,
    ← blockEmbed_mul, humbertForm]
  congr 1
  refine funext fun i => funext fun j => ?_
  have hfun : (fun v => ∑ b : Fin nb, ∑ a : Fin nb,
        T.emb v (N a i) * H a b v * T.emb v (N b j))
      = fun v => ((placeMatrix T v N)ᵀ * (Matrix.of fun a b => H a b v)
          * placeMatrix T v N) i j := by
    funext v
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    rfl
  calc _ = ∑ b : Fin nb, ∑ a : Fin nb,
          (T.entryRep (N a i))ᵀ * (T.embMatrixᵀ * Matrix.diagonal (H a b) * T.embMatrix)
            * T.entryRep (N b j) := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
        rfl
    _ = ∑ b : Fin nb, ∑ a : Fin nb, T.embMatrixᵀ
          * Matrix.diagonal (fun v => T.emb v (N a i) * H a b v * T.emb v (N b j))
          * T.embMatrix :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
          embConj_diagonal T (N a i) (N b j) (H a b)
    _ = T.embMatrixᵀ * Matrix.diagonal (fun v => ∑ b : Fin nb, ∑ a : Fin nb,
          T.emb v (N a i) * H a b v * T.emb v (N b j)) * T.embMatrix := by
        rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => sum_embConj T
              (fun a : Fin nb => fun v => T.emb v (N a i) * H a b v * T.emb v (N b j))),
          sum_embConj]
    _ = _ := by rw [hfun]; rfl

end GaloisForLFunctions.HTGeometry
