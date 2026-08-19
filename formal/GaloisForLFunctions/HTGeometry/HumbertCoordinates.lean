import GaloisForLFunctions.HTGeometry.RealOrderEmbeddings

/-!
# Humbert coordinates

A symmetric balanced form over an order with `d` real embeddings is, block by block, the pullback of
a diagonal form along the embedding matrix.  So it is determined by a matrix `H` of vectors indexed
by the embeddings — equivalently by `d` real symmetric `n × n` matrices, one per embedding.  These
are the Humbert coordinates.

* `blockUnembed` : the inverse of the flattening.
* `humbertForm` : the form attached to Humbert coordinates.
* `humbertForm_mem_balancedSubspace`, `exists_humbert_of_mem_balancedSubspace` : **balanced forms
  are exactly the Humbert forms.**
* `humbertForm_factor` : **a Humbert form is `Wᵀ E W` for the Gram–Schmidt data of the embeddings.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- The inverse of the flattening. -/
def blockUnembed {S : Type*} (N : Matrix (Fin (nb * d)) (Fin (nb * d)) S) :
    Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S) :=
  Matrix.of fun i j => Matrix.of fun k l =>
    N (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l))

theorem blockEmbed_blockUnembed {S : Type*} (N : Matrix (Fin (nb * d)) (Fin (nb * d)) S) :
    blockEmbed (blockUnembed N) = N := by
  ext p q
  show blockUnembed N (Fin.divNat p) (Fin.divNat q) (Fin.modNat p) (Fin.modNat q) = N p q
  show N (finProdFinEquiv (Fin.divNat p, Fin.modNat p))
    (finProdFinEquiv (Fin.divNat q, Fin.modNat q)) = N p q
  rw [finProdFinEquiv_divNat_modNat, finProdFinEquiv_divNat_modNat]

theorem blockUnembed_blockEmbed {S : Type*}
    (M : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S)) :
    blockUnembed (blockEmbed M) = M := by
  ext i j k l
  show blockEmbed M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) = M i j k l
  rw [blockEmbed_apply]

theorem blockEmbed_map {S S' : Type*} (f : S → S')
    (M : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S)) :
    (blockEmbed M).map f = blockEmbed (Matrix.of fun i j => (M i j).map f) := rfl

theorem blockEmbed_smulOne (ω : Module.Basis (Fin d) ℤ R) (α : R) :
    orderScalar (nb := nb) ω α
      = blockEmbed (Matrix.diagonal fun _ : Fin nb =>
          (Algebra.leftMulMatrix ω α).map (fun z : ℤ => (z : ℝ))) := by
  classical
  have hsmul : (α • (1 : Matrix (Fin nb) (Fin nb) R))
      = Matrix.diagonal fun _ : Fin nb => α := by
    ext i j
    by_cases hij : i = j
    · subst hij
      show α * (1 : Matrix (Fin nb) (Fin nb) R) i i = _
      rw [Matrix.one_apply_eq, mul_one, Matrix.diagonal_apply_eq]
    · show α * (1 : Matrix (Fin nb) (Fin nb) R) i j = _
      rw [Matrix.one_apply_ne hij, mul_zero, Matrix.diagonal_apply_ne _ hij]
  show ((orderRep ω (α • (1 : Matrix (Fin nb) (Fin nb) R))).map (fun z : ℤ => (z : ℝ))) = _
  rw [orderRep, hsmul, Matrix.diagonal_map (by simp), blockEmbed_map]
  congr 1
  refine funext fun i => funext fun j => ?_
  show ((Matrix.diagonal fun _ : Fin nb => Algebra.leftMulMatrix ω α) i j).map
      (fun z : ℤ => (z : ℝ)) = _
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
    ext k l
    simp

/-- The form attached to Humbert coordinates. -/
noncomputable def humbertForm (T : RealOrderData R d)
    (H : Matrix (Fin nb) (Fin nb) (Fin d → ℝ)) : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ :=
  blockEmbed (Matrix.of fun i j => T.embMatrixᵀ * Matrix.diagonal (H i j) * T.embMatrix)

/-- Multiplication by a ring element is self-adjoint for a pullback of a diagonal form. -/
theorem selfAdjoint_of_diagonal (T : RealOrderData R d) (c : Fin d → ℝ) (α : R) :
    (T.entryRep α)ᵀ * (T.embMatrixᵀ * Matrix.diagonal c * T.embMatrix)
      = (T.embMatrixᵀ * Matrix.diagonal c * T.embMatrix) * T.entryRep α := by
  have hcomm := T.embMatrix_mul_entryRep α
  have hT : (T.entryRep α)ᵀ * T.embMatrixᵀ
      = T.embMatrixᵀ * Matrix.diagonal (fun v => T.emb v α) := by
    rw [← Matrix.transpose_mul, hcomm, Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc (T.entryRep α)ᵀ * (T.embMatrixᵀ * Matrix.diagonal c * T.embMatrix)
      = ((T.entryRep α)ᵀ * T.embMatrixᵀ) * Matrix.diagonal c * T.embMatrix := by
        simp only [Matrix.mul_assoc]
    _ = T.embMatrixᵀ * (Matrix.diagonal (fun v => T.emb v α) * Matrix.diagonal c)
          * T.embMatrix := by rw [hT]; simp only [Matrix.mul_assoc]
    _ = T.embMatrixᵀ * (Matrix.diagonal c * Matrix.diagonal (fun v => T.emb v α))
          * T.embMatrix := by
        have hfun : (fun i => T.emb i α * c i) = (fun i => c i * T.emb i α) := by
          funext v
          ring
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, hfun]
    _ = T.embMatrixᵀ * Matrix.diagonal c * (Matrix.diagonal (fun v => T.emb v α)
          * T.embMatrix) := by simp only [Matrix.mul_assoc]
    _ = (T.embMatrixᵀ * Matrix.diagonal c * T.embMatrix) * T.entryRep α := by
        rw [← hcomm]; simp only [Matrix.mul_assoc]

theorem orderScalar_transpose (T : RealOrderData R d) (α : R) :
    (orderScalar (nb := nb) T.basis α)ᵀ
      = blockEmbed (Matrix.diagonal fun _ : Fin nb => (T.entryRep α)ᵀ) := by
  classical
  rw [blockEmbed_smulOne, blockEmbed_transpose]
  congr 1
  refine funext fun i => funext fun j => ?_
  show ((Matrix.diagonal fun _ : Fin nb => T.entryRep α) j i)ᵀ = _
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), Matrix.diagonal_apply_ne _ hij,
      Matrix.transpose_zero]

theorem orderScalar_eq_blockEmbed (T : RealOrderData R d) (α : R) :
    orderScalar (nb := nb) T.basis α
      = blockEmbed (Matrix.diagonal fun _ : Fin nb => T.entryRep α) := blockEmbed_smulOne _ _

/-- **A Humbert form is balanced.** -/
theorem humbertForm_mem_balancedSubspace (T : RealOrderData R d)
    (H : Matrix (Fin nb) (Fin nb) (Fin d → ℝ)) :
    humbertForm T H ∈ balancedSubspace (nb := nb) T.basis := by
  classical
  intro α
  rw [orderScalar_transpose, orderScalar_eq_blockEmbed, humbertForm, ← blockEmbed_mul,
    ← blockEmbed_mul]
  congr 1
  refine funext fun i => funext fun j => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact selfAdjoint_of_diagonal T (H i j) α

/-- **Every balanced form has Humbert coordinates.** -/
theorem exists_humbert_of_mem_balancedSubspace (T : RealOrderData R d)
    {A : Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ}
    (hA : A ∈ balancedSubspace (nb := nb) T.basis) :
    ∃ H : Matrix (Fin nb) (Fin nb) (Fin d → ℝ), A = humbertForm T H := by
  classical
  have hblock : ∀ i j : Fin nb, ∀ α : R,
      (T.entryRep α)ᵀ * (blockUnembed A i j) = (blockUnembed A i j) * T.entryRep α := by
    intro i j α
    have h := hA α
    rw [orderScalar_transpose, orderScalar_eq_blockEmbed, ← blockEmbed_blockUnembed A,
      ← blockEmbed_mul, ← blockEmbed_mul] at h
    have hb := blockEmbed_injective h
    have hij := congrFun (congrFun hb i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
    exact hij
  choose c hc using fun p : Fin nb × Fin nb =>
    exists_diagonal_of_selfAdjoint (T := T) (hblock p.1 p.2)
  refine ⟨Matrix.of fun i j => c (i, j), ?_⟩
  rw [humbertForm, ← blockEmbed_blockUnembed A]
  congr 1
  refine funext fun i => funext fun j => ?_
  exact hc (i, j)

theorem divNat_le_of_le {p q : Fin (nb * d)} (hqp : q ≤ p) :
    ((Fin.divNat q : Fin nb) : ℕ) ≤ (Fin.divNat p : Fin nb) :=
  Nat.div_le_div_right (Fin.le_def.1 hqp)

/-- **A block upper unitriangular matrix flattens to a unipotent upper triangular one.** -/
theorem isUnipotentUpper_blockEmbed
    {M : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) ℝ)}
    (hlow : ∀ i j : Fin nb, j < i → M i j = 0) (hdiag : ∀ i, M i i = 1) :
    IsUnipotentUpper (blockEmbed M) := by
  classical
  constructor
  · intro p q hqp
    show M (Fin.divNat p) (Fin.divNat q) (Fin.modNat p) (Fin.modNat q) = 0
    by_cases hdiv : (Fin.divNat p : Fin nb) = Fin.divNat q
    · rw [hdiv, hdiag]
      refine Matrix.one_apply_ne ?_
      intro hmod
      exact absurd (lt_of_divNat_eq hdiv hqp) (by rw [hmod]; exact lt_irrefl _)
    · have hle := divNat_le_of_le (le_of_lt hqp)
      have hlt : (Fin.divNat q : Fin nb) < Fin.divNat p :=
        Fin.lt_def.2 (lt_of_le_of_ne hle fun hcon => hdiv (Fin.ext hcon.symm))
      rw [hlow _ _ hlt, Matrix.zero_apply]
  · intro p
    show M (Fin.divNat p) (Fin.divNat p) (Fin.modNat p) (Fin.modNat p) = 1
    rw [hdiag, Matrix.one_apply_eq]

/-- The unipotent factor attached to a family of Jacobi data, one per embedding. -/
noncomputable def humbertUnipotent (T : RealOrderData R d) (Jv : Fin d → JacobiData nb) :
    Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ :=
  blockEmbed (Matrix.of fun m i =>
    T.embMatrix⁻¹ * Matrix.diagonal (fun v => (Jv v).U m i) * T.embMatrix)

/-- The block diagonal factor attached to a family of Jacobi data. -/
noncomputable def humbertDiagonal (T : RealOrderData R d) (Jv : Fin d → JacobiData nb) :
    Matrix (Fin (nb * d)) (Fin (nb * d)) ℝ :=
  blockEmbed (Matrix.diagonal fun m =>
    T.embMatrixᵀ * Matrix.diagonal (fun v => (Jv v).d m) * T.embMatrix)

theorem isUnipotentUpper_humbertUnipotent (T : RealOrderData R d) (Jv : Fin d → JacobiData nb) :
    IsUnipotentUpper (humbertUnipotent T Jv) := by
  classical
  have hu : IsUnit T.embMatrix.det := T.invertible
  refine isUnipotentUpper_blockEmbed (fun m i him => ?_) (fun m => ?_)
  · show T.embMatrix⁻¹ * Matrix.diagonal (fun v => (Jv v).U m i) * T.embMatrix = 0
    have hz : (fun v => (Jv v).U m i) = fun _ : Fin d => (0 : ℝ) := by
      funext v
      exact (Jv v).upper m i him
    rw [hz, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]
  · show T.embMatrix⁻¹ * Matrix.diagonal (fun v => (Jv v).U m m) * T.embMatrix = 1
    have ho : (fun v => (Jv v).U m m) = fun _ : Fin d => (1 : ℝ) := by
      funext v
      exact (Jv v).unit m
    rw [ho, Matrix.diagonal_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]

/-- **Humbert coordinates factor through the Gram–Schmidt data of the embeddings.** -/
theorem humbertForm_factor (T : RealOrderData R d) (Jv : Fin d → JacobiData nb) :
    humbertForm T (Matrix.of fun i j => fun v => (Jv v).form i j)
      = (humbertUnipotent T Jv)ᵀ * humbertDiagonal T Jv * humbertUnipotent T Jv := by
  classical
  have hu : IsUnit T.embMatrix.det := T.invertible
  have huT : IsUnit (T.embMatrixᵀ).det := by rw [Matrix.det_transpose]; exact hu
  set Mblk : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) ℝ) :=
    Matrix.of fun m i => T.embMatrix⁻¹ * Matrix.diagonal (fun v => (Jv v).U m i) * T.embMatrix
    with hMblk
  set Eblk : Fin nb → Matrix (Fin d) (Fin d) ℝ :=
    fun m => T.embMatrixᵀ * Matrix.diagonal (fun v => (Jv v).d m) * T.embMatrix with hEblk
  have hW : humbertUnipotent T Jv = blockEmbed Mblk := rfl
  have hE : humbertDiagonal T Jv = blockEmbed (Matrix.diagonal Eblk) := rfl
  have hsum : ∀ f : Fin nb → Fin d → ℝ,
      (∑ m : Fin nb, T.embMatrixᵀ * Matrix.diagonal (f m) * T.embMatrix)
        = T.embMatrixᵀ * Matrix.diagonal (fun v => ∑ m : Fin nb, f m v) * T.embMatrix := by
    intro f
    have hdiag : Matrix.diagonal (fun v => ∑ m : Fin nb, f m v)
        = ∑ m : Fin nb, Matrix.diagonal (f m) := by
      ext v w
      by_cases hvw : v = w
      · subst hvw
        rw [Matrix.diagonal_apply_eq, Matrix.sum_apply]
        exact Finset.sum_congr rfl fun m _ => (Matrix.diagonal_apply_eq (f m) v).symm
      · rw [Matrix.diagonal_apply_ne _ hvw, Matrix.sum_apply]
        exact (Finset.sum_eq_zero fun m _ => Matrix.diagonal_apply_ne _ hvw).symm
    rw [hdiag, Finset.mul_sum, Finset.sum_mul]
  rw [hW, hE, blockEmbed_transpose, ← blockEmbed_mul, ← blockEmbed_mul, humbertForm]
  congr 1
  refine funext fun i => funext fun j => ?_
  have hterm : ∀ m : Fin nb, (Mblk m i)ᵀ * Eblk m * Mblk m j
      = T.embMatrixᵀ
        * Matrix.diagonal (fun v => (Jv v).d m * (Jv v).U m i * (Jv v).U m j)
        * T.embMatrix := by
    intro m
    have hd3 : Matrix.diagonal (fun v => (Jv v).U m i) * Matrix.diagonal (fun v => (Jv v).d m)
        * Matrix.diagonal (fun v => (Jv v).U m j)
        = Matrix.diagonal (fun v => (Jv v).d m * (Jv v).U m i * (Jv v).U m j) := by
      have hf : (fun v => (Jv v).U m i * (Jv v).d m * (Jv v).U m j)
          = fun v => (Jv v).d m * (Jv v).U m i * (Jv v).U m j := by
        funext v
        ring
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, hf]
    show (T.embMatrix⁻¹ * Matrix.diagonal (fun v => (Jv v).U m i) * T.embMatrix)ᵀ
        * (T.embMatrixᵀ * Matrix.diagonal (fun v => (Jv v).d m) * T.embMatrix)
        * (T.embMatrix⁻¹ * Matrix.diagonal (fun v => (Jv v).U m j) * T.embMatrix) = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.transpose_nonsing_inv, ← hd3]
    calc _ = T.embMatrixᵀ * Matrix.diagonal (fun v => (Jv v).U m i)
            * ((T.embMatrixᵀ)⁻¹ * T.embMatrixᵀ) * Matrix.diagonal (fun v => (Jv v).d m)
            * (T.embMatrix * T.embMatrix⁻¹) * Matrix.diagonal (fun v => (Jv v).U m j)
            * T.embMatrix := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [Matrix.nonsing_inv_mul _ huT, Matrix.mul_nonsing_inv _ hu]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hMt : ((Matrix.of fun a b => (Mblk b a)ᵀ) * Matrix.diagonal Eblk)
      = Matrix.of fun a m => (Mblk m a)ᵀ * Eblk m := by
    refine funext fun a => funext fun m => ?_
    exact Matrix.mul_diagonal Eblk _ a m
  have hR : T.embMatrixᵀ * Matrix.diagonal (fun v => (Jv v).form i j) * T.embMatrix
      = ∑ m : Fin nb, T.embMatrixᵀ
          * Matrix.diagonal (fun v => (Jv v).d m * (Jv v).U m i * (Jv v).U m j)
          * T.embMatrix := by
    have hfun : (fun v => (Jv v).form i j)
        = fun v => ∑ m : Fin nb, (Jv v).d m * (Jv v).U m i * (Jv v).U m j := by
      funext v
      exact (Jv v).form_apply i j
    rw [hsum, hfun]
  rw [hMt, Matrix.mul_apply]
  show T.embMatrixᵀ * Matrix.diagonal (fun v => (Jv v).form i j) * T.embMatrix = _
  rw [hR]
  exact (Finset.sum_congr rfl fun m _ => hterm m).symm

end GaloisForLFunctions.HTGeometry
