import GaloisForLFunctions.HTGeometry.CommutingNormalMatrixEigenbasis
import GaloisForLFunctions.HTGeometry.FermionicZeroBraidAnchorCommutation

/-!
# Fermionic zero-braid local product diagonalization

This file closes the finite-dimensional operator-Schmidt gap left by
`FermionicZeroBraidAnchorCommutation`.  Instead of choosing a minimal operator-Schmidt
decomposition, it uses all concrete left and right matrix blocks.  The two zero-anchor leg
commutation laws make those block families commute.  Unitarity upgrades the same laws to mixed
commutation with adjoints, so both block families are commuting normal families.  Their joint
orthonormal eigenbases form a local product basis in which every off-diagonal matrix coefficient
vanishes.

The capstone theorem starts with the adjacent braid equation and the exact flip anchor
`B(0) = c P`, converts by the existing right-flip theorem, applies the zero-anchor commutation
law, proves product diagonality for the right flip, and conjugates by `P` to obtain the paper's
left flip `P B(x)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## Concrete leg coefficients and operator blocks -/

@[simp]
theorem threeParticleLeg13_apply
    (A : Matrix (κ × κ) (κ × κ) ℂ) (i a b j c d : κ) :
    threeParticleLeg13 κ A (i, (a, b)) (j, (c, d)) =
      A (i, b) (j, d) * (1 : Matrix κ κ ℂ) a c := by
  change (((tripleFlip12Permutation κ).permMatrix ℂ * threeParticleLeg23 κ A) *
      (tripleFlip12Permutation κ).permMatrix ℂ) (i, (a, b)) (j, (c, d)) = _
  rw [PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  rw [PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply]
  simp [tripleFlip12Permutation, Matrix.one_apply, mul_comm]

@[simp]
theorem threeParticleLeg13_apply_general
    (A : Matrix (κ × κ) (κ × κ) ℂ) (i j : ThreeParticleIndex κ) :
    threeParticleLeg13 κ A i j =
      A (i.1, i.2.2) (j.1, j.2.2) * (1 : Matrix κ κ ℂ) i.2.1 j.2.1 := by
  rcases i with ⟨i, a, b⟩
  rcases j with ⟨j, c, d⟩
  exact threeParticleLeg13_apply A i a b j c d

/-- Matrix block obtained by fixing the second output and input tensor coordinates. -/
noncomputable def leftOperatorBlock (L : Matrix (κ × κ) (κ × κ) ℂ) (a c : κ) :
    Matrix κ κ ℂ := fun i j => L (i, a) (j, c)

/-- Matrix block obtained by fixing the first output and input tensor coordinates. -/
noncomputable def rightOperatorBlock (L : Matrix (κ × κ) (κ × κ) ℂ) (a c : κ) :
    Matrix κ κ ℂ := fun i j => L (a, i) (c, j)

/-- Coefficient extraction from a mixed `12`/`13` commutation law. -/
theorem leftOperatorBlock_commute_of_mixed_leg12_leg13
    (A B : Matrix (κ × κ) (κ × κ) ℂ)
    (h : threeParticleLeg12 κ A * threeParticleLeg13 κ B =
      threeParticleLeg13 κ B * threeParticleLeg12 κ A) (a c b d : κ) :
    Commute (leftOperatorBlock A a c) (leftOperatorBlock B b d) := by
  rw [commute_iff_eq]
  ext i j
  have hij := congrFun (congrFun h (i, (a, b))) (j, (c, d))
  simp only [Matrix.mul_apply] at hij
  rw [Fintype.sum_prod_type] at hij
  simp_rw [Fintype.sum_prod_type] at hij
  simpa [Matrix.mul_apply, leftOperatorBlock, Matrix.one_apply] using hij

/-- Coefficient extraction from a mixed `13`/`23` commutation law. -/
theorem rightOperatorBlock_commute_of_mixed_leg13_leg23
    (A B : Matrix (κ × κ) (κ × κ) ℂ)
    (h : threeParticleLeg13 κ A * threeParticleLeg23 κ B =
      threeParticleLeg23 κ B * threeParticleLeg13 κ A) (a c b d : κ) :
    Commute (rightOperatorBlock A a c) (rightOperatorBlock B b d) := by
  rw [commute_iff_eq]
  ext i j
  have hij := congrFun (congrFun h (a, (b, i))) (c, (d, j))
  simp only [Matrix.mul_apply] at hij
  rw [Fintype.sum_prod_type] at hij
  simp_rw [Fintype.sum_prod_type] at hij
  simpa [Matrix.mul_apply, rightOperatorBlock, Matrix.one_apply] using hij

theorem leftOperatorBlock_commute_of_leg12_leg13
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (h : threeParticleLeg12 κ L * threeParticleLeg13 κ L =
      threeParticleLeg13 κ L * threeParticleLeg12 κ L) (a c b d : κ) :
    Commute (leftOperatorBlock L a c) (leftOperatorBlock L b d) :=
  leftOperatorBlock_commute_of_mixed_leg12_leg13 L L h a c b d

theorem rightOperatorBlock_commute_of_leg13_leg23
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (h : threeParticleLeg13 κ L * threeParticleLeg23 κ L =
      threeParticleLeg23 κ L * threeParticleLeg13 κ L) (a c b d : κ) :
    Commute (rightOperatorBlock L a c) (rightOperatorBlock L b d) :=
  rightOperatorBlock_commute_of_mixed_leg13_leg23 L L h a c b d

omit [Fintype κ] [DecidableEq κ] in
@[simp]
theorem star_leftOperatorBlock (L : Matrix (κ × κ) (κ × κ) ℂ) (a c : κ) :
    star (leftOperatorBlock L a c) = leftOperatorBlock (star L) c a := by
  ext i j
  rfl

omit [Fintype κ] [DecidableEq κ] in
@[simp]
theorem star_rightOperatorBlock (L : Matrix (κ × κ) (κ × κ) ℂ) (a c : κ) :
    star (rightOperatorBlock L a c) = rightOperatorBlock (star L) c a := by
  ext i j
  rfl

/-! ## Unitarity of concrete leg embeddings -/

theorem permMatrix_mem_unitary (σ : Equiv.Perm κ) :
    σ.permMatrix ℂ ∈ unitary (Matrix κ κ ℂ) := by
  constructor
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rw [← Matrix.permMatrix_mul]
    simp
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rw [← Matrix.permMatrix_mul]
    simp

@[simp]
theorem star_threeParticleLeg23 (L : Matrix (κ × κ) (κ × κ) ℂ) :
    star (threeParticleLeg23 κ L) = threeParticleLeg23 κ (star L) := by
  change (Matrix.kronecker (1 : Matrix κ κ ℂ) L)ᴴ =
    Matrix.kronecker (1 : Matrix κ κ ℂ) Lᴴ
  simpa only [Matrix.kronecker, Matrix.conjTranspose_one] using
    (Matrix.conjTranspose_kronecker (1 : Matrix κ κ ℂ) L)

theorem threeParticleLeg23_mem_unitary
    {L : Matrix (κ × κ) (κ × κ) ℂ}
    (hL : L ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ)) :
    threeParticleLeg23 κ L ∈
      unitary (Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ) := by
  constructor
  · rw [star_threeParticleLeg23, ← map_mul, hL.1, map_one]
  · rw [star_threeParticleLeg23, ← map_mul, hL.2, map_one]

theorem threeParticleLeg13_mem_unitary
    {L : Matrix (κ × κ) (κ × κ) ℂ}
    (hL : L ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ)) :
    threeParticleLeg13 κ L ∈
      unitary (Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ) := by
  have hF : threeParticleFlip12Matrix κ ∈
      unitary (Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ) :=
    permMatrix_mem_unitary (tripleFlip12Permutation κ)
  exact (unitary (Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ)).mul_mem
    ((unitary (Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ)).mul_mem hF
      (threeParticleLeg23_mem_unitary hL)) hF

omit [Fintype κ] in
@[simp]
theorem star_threeParticleFlip12Matrix :
    star (threeParticleFlip12Matrix κ) = threeParticleFlip12Matrix κ := by
  change ((tripleFlip12Permutation κ).permMatrix ℂ)ᴴ =
    (tripleFlip12Permutation κ).permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  congr 1

@[simp]
theorem star_threeParticleLeg13 (L : Matrix (κ × κ) (κ × κ) ℂ) :
    star (threeParticleLeg13 κ L) = threeParticleLeg13 κ (star L) := by
  simp [threeParticleLeg13, star_threeParticleLeg23, mul_assoc]

/-- If `x` commutes with a unitary `y`, it also commutes with `y⋆ = y⁻¹`. -/
theorem commute_star_right_of_mem_unitary
    {R : Type*} [Monoid R] [StarMul R] {x y : R}
    (h : Commute x y) (hy : y ∈ unitary R) : Commute x (star y) := by
  let u : unitary R := ⟨y, hy⟩
  let v : Rˣ := Unitary.toUnits u
  have hv : Commute x (v : R) := by simpa [v, u] using h
  have hinv := hv.units_inv_right
  change Commute x (star y) at hinv
  exact hinv

theorem leftOperatorBlocks_commute_star_of_unitary_leg_commute
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (hL : L ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ))
    (h : threeParticleLeg12 κ L * threeParticleLeg13 κ L =
      threeParticleLeg13 κ L * threeParticleLeg12 κ L) (a c b d : κ) :
    Commute (leftOperatorBlock L a c) (star (leftOperatorBlock L b d)) := by
  have hleg : Commute (threeParticleLeg12 κ L) (threeParticleLeg13 κ L) := h
  have hmixed := commute_star_right_of_mem_unitary hleg (threeParticleLeg13_mem_unitary hL)
  rw [star_threeParticleLeg13] at hmixed
  rw [star_leftOperatorBlock]
  exact leftOperatorBlock_commute_of_mixed_leg12_leg13 L (star L) hmixed.eq a c d b

theorem rightOperatorBlocks_commute_star_of_unitary_leg_commute
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (hL : L ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ))
    (h : threeParticleLeg13 κ L * threeParticleLeg23 κ L =
      threeParticleLeg23 κ L * threeParticleLeg13 κ L) (a c b d : κ) :
    Commute (rightOperatorBlock L a c) (star (rightOperatorBlock L b d)) := by
  have hleg : Commute (threeParticleLeg13 κ L) (threeParticleLeg23 κ L) := h
  have hmixed := commute_star_right_of_mem_unitary hleg (threeParticleLeg23_mem_unitary hL)
  rw [star_threeParticleLeg23] at hmixed
  rw [star_rightOperatorBlock]
  exact rightOperatorBlock_commute_of_mixed_leg13_leg23 L (star L) hmixed.eq a c d b

/-! ## Exact local product matrix coefficients -/

/-- The exact coefficient
`⟨u_i ⊗ v_j, L (u_k ⊗ v_l)⟩`, written in a left-block contraction order. -/
noncomputable def localProductMatrixCoefficient
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ))
    (i j k l : Fin (Fintype.card κ)) : ℂ :=
  ∑ b, ∑ d, star (v j b) * v l d *
    ∑ a, star (u i a) * (leftOperatorBlock L b d *ᵥ (u k)) a

/-- Pure tensor of two vectors from local orthonormal bases, in the concrete product-coordinate
Euclidean space. -/
noncomputable def localProductVector
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ))
    (i j : Fin (Fintype.card κ)) : EuclideanSpace ℂ (κ × κ) :=
  WithLp.toLp 2 (fun p => u i p.1 * v j p.2)

/-- The factored block formula `localProductMatrixCoefficient` is literally the Hilbert-space
matrix coefficient `⟨u_i ⊗ v_j, L(u_k ⊗ v_l)⟩`. -/
theorem localProductMatrixCoefficient_eq_inner
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ))
    (i j k l : Fin (Fintype.card κ)) :
    localProductMatrixCoefficient L u v i j k l =
      inner ℂ (localProductVector u v i j)
        (Matrix.toEuclideanLin L (localProductVector u v k l)) := by
  classical
  rw [show Matrix.toEuclideanLin L (localProductVector u v k l) =
    WithLp.toLp 2 (L *ᵥ (fun p => u k p.1 * v l p.2)) from rfl]
  simp only [localProductMatrixCoefficient, localProductVector, PiLp.inner_apply,
    Matrix.mulVec, dotProduct, leftOperatorBlock, RCLike.inner_apply]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [map_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun _ _ =>
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp only [starRingEnd_apply]
  ring

omit [DecidableEq κ] in
/-- Pure tensors of two local orthonormal bases are an orthonormal family. -/
theorem localProductVectors_orthonormal
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ)) :
    Orthonormal ℂ (fun p : Fin (Fintype.card κ) × Fin (Fintype.card κ) =>
      localProductVector u v p.1 p.2) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, j⟩ ⟨k, l⟩
  simp only [localProductVector, PiLp.inner_apply]
  simp_rw [Fintype.sum_prod_type, RCLike.inner_apply, map_mul]
  calc
    _ = (∑ x, u k x * star (u i x)) * (∑ x, v l x * star (v j x)) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [starRingEnd_apply]
      ring
    _ = inner ℂ (u i) (u k) * inner ℂ (v j) (v l) := rfl
    _ = _ := by
      rw [u.inner_eq_ite, v.inner_eq_ite]
      by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]

omit [DecidableEq κ] in
/-- The local pure tensors form a full orthonormal basis, not merely an orthonormal subset. -/
theorem exists_localProductOrthonormalBasis
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ)) :
    ∃ w : OrthonormalBasis
        (Fin (Fintype.card κ) × Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ (κ × κ)),
      ∀ i j, w (i, j) = localProductVector u v i j := by
  classical
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (κ × κ)) =
      Fintype.card (Fin (Fintype.card κ) × Fin (Fintype.card κ)) := by
    simp [Fintype.card_prod]
  have hon := localProductVectors_orthonormal u v
  have hon' : Orthonormal ℂ
      ((Set.univ : Set (Fin (Fintype.card κ) × Fin (Fintype.card κ))).restrict
        (fun p => localProductVector u v p.1 p.2)) := by
    exact hon.comp _ Subtype.val_injective
  obtain ⟨w, hw⟩ := hon'.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨w, fun i j => hw (i, j) (Set.mem_univ _)⟩

/-- A two-particle matrix is diagonal in a local orthonormal product basis when every
off-diagonal coefficient in that basis vanishes. -/
def IsLocallyProductDiagonalizable
    (L : Matrix (κ × κ) (κ × κ) ℂ) : Prop :=
  ∃ u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ),
    ∀ i j k l, (i, j) ≠ (k, l) → localProductMatrixCoefficient L u v i j k l = 0

omit [DecidableEq κ] in
theorem localProductMatrixCoefficient_eq_right
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ))
    (i j k l : Fin (Fintype.card κ)) :
    localProductMatrixCoefficient L u v i j k l =
      ∑ a, ∑ c, star (u i a) * u k c *
        ∑ b, star (v j b) * (rightOperatorBlock L a c *ᵥ (v l)) b := by
  classical
  simp only [localProductMatrixCoefficient, leftOperatorBlock, rightOperatorBlock,
    Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun _ _ =>
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem mulVec_eigen_of_toEuclideanLin
    (A : Matrix κ κ ℂ) (w : EuclideanSpace ℂ κ) (μ : ℂ)
    (h : Matrix.toEuclideanLin A w = μ • w) : A *ᵥ w = μ • (w : κ → ℂ) := by
  apply funext
  intro i
  have hi := congrArg (fun z : EuclideanSpace ℂ κ => z i) h
  simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using hi

theorem localProductMatrixCoefficient_eq_zero_of_left_eigen
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ))
    (hu : ∀ (p : κ × κ) i, ∃ μ : ℂ,
      Matrix.toEuclideanLin (leftOperatorBlock L p.1 p.2) (u i) = μ • u i)
    {i k j l : Fin (Fintype.card κ)} (hik : i ≠ k) :
    localProductMatrixCoefficient L u v i j k l = 0 := by
  classical
  have hortho : ∑ a, star (u i a) * u k a = 0 := by
    simpa [PiLp.inner_apply, mul_comm] using u.inner_eq_zero hik
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro d _
  obtain ⟨μ, hμ⟩ := hu (b, d) k
  have hmul := mulVec_eigen_of_toEuclideanLin (leftOperatorBlock L b d) (u k) μ hμ
  rw [hmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinner : ∑ x, star (u i x) * (μ * u k x) = 0 := by
    calc
      _ = μ * ∑ x, star (u i x) * u k x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hortho, mul_zero]
  rw [hinner, mul_zero]

theorem localProductMatrixCoefficient_eq_zero_of_right_eigen
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ))
    (hv : ∀ (p : κ × κ) i, ∃ μ : ℂ,
      Matrix.toEuclideanLin (rightOperatorBlock L p.1 p.2) (v i) = μ • v i)
    {i k j l : Fin (Fintype.card κ)} (hjl : j ≠ l) :
    localProductMatrixCoefficient L u v i j k l = 0 := by
  classical
  rw [localProductMatrixCoefficient_eq_right]
  have hortho : ∑ b, star (v j b) * v l b = 0 := by
    simpa [PiLp.inner_apply, mul_comm] using v.inner_eq_zero hjl
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro c _
  obtain ⟨μ, hμ⟩ := hv (a, c) l
  have hmul := mulVec_eigen_of_toEuclideanLin (rightOperatorBlock L a c) (v l) μ hμ
  rw [hmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinner : ∑ x, star (v j x) * (μ * v l x) = 0 := by
    calc
      _ = μ * ∑ x, star (v j x) * v l x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hortho, mul_zero]
  rw [hinner, mul_zero]

set_option maxHeartbeats 1600000 in
/-- **Unitary leg-commutation rigidity.**  A unitary two-particle matrix whose `12` and `23` legs
both commute with its `13` leg is diagonal in a local orthonormal product basis. -/
theorem unitary_leg_commute_locallyProductDiagonalizable
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (hL : L ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ))
    (h12_13 : threeParticleLeg12 κ L * threeParticleLeg13 κ L =
      threeParticleLeg13 κ L * threeParticleLeg12 κ L)
    (h13_23 : threeParticleLeg13 κ L * threeParticleLeg23 κ L =
      threeParticleLeg23 κ L * threeParticleLeg13 κ L) :
    IsLocallyProductDiagonalizable L := by
  classical
  obtain ⟨u, hu⟩ := exists_orthonormalBasis_eigen_of_pairwise_commute_star
    (fun p : κ × κ => leftOperatorBlock L p.1 p.2)
    (fun p q => leftOperatorBlock_commute_of_leg12_leg13 L h12_13 p.1 p.2 q.1 q.2)
    (fun p q => leftOperatorBlocks_commute_star_of_unitary_leg_commute
      L hL h12_13 p.1 p.2 q.1 q.2)
  obtain ⟨v, hv⟩ := exists_orthonormalBasis_eigen_of_pairwise_commute_star
    (fun p : κ × κ => rightOperatorBlock L p.1 p.2)
    (fun p q => rightOperatorBlock_commute_of_leg13_leg23 L h13_23 p.1 p.2 q.1 q.2)
    (fun p q => rightOperatorBlocks_commute_star_of_unitary_leg_commute
      L hL h13_23 p.1 p.2 q.1 q.2)
  refine ⟨u, v, fun i j k l hne => ?_⟩
  by_cases hik : i = k
  · have hjl : j ≠ l := by
      intro hjl
      exact hne (Prod.ext hik hjl)
    exact localProductMatrixCoefficient_eq_zero_of_right_eigen L u v hv hjl
  · exact localProductMatrixCoefficient_eq_zero_of_left_eigen L u v hu hik

/-! ## Flip conjugation swaps the local bases -/

@[simp]
theorem twoParticleFlip_conjugate_apply
    (L : Matrix (κ × κ) (κ × κ) ℂ) (i j k l : κ) :
    (twoParticleFlipMatrix κ * L * twoParticleFlipMatrix κ) (i, j) (k, l) =
      L (j, i) (l, k) := by
  let σ : Equiv.Perm (κ × κ) := Equiv.prodComm κ κ
  change (((σ.permMatrix ℂ * L) * σ.permMatrix ℂ) (i, j) (k, l)) = _
  rw [PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  rw [PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply]
  rfl

theorem leftOperatorBlock_flipConjugate
    (L : Matrix (κ × κ) (κ × κ) ℂ) (a c : κ) :
    leftOperatorBlock (twoParticleFlipMatrix κ * L * twoParticleFlipMatrix κ) a c =
      rightOperatorBlock L a c := by
  ext i j
  exact twoParticleFlip_conjugate_apply L i a j c

theorem rightOperatorBlock_flipConjugate
    (L : Matrix (κ × κ) (κ × κ) ℂ) (a c : κ) :
    rightOperatorBlock (twoParticleFlipMatrix κ * L * twoParticleFlipMatrix κ) a c =
      leftOperatorBlock L a c := by
  ext i j
  exact twoParticleFlip_conjugate_apply L a i c j

theorem localProductMatrixCoefficient_flipConjugate
    (L : Matrix (κ × κ) (κ × κ) ℂ)
    (u v : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ))
    (i j k l : Fin (Fintype.card κ)) :
    localProductMatrixCoefficient
        (twoParticleFlipMatrix κ * L * twoParticleFlipMatrix κ) v u i j k l =
      localProductMatrixCoefficient L u v j i l k := by
  rw [localProductMatrixCoefficient_eq_right]
  simp only [localProductMatrixCoefficient, rightOperatorBlock_flipConjugate]

theorem IsLocallyProductDiagonalizable.flipConjugate
    {L : Matrix (κ × κ) (κ × κ) ℂ}
    (hL : IsLocallyProductDiagonalizable L) :
    IsLocallyProductDiagonalizable
      (twoParticleFlipMatrix κ * L * twoParticleFlipMatrix κ) := by
  obtain ⟨u, v, hdiag⟩ := hL
  refine ⟨v, u, fun i j k l hne => ?_⟩
  rw [localProductMatrixCoefficient_flipConjugate]
  apply hdiag
  intro heq
  exact hne (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))

/-! ## Adjacent braid equation and flip anchor -/

theorem threeParticleLeg12_smul_one (c : ℂ) :
    threeParticleLeg12 κ (c • (1 : Matrix (κ × κ) (κ × κ) ℂ)) =
      c • (1 : Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ) := by
  ext ⟨i, j, k⟩ ⟨a, b, d⟩
  simp [threeParticleLeg12, Matrix.one_apply]
  split_ifs <;> simp_all

theorem threeParticleLeg23_smul_one (c : ℂ) :
    threeParticleLeg23 κ (c • (1 : Matrix (κ × κ) (κ × κ) ℂ)) =
      c • (1 : Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ) := by
  ext ⟨i, j, k⟩ ⟨a, b, d⟩
  simp [threeParticleLeg23, Matrix.one_apply]
  split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
/-- **Flip-anchor local product diagonalization.**  Let `B` satisfy the additive adjacent braid
equation, `B(0) = c P` with `c ≠ 0`, and pointwise positive-metric unitarity.  Then every left flip
`P B(x)` is diagonal in a (possibly `x`-dependent) local orthonormal product basis. -/
theorem fermionicZeroBraid_leftFlip_locallyProductDiagonalizable
    {Θ : Type*} [AddCommMonoid Θ]
    (B : Θ → Matrix (κ × κ) (κ × κ) ℂ) (c : ℂ) (hc : c ≠ 0)
    (hbraid : ∀ x y,
      threeParticleLeg12 κ (B x) * threeParticleLeg23 κ (B (x + y)) *
          threeParticleLeg12 κ (B y) =
        threeParticleLeg23 κ (B y) * threeParticleLeg12 κ (B (x + y)) *
          threeParticleLeg23 κ (B x))
    (hanchor : B 0 = c • twoParticleFlipMatrix κ)
    (hunitary : ∀ x, B x ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ)) :
    ∀ x, IsLocallyProductDiagonalizable (twoParticleFlipMatrix κ * B x) := by
  let F := twoParticleFlipMatrix κ
  let R : Θ → Matrix (κ × κ) (κ × κ) ℂ := fun x => rightFlip (B x) F
  have hq : ∀ x y,
      threeParticleLeg12 κ (R x) * threeParticleLeg13 κ (R (x + y)) *
          threeParticleLeg23 κ (R y) =
        threeParticleLeg23 κ (R y) * threeParticleLeg13 κ (R (x + y)) *
          threeParticleLeg12 κ (R x) := by
    simpa [R, F] using
      (matrix_rightFlip_adjacentBraid_iff_quantumYangBaxter (κ := κ) B).mp hbraid
  have hYBE : ∀ x y,
      threeParticleLeg12 κ (R y) * threeParticleLeg13 κ (R (x + y)) *
          threeParticleLeg23 κ (R x) =
        threeParticleLeg23 κ (R x) * threeParticleLeg13 κ (R (x + y)) *
          threeParticleLeg12 κ (R y) := by
    intro x y
    simpa [add_comm] using hq y x
  have hR0 : R 0 = c • (1 : Matrix (κ × κ) (κ × κ) ℂ) := by
    simp [R, F, rightFlip, hanchor]
  have hanchor12 : threeParticleLeg12 κ (R 0) =
      c • (1 : Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ) := by
    rw [hR0, threeParticleLeg12_smul_one]
  have hanchor23 : threeParticleLeg23 κ (R 0) =
      c • (1 : Matrix (ThreeParticleIndex κ) (ThreeParticleIndex κ) ℂ) := by
    rw [hR0, threeParticleLeg23_smul_one]
  have hcomm := braidZeroAnchor_commute
    (fun x => threeParticleLeg12 κ (R x)) (fun x => threeParticleLeg13 κ (R x))
    (fun x => threeParticleLeg23 κ (R x)) c hc hYBE hanchor12 hanchor23
  intro x
  have hRu : R x ∈ unitary (Matrix (κ × κ) (κ × κ) ℂ) :=
    (matrix_rightFlip_mem_unitary_iff (κ := κ) (B x)).mpr (hunitary x)
  have hRdiag := unitary_leg_commute_locallyProductDiagonalizable
    (R x) hRu (hcomm.2 x) (hcomm.1 x)
  have hconj := hRdiag.flipConjugate
  convert hconj using 1
  simp [R, F, rightFlip, mul_assoc]

end GaloisForLFunctions.HTGeometry
