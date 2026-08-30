import GaloisForLFunctions.HTGeometry.RealSchurPosDef

/-!
# Schur restriction of positive balanced order forms

Splitting off the first complete order block and eliminating its cross term produces a Schur
complement on one fewer order coordinate.  The head is automatically invertible, the Schur
complement is positive definite, and the block self-adjointness equations show it remains balanced.
Thus rank descent retains no auxiliary positivity, invertibility, symmetry, or balance hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n d : ℕ} {R : Type*} [CommRing R]

def orderHeadIndex (k : Fin d) : Fin ((n + 1) * d) :=
  finProdFinEquiv (0, k)

def orderTailIndex (p : Fin (n * d)) : Fin ((n + 1) * d) :=
  orderPrincipalIndex Fin.succ p

def orderHeadTailIndex : Fin d ⊕ Fin (n * d) → Fin ((n + 1) * d)
  | Sum.inl k => orderHeadIndex k
  | Sum.inr p => orderTailIndex p

theorem orderHeadTailIndex_injective :
    Function.Injective (orderHeadTailIndex (n := n) (d := d)) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          congr 1
          exact congrArg Prod.snd (finProdFinEquiv.injective hxy)
      | inr y =>
          exfalso
          have hdiv := congrArg (fun p => Fin.divNat p) hxy
          simp only [orderHeadTailIndex, orderHeadIndex, orderTailIndex, orderPrincipalIndex,
            divNat_finProdFinEquiv] at hdiv
          have hv := congrArg Fin.val hdiv
          change 0 = (Fin.divNat y).val + 1 at hv
          omega
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          have hdiv := congrArg (fun p => Fin.divNat p) hxy
          simp only [orderHeadTailIndex, orderHeadIndex, orderTailIndex, orderPrincipalIndex,
            divNat_finProdFinEquiv] at hdiv
          have hv := congrArg Fin.val hdiv
          change (Fin.divNat x).val + 1 = 0 at hv
          omega
      | inr y =>
          congr 1
          exact orderPrincipalIndex_injective (Fin.succ_injective n) hxy

def orderHead (A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  blockUnembed A 0 0

def orderCross (A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ) :
    Matrix (Fin d) (Fin (n * d)) ℝ :=
  Matrix.of fun k p => A (orderHeadIndex k) (orderTailIndex p)

def orderHeadTailMatrix (A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ) :
    Matrix (Fin d ⊕ Fin (n * d)) (Fin d ⊕ Fin (n * d)) ℝ :=
  A.submatrix orderHeadTailIndex orderHeadTailIndex

theorem orderHeadTailMatrix_eq_fromBlocks
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ}
    (hA : Aᵀ = A) :
    orderHeadTailMatrix A =
      fromBlocks (orderHead A) (orderCross A) (orderCross A)ᵀ
        (orderPrincipal Fin.succ A) := by
  ext x y
  cases x with
  | inl x =>
      cases y with
      | inl y => rfl
      | inr y => rfl
  | inr x =>
      cases y with
      | inl y =>
          have h := congrFun (congrFun hA (orderHeadIndex y)) (orderTailIndex x)
          change A (orderTailIndex x) (orderHeadIndex y) =
            A (orderHeadIndex y) (orderTailIndex x)
          simpa only [Matrix.transpose_apply] using h
      | inr y =>
          rw [orderPrincipal_eq_submatrix]
          rfl

theorem orderHeadTailMatrix_posDef
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ} (hA : A.PosDef) :
    (orderHeadTailMatrix A).PosDef :=
  hA.submatrix orderHeadTailIndex_injective

theorem orderHead_posDef
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ} (hA : A.PosDef) :
    (orderHead A).PosDef := by
  have hfull := orderHeadTailMatrix_posDef hA
  have hsub := hfull.submatrix
    (Sum.inl_injective : Function.Injective (Sum.inl : Fin d → Fin d ⊕ Fin (n * d)))
  have heq : (orderHeadTailMatrix A).submatrix Sum.inl Sum.inl = orderHead A := by
    ext i j
    rfl
  rw [heq] at hsub
  exact hsub

theorem orderHead_symm
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ} (hA : Aᵀ = A) :
    (orderHead A)ᵀ = orderHead A := by
  ext i j
  have h := congrFun (congrFun hA (orderHeadIndex i)) (orderHeadIndex j)
  change A (orderHeadIndex j) (orderHeadIndex i) = A (orderHeadIndex i) (orderHeadIndex j)
  simpa only [Matrix.transpose_apply, orderHeadIndex] using h

noncomputable def orderSchur (A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ) :
    Matrix (Fin (n * d)) (Fin (n * d)) ℝ :=
  orderPrincipal Fin.succ A - (orderCross A)ᵀ * (orderHead A)⁻¹ * orderCross A

theorem orderSchur_posDef
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ} (hA : A.PosDef) :
    (orderSchur A).PosDef := by
  have hsymm : Aᵀ = A := by
    have hh := hA.isHermitian
    change Aᴴ = A at hh
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  have hhead := orderHead_posDef hA
  have hfull := orderHeadTailMatrix_posDef hA
  rw [orderHeadTailMatrix_eq_fromBlocks hsymm] at hfull
  exact schurComplement_posDef_real hhead.isUnit (orderHead_symm hsymm)
    (orderCross A) (orderPrincipal Fin.succ A) hfull

theorem blockUnembed_orderCross_term
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ} (hA : Aᵀ = A)
    (i j : Fin n) :
    blockUnembed ((orderCross A)ᵀ * (orderHead A)⁻¹ * orderCross A) i j =
      blockUnembed A (Fin.succ i) 0 * (orderHead A)⁻¹ *
        blockUnembed A 0 (Fin.succ j) := by
  ext k l
  change (((orderCross A)ᵀ * (orderHead A)⁻¹ * orderCross A)
      (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l))) =
    (blockUnembed A (Fin.succ i) 0 * (orderHead A)⁻¹ *
      blockUnembed A 0 (Fin.succ j)) k l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  apply congrArg₂ (· * ·)
  · rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [Matrix.transpose_apply]
    change A (orderHeadIndex s) (orderTailIndex (finProdFinEquiv (i, k))) =
      A (finProdFinEquiv (Fin.succ i, k)) (finProdFinEquiv (0, s))
    have htail : orderTailIndex (finProdFinEquiv (i, k)) =
        finProdFinEquiv (Fin.succ i, k) := by
      rw [orderTailIndex, orderPrincipalIndex, divNat_finProdFinEquiv, modNat_finProdFinEquiv]
    rw [htail]
    have h := congrFun (congrFun hA (finProdFinEquiv (Fin.succ i, k)))
      (orderHeadIndex s)
    simpa only [Matrix.transpose_apply, orderHeadIndex] using h
  · change A (orderHeadIndex r) (orderTailIndex (finProdFinEquiv (j, l))) =
      A (finProdFinEquiv (0, r)) (finProdFinEquiv (Fin.succ j, l))
    have htail : orderTailIndex (finProdFinEquiv (j, l)) =
        finProdFinEquiv (Fin.succ j, l) := by
      rw [orderTailIndex, orderPrincipalIndex, divNat_finProdFinEquiv, modNat_finProdFinEquiv]
    rw [htail]
    rfl

theorem blockUnembed_orderSchur
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ} (hA : Aᵀ = A)
    (i j : Fin n) :
    blockUnembed (orderSchur A) i j =
      blockUnembed A (Fin.succ i) (Fin.succ j) -
        blockUnembed A (Fin.succ i) 0 * (orderHead A)⁻¹ *
          blockUnembed A 0 (Fin.succ j) := by
  change blockUnembed (orderPrincipal Fin.succ A) i j -
      blockUnembed ((orderCross A)ᵀ * (orderHead A)⁻¹ * orderCross A) i j = _
  rw [blockUnembed_orderPrincipal, blockUnembed_orderCross_term hA]

theorem orderSchur_mem_balanced (ω : Module.Basis (Fin d) ℤ R)
    {A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ}
    (hbal : A ∈ balancedSubspace ω) (hpos : A.PosDef) :
    orderSchur A ∈ balancedSubspace ω := by
  have hsymm : Aᵀ = A := by
    have hh := hpos.isHermitian
    change Aᴴ = A at hh
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  rw [mem_balancedSubspace_iff_blocks] at hbal ⊢
  intro i j α
  rw [blockUnembed_orderSchur hsymm]
  let L := basisEntryRep ω α
  let H := orderHead A
  have hHpos : H.PosDef := orderHead_posDef hpos
  have hHu : IsUnit H := hHpos.isUnit
  have hHdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hHu
  have hinvH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hHdet
  have hHinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hHdet
  have h00 := hbal (0 : Fin (n + 1)) 0 α
  have hi0 := hbal (Fin.succ i) 0 α
  have h0j := hbal 0 (Fin.succ j) α
  have hij := hbal (Fin.succ i) (Fin.succ j) α
  change Lᵀ * H = H * L at h00
  change Lᵀ * blockUnembed A (Fin.succ i) 0 =
    blockUnembed A (Fin.succ i) 0 * L at hi0
  change Lᵀ * blockUnembed A 0 (Fin.succ j) =
    blockUnembed A 0 (Fin.succ j) * L at h0j
  change Lᵀ * blockUnembed A (Fin.succ i) (Fin.succ j) =
    blockUnembed A (Fin.succ i) (Fin.succ j) * L at hij
  have hcommInv : L * H⁻¹ = H⁻¹ * Lᵀ := by
    calc
      L * H⁻¹ = (H⁻¹ * H) * (L * H⁻¹) := by rw [hinvH, Matrix.one_mul]
      _ = H⁻¹ * (H * L) * H⁻¹ := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ * (Lᵀ * H) * H⁻¹ := by rw [h00]
      _ = (H⁻¹ * Lᵀ) * (H * H⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ * Lᵀ := by rw [hHinv, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, hij]
  congr 1
  calc
    Lᵀ * (blockUnembed A (Fin.succ i) 0 * H⁻¹ * blockUnembed A 0 (Fin.succ j))
        = (Lᵀ * blockUnembed A (Fin.succ i) 0) * H⁻¹ *
            blockUnembed A 0 (Fin.succ j) := by simp only [Matrix.mul_assoc]
    _ = (blockUnembed A (Fin.succ i) 0 * L) * H⁻¹ *
            blockUnembed A 0 (Fin.succ j) := by rw [hi0]
    _ = blockUnembed A (Fin.succ i) 0 * (L * H⁻¹) *
            blockUnembed A 0 (Fin.succ j) := by simp only [Matrix.mul_assoc]
    _ = blockUnembed A (Fin.succ i) 0 * (H⁻¹ * Lᵀ) *
            blockUnembed A 0 (Fin.succ j) := by rw [hcommInv]
    _ = blockUnembed A (Fin.succ i) 0 * H⁻¹ *
            (Lᵀ * blockUnembed A 0 (Fin.succ j)) := by simp only [Matrix.mul_assoc]
    _ = blockUnembed A (Fin.succ i) 0 * H⁻¹ *
            (blockUnembed A 0 (Fin.succ j) * L) := by rw [h0j]
    _ = (blockUnembed A (Fin.succ i) 0 * H⁻¹ *
            blockUnembed A 0 (Fin.succ j)) * L := by simp only [Matrix.mul_assoc]

noncomputable def orderConeSchur (ω : Module.Basis (Fin d) ℤ R)
    (A : ↥(orderCone (nb := n + 1) ω)) : ↥(orderCone (nb := n) ω) := by
  let S := orderSchur (A : Matrix (Fin ((n + 1) * d)) (Fin ((n + 1) * d)) ℝ)
  have hpos : S.PosDef := orderSchur_posDef A.2
  have hsymm : S ∈ symmMatrices (n * d) := by
    rw [mem_symmMatrices_iff]
    have hh := hpos.isHermitian
    change Sᴴ = S at hh
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  exact ⟨⟨S, ⟨hsymm, orderSchur_mem_balanced ω A.1.2.2 A.2⟩⟩, hpos⟩

end GaloisForLFunctions.HTGeometry
