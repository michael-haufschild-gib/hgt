import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Abel

/-!
# Exact rank of a block triangular map

Projection of the image of `(v,w) ↦ (Av,Bv+Dw)` onto the first component
has image `range A`. Its kernel is the vertical space `range D + B(ker A)`.
Rank-nullity therefore gives the exact rank, the diagonal-rank lower bound,
and the criterion for equality: `B(ker A) ≤ range D`.

This sharpens the block-rank estimate used in Proposition 3.2 of Abuaf,
*Derived invariance of the space of holomorphic two-forms*. An identity
diagonal block absorbs the entire off-diagonal image; the remaining kernel
is explicitly the graph `v ↦ (v,-Bv)` over `ker A`.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Matrix

variable {K V W X Y : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The block triangular map `(v,w) ↦ (Av,Bv+Dw)`. -/
def lowerBlock (A : V →ₗ[K] X) (B : V →ₗ[K] Y) (D : W →ₗ[K] Y) :
    V × W →ₗ[K] X × Y :=
  (A.comp (LinearMap.fst K V W)).prod (B.coprod D)

@[simp] theorem lowerBlock_apply (A : V →ₗ[K] X) (B : V →ₗ[K] Y)
    (D : W →ₗ[K] Y) (v : V × W) :
    lowerBlock A B D v = (A v.1, B v.1 + D v.2) := rfl

/-- Vertical image: the diagonal image plus the coupling of the first kernel. -/
def lowerBlockVertical (A : V →ₗ[K] X) (B : V →ₗ[K] Y) (D : W →ₗ[K] Y) :
    Submodule K Y := LinearMap.range D ⊔ (LinearMap.ker A).map B

private def imageFst (A : V →ₗ[K] X) (B : V →ₗ[K] Y) (D : W →ₗ[K] Y) :
    LinearMap.range (lowerBlock A B D) →ₗ[K] LinearMap.range A :=
  LinearMap.codRestrict (LinearMap.range A)
    ((LinearMap.fst K X Y).comp (LinearMap.range (lowerBlock A B D)).subtype) (by
      rintro ⟨x, v, rfl⟩
      exact ⟨v.1, rfl⟩)

private theorem imageFst_surjective (A : V →ₗ[K] X) (B : V →ₗ[K] Y)
    (D : W →ₗ[K] Y) : Function.Surjective (imageFst A B D) := by
  rintro ⟨x, v, rfl⟩
  exact ⟨⟨lowerBlock A B D (v, 0), ⟨(v, 0), rfl⟩⟩, rfl⟩

/-- The vertical image is exactly the image lying over zero in the first component. -/
theorem mem_lowerBlockVertical_iff (A : V →ₗ[K] X) (B : V →ₗ[K] Y)
    (D : W →ₗ[K] Y) (y : Y) :
    y ∈ lowerBlockVertical A B D ↔ (0, y) ∈ LinearMap.range (lowerBlock A B D) := by
  constructor
  · intro h
    obtain ⟨d, ⟨w, rfl⟩, b, ⟨v, hv, rfl⟩, he⟩ := Submodule.mem_sup.mp h
    refine ⟨(v, w), ?_⟩
    have ha : A v = 0 := hv
    change (A v, B v + D w) = (0, y)
    exact Prod.ext ha (by simpa only [add_comm] using he)
  · rintro ⟨⟨v, w⟩, he⟩
    have ha : A v = 0 := congrArg Prod.fst he
    have hy : B v + D w = y := congrArg Prod.snd he
    exact Submodule.mem_sup.mpr ⟨D w, ⟨w, rfl⟩, B v, ⟨v, ha, rfl⟩,
      (add_comm _ _).trans hy⟩

private def kernelVerticalMap (A : V →ₗ[K] X) (B : V →ₗ[K] Y)
    (D : W →ₗ[K] Y) :
    LinearMap.ker (imageFst A B D) →ₗ[K] lowerBlockVertical A B D where
  toFun z := ⟨z.1.1.2, by
    apply (mem_lowerBlockVertical_iff A B D _).mpr
    have hz : z.1.1.1 = 0 := congrArg Subtype.val z.2
    simpa only [← hz, Prod.mk.eta] using z.1.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def kernelVerticalEquiv (A : V →ₗ[K] X) (B : V →ₗ[K] Y)
    (D : W →ₗ[K] Y) :
    LinearMap.ker (imageFst A B D) ≃ₗ[K] lowerBlockVertical A B D :=
  LinearEquiv.ofBijective (kernelVerticalMap A B D) ⟨by
    intro z w h
    have hz : z.1.1.1 = 0 := congrArg Subtype.val z.2
    have hw : w.1.1.1 = 0 := congrArg Subtype.val w.2
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (hz.trans hw.symm) (congrArg Subtype.val h), by
    intro y
    refine ⟨⟨⟨(0, y.1), (mem_lowerBlockVertical_iff A B D _).mp y.2⟩, ?_⟩, rfl⟩
    apply Subtype.ext
    rfl⟩

/-- With an identity second block, the kernel is the graph of `-B` over `ker A`. -/
def lowerBlockIdKernelEquiv (A : V →ₗ[K] X) (B : V →ₗ[K] Y) :
    LinearMap.ker (lowerBlock A B LinearMap.id) ≃ₗ[K] LinearMap.ker A where
  toFun z := ⟨z.1.1, congrArg Prod.fst z.2⟩
  invFun v := ⟨(v.1, -B v.1), by
    change (A v.1, B v.1 + -B v.1) = (0, 0)
    exact Prod.ext v.2 (add_neg_cancel _)⟩
  left_inv z := by
    apply Subtype.ext
    change (z.1.1, -B z.1.1) = z.1
    refine Prod.ext rfl ?_
    have hz : B z.1.1 + z.1.2 = 0 := congrArg Prod.snd z.2
    calc
      -B z.1.1 = -B z.1.1 + (B z.1.1 + z.1.2) := by rw [hz, add_zero]
      _ = z.1.2 := by abel
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- Exact rank from the first projected image and its vertical kernel. -/
theorem finrank_lowerBlock (A : V →ₗ[K] X) (B : V →ₗ[K] Y) (D : W →ₗ[K] Y) :
    Module.finrank K (LinearMap.range (lowerBlock A B D)) =
      Module.finrank K (LinearMap.range A) + Module.finrank K (lowerBlockVertical A B D) := by
  have h := LinearMap.finrank_range_add_finrank_ker (imageFst A B D)
  rw [LinearMap.range_eq_top.mpr (imageFst_surjective A B D),
    (kernelVerticalEquiv A B D).finrank_eq] at h
  simpa using h.symm

variable [FiniteDimensional K Y]

/-- A block triangular map has at least the sum of its diagonal ranks. -/
theorem diagonal_finrank_le_lowerBlock (A : V →ₗ[K] X) (B : V →ₗ[K] Y)
    (D : W →ₗ[K] Y) :
    Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range D) ≤
      Module.finrank K (LinearMap.range (lowerBlock A B D)) := by
  rw [finrank_lowerBlock]
  exact Nat.add_le_add_left (Submodule.finrank_mono (show LinearMap.range D ≤
    lowerBlockVertical A B D from le_sup_left)) _

/-- Equality holds exactly when the second diagonal image absorbs `B(ker A)`. -/
theorem finrank_lowerBlock_eq_diagonal_iff (A : V →ₗ[K] X) (B : V →ₗ[K] Y)
    (D : W →ₗ[K] Y) :
    Module.finrank K (LinearMap.range (lowerBlock A B D)) =
      Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range D) ↔
      (LinearMap.ker A).map B ≤ LinearMap.range D := by
  rw [finrank_lowerBlock, Nat.add_left_cancel_iff]
  constructor
  · intro h
    have he : LinearMap.range D = lowerBlockVertical A B D :=
      Submodule.eq_of_le_of_finrank_eq le_sup_left h.symm
    exact sup_eq_left.mp he.symm
  · intro h
    rw [lowerBlockVertical, sup_eq_left.mpr h]

/-- An identity diagonal block adds its full dimension, independently of the coupling. -/
theorem finrank_lowerBlock_id (A : V →ₗ[K] X) (B : V →ₗ[K] Y) :
    Module.finrank K (LinearMap.range (lowerBlock A B LinearMap.id)) =
      Module.finrank K (LinearMap.range A) + Module.finrank K Y := by
  rw [finrank_lowerBlock, lowerBlockVertical, LinearMap.range_id, top_sup_eq,
    finrank_top]

section Matrix
variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

omit [Fintype m] [Fintype p] in
private theorem lowerBlock_mulVecLin (A : Matrix m n K) (B : Matrix p n K)
    (D : Matrix p q K) :
    lowerBlock A.mulVecLin B.mulVecLin D.mulVecLin =
      ((LinearEquiv.sumArrowLequivProdArrow m p K K).toLinearMap.comp
        (Matrix.fromBlocks A 0 B D).mulVecLin).comp
          (LinearEquiv.sumArrowLequivProdArrow n q K K).symm.toLinearMap := by
  apply LinearMap.ext
  intro v
  change (A *ᵥ v.1, B *ᵥ v.1 + D *ᵥ v.2) = _
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero]
  rfl

omit [Fintype m] [Fintype p] in
/-- Exact rank for rectangular block matrices, with arbitrary row index types. -/
theorem rank_fromBlocks_zero_upper (A : Matrix m n K) (B : Matrix p n K)
    (D : Matrix p q K) :
    (Matrix.fromBlocks A 0 B D).rank = A.rank +
      Module.finrank K (lowerBlockVertical A.mulVecLin B.mulVecLin D.mulVecLin) := by
  have h := finrank_lowerBlock A.mulVecLin B.mulVecLin D.mulVecLin
  rw [lowerBlock_mulVecLin,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
      (LinearEquiv.sumArrowLequivProdArrow n q K K).symm.surjective),
    LinearMap.range_comp, LinearEquiv.finrank_map_eq] at h
  exact h

omit [Fintype m] in
/-- The diagonal-rank estimate in matrix form. -/
theorem diagonal_rank_le_fromBlocks_zero_upper (A : Matrix m n K) (B : Matrix p n K)
    (D : Matrix p q K) : A.rank + D.rank ≤ (Matrix.fromBlocks A 0 B D).rank := by
  rw [rank_fromBlocks_zero_upper]
  exact Nat.add_le_add_left (Submodule.finrank_mono (show LinearMap.range D.mulVecLin ≤
    lowerBlockVertical A.mulVecLin B.mulVecLin D.mulVecLin from le_sup_left)) _

omit [Fintype m] in
/-- The matrix diagonal-rank estimate is sharp exactly when the coupling adds no new image. -/
theorem rank_fromBlocks_zero_upper_eq_diagonal_iff (A : Matrix m n K) (B : Matrix p n K)
    (D : Matrix p q K) :
    (Matrix.fromBlocks A 0 B D).rank = A.rank + D.rank ↔
      (LinearMap.ker A.mulVecLin).map B.mulVecLin ≤ LinearMap.range D.mulVecLin := by
  rw [rank_fromBlocks_zero_upper]
  simpa only [finrank_lowerBlock, Matrix.rank] using
    finrank_lowerBlock_eq_diagonal_iff A.mulVecLin B.mulVecLin D.mulVecLin

omit [Fintype m] in
/-- An identity matrix block contributes exactly its size to the rank. -/
theorem rank_fromBlocks_zero_upper_one [DecidableEq p]
    (A : Matrix m n K) (B : Matrix p n K) :
    (Matrix.fromBlocks A 0 B (1 : Matrix p p K)).rank = A.rank + Fintype.card p := by
  rw [rank_fromBlocks_zero_upper, lowerBlockVertical, Matrix.mulVecLin_one,
    LinearMap.range_id, top_sup_eq, finrank_top, Module.finrank_pi]

end Matrix
end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.finrank_lowerBlock
#print axioms GaloisForLFunctions.HTGeometry.lowerBlockIdKernelEquiv
#print axioms GaloisForLFunctions.HTGeometry.rank_fromBlocks_zero_upper
#print axioms GaloisForLFunctions.HTGeometry.rank_fromBlocks_zero_upper_eq_diagonal_iff
