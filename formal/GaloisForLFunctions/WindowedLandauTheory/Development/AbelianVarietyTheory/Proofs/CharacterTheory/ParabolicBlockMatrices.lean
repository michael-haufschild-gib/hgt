import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.TwoBlockHarishChandraInduction

/-! Block coordinates for units and for the kernel of the two-block Levi map. -/

noncomputable section
open scoped Classical

open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

local notation "Rect" => Matrix (Fin a) (Fin b) (ZMod g)

@[simp] theorem upperBlockMatrix_one :
    upperBlockMatrix (1 : Mt g a) (0 : Rect) (1 : Mt g b) = 1 := by
  rw [upperBlockMatrix, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/-- An upper block matrix with invertible diagonal blocks is a unit. -/
def upperBlockUnit (A : Gn g a) (X : Rect) (D : Gn g b) : Gn g (a + b) where
  val := upperBlockMatrix A.val X D.val
  inv := upperBlockMatrix A.inv (-(A.inv * X * D.inv)) D.inv
  val_inv := by
    have h : A.val * (A.inv * X * D.inv) = X * D.inv := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, A.val_inv, Matrix.one_mul]
    rw [upperBlockMatrix_mul, A.val_inv, D.val_inv, Matrix.mul_neg, h, neg_add_cancel,
      upperBlockMatrix_one]
  inv_val := by
    have h : A.inv * X * D.inv * D.val = A.inv * X := by
      rw [Matrix.mul_assoc, D.inv_val, Matrix.mul_one]
    rw [upperBlockMatrix_mul, A.inv_val, D.inv_val, Matrix.neg_mul, h, add_neg_cancel,
      upperBlockMatrix_one]

theorem upperBlockUnit_mul (A A' : Gn g a) (X X' : Rect) (D D' : Gn g b) :
    upperBlockUnit A X D * upperBlockUnit A' X' D' =
      upperBlockUnit (A * A') (A.val * X' + X * D'.val) (D * D') :=
  Units.ext (upperBlockMatrix_mul _ _ _ _ _ _)

@[simp] theorem upperBlockUnit_one :
    upperBlockUnit (1 : Gn g a) (0 : Rect) (1 : Gn g b) = 1 :=
  Units.ext upperBlockMatrix_one

theorem upperBlockUnit_eq_of_mem_parabolic (x : twoBlockParabolic g a b) :
    upperBlockUnit (twoBlockLevi x).1 (upperRightBlock x.val.val) (twoBlockLevi x).2 = x.val :=
  Units.ext (upperBlockMatrix_eq x.property)

omit [Fact g.Prime] in
@[simp] theorem upperRightBlock_upperBlockMatrix (A : Mt g a) (X : Rect) (D : Mt g b) :
    upperRightBlock (upperBlockMatrix A X D) = X := by
  ext i j
  simp [upperRightBlock, upperBlockMatrix]

/-- The Levi projection reads off the diagonal blocks of an assembled unit. -/
theorem twoBlockLevi_upperBlockUnit (A : Gn g a) (X : Rect) (D : Gn g b) :
    twoBlockLevi (⟨upperBlockUnit A X D, inPar_upperBlockMatrix A.val X D.val⟩ :
      twoBlockParabolic g a b) = (A, D) := by
  rw [twoBlockLevi_val]
  have hA : tl a (upperBlockMatrix A.val X D.val) = A.val := by
    ext i j
    simp [tl_apply_add, upperBlockMatrix]
  have hD : br a b (upperBlockMatrix A.val X D.val) = D.val := by
    ext i j
    simp [br_apply_add, upperBlockMatrix]
  change (toG (tl a (upperBlockMatrix A.val X D.val)), toG (br a b (upperBlockMatrix A.val X D.val))) = _
  rw [hA, hD]
  congr 1 <;> exact Units.ext (by rw [toG, dif_pos (Units.isUnit _), IsUnit.unit_spec])

/-- The Levi kernel consists of the translations by upper-right rectangles. -/
def twoBlockRadicalEquiv :
    Multiplicative Rect ≃* (twoBlockLevi (g := g) (a := a) (b := b)).ker where
  toFun X :=
    ⟨⟨upperBlockUnit 1 X.toAdd 1, inPar_upperBlockMatrix 1 X.toAdd 1⟩,
      twoBlockLevi_upperBlockUnit 1 X.toAdd 1⟩
  invFun x := Multiplicative.ofAdd (upperRightBlock (x.val.val : Mt g (a + b)))
  left_inv X := upperRightBlock_upperBlockMatrix 1 X.toAdd 1
  right_inv x := by
    have h : twoBlockLevi x.val = 1 := x.property
    have hA : tl a (x.val.val : Mt g (a + b)) = 1 := by
      have e := congrArg (fun z : Gn g a × Gn g b => z.1.val) ((twoBlockLevi_val x.val).symm.trans h)
      have hu : IsUnit (tl a (x.val.val : Mt g (a + b))) := (twoBlockLevi x.val).1.isUnit
      change (toG (tl a (x.val.val : Mt g (a + b)))).val = 1 at e
      rw [toG, dif_pos hu, IsUnit.unit_spec] at e
      exact e
    have hD : br a b (x.val.val : Mt g (a + b)) = 1 := by
      have e := congrArg (fun z : Gn g a × Gn g b => z.2.val) ((twoBlockLevi_val x.val).symm.trans h)
      have hu : IsUnit (br a b (x.val.val : Mt g (a + b))) := (twoBlockLevi x.val).2.isUnit
      change (toG (br a b (x.val.val : Mt g (a + b)))).val = 1 at e
      rw [toG, dif_pos hu, IsUnit.unit_spec] at e
      exact e
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    change upperBlockMatrix 1 (upperRightBlock (x.val.val : Mt g (a + b))) 1 = x.val.val.val
    exact (congrArg₂ (fun A D => upperBlockMatrix A (upperRightBlock (x.val.val : Mt g (a + b))) D)
      hA hD).symm.trans (upperBlockMatrix_eq x.val.property)
  map_mul' X Y := by
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    change upperBlockMatrix 1 (X.toAdd + Y.toAdd) 1 =
      upperBlockMatrix 1 X.toAdd 1 * upperBlockMatrix 1 Y.toAdd 1
    simp only [upperBlockMatrix_mul, Matrix.one_mul, Matrix.mul_one, add_comm X.toAdd Y.toAdd]

end GlobalTheory.GLq
