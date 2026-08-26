import GaloisForLFunctions.HTGeometry.AlgebraicTorusCharacter

/-!
# Points and evaluation on the additive-exponential group

An `L`-valued point of `Gₐⁿ × Gₘⁿ` is represented by an additive coordinate tuple and a
tuple of units.  The multiplicative wrapper turns addition on the first tuple into the group law,
so the point type inherits a commutative group.  The coordinate Hopf algebra evaluates at these
points through the tensor product of the torus group-algebra evaluator and the symmetric-algebra
evaluator.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialPointEvaluation

noncomputable section

open AffineExponentialGroup

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- `L`-valued points of the split additive-exponential group. -/
abbrev Point (L : Type*) [Field L] (n : ℕ) :=
  Multiplicative (Fin n → L) × (Fin n → Lˣ)

/-- Build a point from its additive and torus coordinate tuples. -/
def ofCoordinates {n : ℕ} (x : Fin n → L) (y : Fin n → Lˣ) : Point L n :=
  (Multiplicative.ofAdd x, y)

/-- Additive coordinate tuple of a point. -/
def additivePart {n : ℕ} (p : Point L n) : Fin n → L := p.1.toAdd

/-- Torus coordinate tuple of a point. -/
def torusPart {n : ℕ} (p : Point L n) : Fin n → Lˣ := p.2

@[simp] theorem additivePart_ofCoordinates {n : ℕ} (x : Fin n → L) (y : Fin n → Lˣ) :
    additivePart (ofCoordinates x y) = x := rfl

@[simp] theorem torusPart_ofCoordinates {n : ℕ} (x : Fin n → L) (y : Fin n → Lˣ) :
    torusPart (ofCoordinates x y) = y := rfl

@[simp] theorem additivePart_one {n : ℕ} : additivePart (1 : Point L n) = 0 := rfl

@[simp] theorem torusPart_one {n : ℕ} : torusPart (1 : Point L n) = 1 := rfl

@[simp] theorem additivePart_mul {n : ℕ} (p q : Point L n) :
    additivePart (p * q) = additivePart p + additivePart q := rfl

@[simp] theorem torusPart_mul {n : ℕ} (p q : Point L n) :
    torusPart (p * q) = torusPart p * torusPart q := rfl

@[simp] theorem additivePart_inv {n : ℕ} (p : Point L n) :
    additivePart p⁻¹ = -additivePart p := rfl

@[simp] theorem torusPart_inv {n : ℕ} (p : Point L n) :
    torusPart p⁻¹ = (torusPart p)⁻¹ := rfl

/-- Evaluation of additive-linear coordinate vectors at an `L`-valued point. -/
def additiveLinearEval {n : ℕ} (x : Fin n → L) : (Fin n → k) →ₗ[k] L where
  toFun v := ∑ i, algebraMap k L (v i) * x i
  map_add' v w := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [Algebra.smul_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem additiveLinearEval_additiveBasisVector {n : ℕ}
    (x : Fin n → L) (i : Fin n) :
    additiveLinearEval (k := k) x (additiveBasisVector k i) = x i := by
  classical
  change (∑ j, algebraMap k L ((Pi.single i (1 : k) : Fin n → k) j) * x j) = x i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Evaluation of additive symmetric coordinates at an `L`-valued point. -/
def additiveEval {n : ℕ} (x : Fin n → L) :
    AdditiveCoordinateAlgebra k n →ₐ[k] L :=
  SymmetricAlgebra.lift (additiveLinearEval (k := k) x)

@[simp] theorem additiveEval_ι {n : ℕ} (x : Fin n → L) (v : Fin n → k) :
    additiveEval (k := k) x (SymmetricAlgebra.ι k (Fin n → k) v) =
      additiveLinearEval (k := k) x v := by
  simp [additiveEval]

/-- Evaluation of the full mixed coordinate algebra at an `L`-valued point. -/
def eval {n : ℕ} (p : Point L n) : CoordinateAlgebra k n →ₐ[k] L :=
  Algebra.TensorProduct.lift
    (AlgebraicTorusCharacter.eval (k := k) (torusPart p))
    (additiveEval (k := k) (additivePart p))
    (fun _ _ ↦ Commute.all _ _)

@[simp] theorem eval_tmul {n : ℕ} (p : Point L n)
    (a : TorusCoordinateAlgebra k n) (b : AdditiveCoordinateAlgebra k n) :
    eval (k := k) p (a ⊗ₜ[k] b) =
      AlgebraicTorusCharacter.eval (k := k) (torusPart p) a *
        additiveEval (k := k) (additivePart p) b := by
  simp [eval]

@[simp] theorem eval_torusCharacter {n : ℕ} (p : Point L n) (m : Fin n →₀ ℤ) :
    eval (k := k) p (torusCharacter k m) =
      (AlgebraicTorusCharacter.character (torusPart p) m : L) := by
  simp [torusCharacter]

@[simp] theorem eval_additiveCoordinate {n : ℕ} (p : Point L n) (i : Fin n) :
    eval (k := k) p (additiveCoordinate k i) = additivePart p i := by
  simp [additiveCoordinate]

/-- Evaluation on the torus factor intertwines point multiplication and comultiplication. -/
theorem torusEval_mul_point {n : ℕ} (y z : Fin n → Lˣ)
    (a : TorusCoordinateAlgebra k n) :
    AlgebraicTorusCharacter.eval (k := k) (y * z) a =
      (Algebra.TensorProduct.lift
        (AlgebraicTorusCharacter.eval (k := k) y)
        (AlgebraicTorusCharacter.eval (k := k) z)
        (fun _ _ ↦ Commute.all _ _)) (Coalgebra.comul (R := k) a) := by
  let conv : TorusCoordinateAlgebra k n →ₐ[k] L :=
    (Algebra.TensorProduct.lift
      (AlgebraicTorusCharacter.eval (k := k) y)
      (AlgebraicTorusCharacter.eval (k := k) z)
      (fun _ _ ↦ Commute.all _ _)).comp
        (Bialgebra.comulAlgHom k (TorusCoordinateAlgebra k n))
  have hmaps : AlgebraicTorusCharacter.eval (k := k) (y * z) = conv := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      simp [conv, AlgebraicTorusCharacter.character_mul_point]
    · ext
  exact DFunLike.congr_fun hmaps a

/-- Evaluation on the additive factor intertwines point addition and comultiplication. -/
theorem additiveEval_add_point {n : ℕ} (x z : Fin n → L)
    (b : AdditiveCoordinateAlgebra k n) :
    additiveEval (k := k) (x + z) b =
      (Algebra.TensorProduct.lift
        (additiveEval (k := k) x)
        (additiveEval (k := k) z)
        (fun _ _ ↦ Commute.all _ _)) (Coalgebra.comul (R := k) b) := by
  let conv : AdditiveCoordinateAlgebra k n →ₐ[k] L :=
    (Algebra.TensorProduct.lift
      (additiveEval (k := k) x)
      (additiveEval (k := k) z)
      (fun _ _ ↦ Commute.all _ _)).comp
        (Bialgebra.comulAlgHom k (AdditiveCoordinateAlgebra k n))
  have hmaps : additiveEval (k := k) (x + z) = conv := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [conv, additiveEval, additiveLinearEval, Finset.sum_add_distrib, mul_add]
  exact DFunLike.congr_fun hmaps b

/-- Evaluation commutes with the middle-factor interchange used by the tensor-product
coalgebra.  This is the bilinear transport connecting the separate torus and additive
convolution laws. -/
theorem eval_tensorTensorTensorComm {n : ℕ} (p q : Point L n)
    (u : TorusCoordinateAlgebra k n ⊗[k] TorusCoordinateAlgebra k n)
    (v : AdditiveCoordinateAlgebra k n ⊗[k] AdditiveCoordinateAlgebra k n) :
    (Algebra.TensorProduct.lift
        (AlgebraicTorusCharacter.eval (k := k) (torusPart p))
        (AlgebraicTorusCharacter.eval (k := k) (torusPart q))
        (fun _ _ ↦ Commute.all _ _)) u *
      (Algebra.TensorProduct.lift
        (additiveEval (k := k) (additivePart p))
        (additiveEval (k := k) (additivePart q))
        (fun _ _ ↦ Commute.all _ _)) v =
      (Algebra.TensorProduct.lift
        (eval (k := k) p) (eval (k := k) q) (fun _ _ ↦ Commute.all _ _))
        ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
          k k k k
          (TorusCoordinateAlgebra k n) (TorusCoordinateAlgebra k n)
          (AdditiveCoordinateAlgebra k n) (AdditiveCoordinateAlgebra k n))
            (u ⊗ₜ[k] v)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ =>
      rw [map_add, add_mul, hu₁, hu₂, TensorProduct.add_tmul,
        LinearEquiv.map_add, map_add]
  | tmul a₁ a₂ =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ hv₁ hv₂ =>
          rw [map_add, mul_add, hv₁, hv₂, TensorProduct.tmul_add,
            LinearEquiv.map_add, map_add]
      | tmul b₁ b₂ =>
          simp [eval_tmul,
            TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
          ring

/-- Convolution of the evaluations at two points. -/
def convolutionEval {n : ℕ} (p q : Point L n) : CoordinateAlgebra k n →ₐ[k] L :=
  (Algebra.TensorProduct.lift
    (eval (k := k) p) (eval (k := k) q) (fun _ _ ↦ Commute.all _ _)).comp
      (Bialgebra.comulAlgHom k (CoordinateAlgebra k n))

/-- Full mixed evaluation intertwines point multiplication and Hopf comultiplication. -/
theorem eval_mul_point {n : ℕ} (p q : Point L n) (w : CoordinateAlgebra k n) :
    eval (k := k) (p * q) w = convolutionEval (k := k) p q w := by
  induction w using TensorProduct.induction_on with
  | zero => simp [convolutionEval]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
      rw [eval_tmul]
      simp only [additivePart_mul, torusPart_mul]
      rw [torusEval_mul_point, additiveEval_add_point]
      rw [convolutionEval, AlgHom.comp_apply]
      change _ = (Algebra.TensorProduct.lift (eval (k := k) p) (eval (k := k) q)
        (fun _ _ ↦ Commute.all _ _))
          (Coalgebra.comul (R := k) (a ⊗ₜ[k] b))
      rw [TensorProduct.comul_tmul]
      exact eval_tensorTensorTensorComm p q _ _

/-- Torus evaluation at an inverse point is evaluation after the group-algebra antipode. -/
theorem torusEval_inv_point {n : ℕ} (y : Fin n → Lˣ)
    (a : TorusCoordinateAlgebra k n) :
    AlgebraicTorusCharacter.eval (k := k) y⁻¹ a =
      AlgebraicTorusCharacter.eval (k := k) y (HopfAlgebra.antipode k a) := by
  induction a using AddMonoidAlgebra.induction_on with
  | hM m => simp [AddMonoidAlgebra.of, AlgebraicTorusCharacter.eval_single]
  | hadd a b ha hb => simp [ha, hb]
  | hsmul c a ha => simp [ha]

/-- Additive evaluation at a negative point is evaluation after the symmetric-algebra
antipode. -/
theorem additiveEval_neg_point {n : ℕ} (x : Fin n → L)
    (b : AdditiveCoordinateAlgebra k n) :
    additiveEval (k := k) (-x) b =
      additiveEval (k := k) x (HopfAlgebra.antipode k b) := by
  rw [AdditiveSymmetricHopf.antipode_eq]
  let rhs : AdditiveCoordinateAlgebra k n →ₐ[k] L :=
    (additiveEval (k := k) x).comp
      (AdditiveSymmetricHopf.antipode k (Fin n → k))
  have hmaps : additiveEval (k := k) (-x) = rhs := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [rhs, additiveEval, additiveLinearEval]
  exact DFunLike.congr_fun hmaps b

/-- Full mixed evaluation intertwines point inversion and the Hopf antipode. -/
theorem eval_inv_point {n : ℕ} (p : Point L n) (w : CoordinateAlgebra k n) :
    eval (k := k) p⁻¹ w = eval (k := k) p (HopfAlgebra.antipode k w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | tmul a b =>
      simp [TensorProduct.antipode_def, torusEval_inv_point,
        additiveEval_neg_point]

end
end AffineExponentialPointEvaluation
end GaloisForLFunctions.HTGeometry
