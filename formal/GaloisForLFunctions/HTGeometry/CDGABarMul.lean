import GaloisForLFunctions.HTGeometry.CDGACochain
import GaloisForLFunctions.HTGeometry.CDGATensorDegOne

/-!
# The multiplication of two shifted elements of an augmentation ideal

Multiplying two elements of the shifted augmentation ideal, of shifted degrees `a` and `a'`, gives
an element of the ideal in degree `a + a' + 2`, that is of shifted degree `a + a' + 1`.  So the
multiplication is a map of degree one on the shift, which is what makes the bar differential raise
the total degree by one.

* `HTGeometry.augIdealShiftMulₗ` : the multiplication as a bilinear map on the shift.
* `HTGeometry.augIdealShiftMulTensor` : the same, out of the tensor product.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

/-- **The multiplication of two shifted elements of the augmentation ideal**, as a bilinear map:
shifted degrees `a` and `a'` multiply to shifted degree `a + a' + 1`. -/
def augIdealShiftMulₗ (a a' : ℕ) :
    augIdealCarrier ε (a + 1) →ₗ[R]
      augIdealCarrier ε (a' + 1) →ₗ[R] augIdealCarrier ε (a + a' + 1 + 1) where
  toFun x :=
    { toFun := fun y => augIdealMul ε (show a + 1 + (a' + 1) = a + a' + 1 + 1 by omega) x y
      map_add' := fun y y' => augIdealMul_add_right ε _ x y y'
      map_smul' := fun c y => augIdealMul_smul_right ε _ c x y }
  map_add' x x' := LinearMap.ext fun y => augIdealMul_add_left ε _ x x' y
  map_smul' c x := LinearMap.ext fun y => augIdealMul_smul_left ε _ c x y

@[simp] theorem augIdealShiftMulₗ_apply (a a' : ℕ) (x : augIdealCarrier ε (a + 1))
    (y : augIdealCarrier ε (a' + 1)) :
    augIdealShiftMulₗ ε a a' x y
      = augIdealMul ε (show a + 1 + (a' + 1) = a + a' + 1 + 1 by omega) x y := rfl

/-- The multiplication of shifted elements, out of the tensor product. -/
noncomputable def augIdealShiftMulTensor (a a' : ℕ) :
    TensorProduct R (augIdealCarrier ε (a + 1)) (augIdealCarrier ε (a' + 1)) →ₗ[R]
      augIdealCarrier ε (a + a' + 1 + 1) :=
  TensorProduct.lift (augIdealShiftMulₗ ε a a')

@[simp] theorem augIdealShiftMulTensor_tmul (a a' : ℕ) (x : augIdealCarrier ε (a + 1))
    (y : augIdealCarrier ε (a' + 1)) :
    augIdealShiftMulTensor ε a a' (x ⊗ₜ[R] y)
      = augIdealMul ε (show a + 1 + (a' + 1) = a + a' + 1 + 1 by omega) x y := rfl

end GaloisForLFunctions.HTGeometry
