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
shifted degrees `a` and `a'` multiply to shifted degree `a + a' + 1`, with the sign of the shifted
degree of the first factor.  That sign is not a convention: without it the bar differential does not
square to zero, because the two ways of bracketing three factors then fail to cancel. -/
def augIdealShiftMulₗ (a a' : ℕ) :
    augIdealCarrier ε (a + 1) →ₗ[R]
      augIdealCarrier ε (a' + 1) →ₗ[R] augIdealCarrier ε (a + a' + 1 + 1) where
  toFun x :=
    { toFun := fun y =>
        ((-1 : R)) ^ a • augIdealMul ε (show a + 1 + (a' + 1) = a + a' + 1 + 1 by omega) x y
      map_add' := fun y y' => by
        rw [augIdealMul_add_right, smul_add]
      map_smul' := fun c y => by
        show ((-1 : R)) ^ a • augIdealMul ε _ x (c • y) = _
        rw [augIdealMul_smul_right, smul_comm]
        rfl }
  map_add' x x' := LinearMap.ext fun y => by
    show ((-1 : R)) ^ a • augIdealMul ε _ (x + x') y = _
    rw [augIdealMul_add_left, smul_add]
    rfl
  map_smul' c x := LinearMap.ext fun y => by
    show ((-1 : R)) ^ a • augIdealMul ε _ (c • x) y = _
    rw [augIdealMul_smul_left, smul_comm]
    rfl

@[simp] theorem augIdealShiftMulₗ_apply (a a' : ℕ) (x : augIdealCarrier ε (a + 1))
    (y : augIdealCarrier ε (a' + 1)) :
    augIdealShiftMulₗ ε a a' x y
      = ((-1 : R)) ^ a •
        augIdealMul ε (show a + 1 + (a' + 1) = a + a' + 1 + 1 by omega) x y := rfl

/-- The multiplication of shifted elements, out of the tensor product. -/
noncomputable def augIdealShiftMulTensor (a a' : ℕ) :
    TensorProduct R (augIdealCarrier ε (a + 1)) (augIdealCarrier ε (a' + 1)) →ₗ[R]
      augIdealCarrier ε (a + a' + 1 + 1) :=
  TensorProduct.lift (augIdealShiftMulₗ ε a a')

@[simp] theorem augIdealShiftMulTensor_tmul (a a' : ℕ) (x : augIdealCarrier ε (a + 1))
    (y : augIdealCarrier ε (a' + 1)) :
    augIdealShiftMulTensor ε a a' (x ⊗ₜ[R] y)
      = ((-1 : R)) ^ a •
        augIdealMul ε (show a + 1 + (a' + 1) = a + a' + 1 + 1 by omega) x y := rfl

/-- The multiplication of shifted elements, landing in a degree prescribed by an equation.  Keeping
the target degree a parameter is what lets associativity be stated without transporting along an
identification of degrees. -/
def augIdealShiftMulOf {a a' n : ℕ} (h : a + a' + 1 = n) (x : augIdealCarrier ε (a + 1))
    (y : augIdealCarrier ε (a' + 1)) : augIdealCarrier ε (n + 1) :=
  ((-1 : R)) ^ a • augIdealMul ε (show a + 1 + (a' + 1) = n + 1 by omega) x y

@[simp] theorem augIdealShiftMulOf_rfl (a a' : ℕ) (x : augIdealCarrier ε (a + 1))
    (y : augIdealCarrier ε (a' + 1)) :
    augIdealShiftMulOf ε (rfl : a + a' + 1 = a + a' + 1) x y = augIdealShiftMulₗ ε a a' x y := rfl

/-- **The shifted multiplication is associative up to the sign of the shift.**  This is the identity
that makes a bar differential square to zero: the two bracketings of three factors differ by
`-(-1)^p`, which is exactly the sign the tail of the bar differential contributes. -/
theorem augIdealShiftMulOf_assoc {p q r m m' n : ℕ} (h₁ : p + q + 1 = m) (h₂ : m + r + 1 = n)
    (h₃ : q + r + 1 = m') (h₄ : p + m' + 1 = n) (x : augIdealCarrier ε (p + 1))
    (y : augIdealCarrier ε (q + 1)) (z : augIdealCarrier ε (r + 1)) :
    augIdealShiftMulOf ε h₂ (augIdealShiftMulOf ε h₁ x y) z
      = (-((-1 : R)) ^ p) • augIdealShiftMulOf ε h₄ x (augIdealShiftMulOf ε h₃ y z) := by
  have hassoc := augIdealMul_assoc ε
    (show p + 1 + (q + 1) = m + 1 by omega) (show m + 1 + (r + 1) = n + 1 by omega)
    (show q + 1 + (r + 1) = m' + 1 by omega) (show p + 1 + (m' + 1) = n + 1 by omega) x y z
  show ((-1 : R)) ^ m • augIdealMul ε _ (((-1 : R)) ^ p • augIdealMul ε _ x y) z
    = (-((-1 : R)) ^ p) • (((-1 : R)) ^ p • augIdealMul ε _ x (((-1 : R)) ^ q • augIdealMul ε _ y z))
  rw [augIdealMul_smul_left, augIdealMul_smul_right, smul_smul, smul_smul, smul_smul, hassoc]
  refine congrArg (fun c : R => c • augIdealMul ε (show p + 1 + (m' + 1) = n + 1 by omega) x
    (augIdealMul ε (show q + 1 + (r + 1) = m' + 1 by omega) y z)) ?_
  have hm : m = p + q + 1 := h₁.symm
  subst hm
  have hL : ((-1 : R)) ^ (p + q + 1 + p) = -((-1 : R)) ^ q := by
    have hsplit : p + q + 1 + p = (p + p) + (q + 1) := by omega
    rw [hsplit, pow_add, Even.neg_one_pow ⟨p, rfl⟩, one_mul, pow_succ]
    ring
  have hR : -((-1 : R)) ^ p * ((-1 : R)) ^ p * ((-1 : R)) ^ q = -((-1 : R)) ^ q := by
    have hsq : ((-1 : R)) ^ p * ((-1 : R)) ^ p = 1 := by
      rw [← pow_add, Even.neg_one_pow ⟨p, rfl⟩]
    calc -((-1 : R)) ^ p * ((-1 : R)) ^ p * ((-1 : R)) ^ q
        = -(((-1 : R)) ^ p * ((-1 : R)) ^ p) * ((-1 : R)) ^ q := by ring
      _ = -((-1 : R)) ^ q := by rw [hsq]; ring
  rw [← pow_add, hL, hR]

/-- **The cancellation that makes the bar differential square to zero.**  Multiplying the first two
of three shifted factors and then the result with the third, against multiplying the last two and
then the first with the result — the second weighted by the sign the tail of the bar differential
contributes — add up to zero. -/
theorem augIdealShiftMulOf_cancel {p q r m m' n : ℕ} (h₁ : p + q + 1 = m) (h₂ : m + r + 1 = n)
    (h₃ : q + r + 1 = m') (h₄ : p + m' + 1 = n) (x : augIdealCarrier ε (p + 1))
    (y : augIdealCarrier ε (q + 1)) (z : augIdealCarrier ε (r + 1)) :
    augIdealShiftMulOf ε h₂ (augIdealShiftMulOf ε h₁ x y) z
      + ((-1 : R)) ^ p • augIdealShiftMulOf ε h₄ x (augIdealShiftMulOf ε h₃ y z) = 0 := by
  rw [augIdealShiftMulOf_assoc ε h₁ h₂ h₃ h₄ x y z, ← add_smul]
  have hzero : (-((-1 : R)) ^ p) + ((-1 : R)) ^ p = 0 := by ring
  rw [hzero, zero_smul]

end GaloisForLFunctions.HTGeometry
