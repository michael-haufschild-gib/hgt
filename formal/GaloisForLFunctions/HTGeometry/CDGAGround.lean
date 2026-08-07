import GaloisForLFunctions.HTGeometry.CDGAConstCell
import GaloisForLFunctions.HTGeometry.CDGAUnital

/-!
# The ground ring as a commutative differential graded algebra

The ground ring placed in degree zero, with zero differential, is a commutative differential graded
algebra: the product is the product of `R` in the only degree where anything lives, and every
identity involving the differential holds because its target is concentrated away from degree zero,
hence a subsingleton.

This is the unit object of the tensor product of algebras, and the target of an augmentation.

* `HTGeometry.groundCDGA` : the ground ring as an algebra.
* `HTGeometry.groundCDGAUnit` : its unit.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

variable (R : Type u) [CommRing R]

theorem groundCarrierSubsingleton {n : ℕ} (h : n ≠ 0) :
    Subsingleton (ConstCellCarrier R 0 n) :=
  constCellCarrier_subsingleton h

/-- **The ground ring, concentrated in degree zero.** -/
def groundCDGA : CDGAStructure R (ConstCellCarrier R 0) where
  mul {a b n} _ x y := fun p => x ⟨by have := p.down; omega⟩ * y ⟨by have := p.down; omega⟩
  d _ _ := fun p => absurd p.down (by omega)
  mul_add_left _ x x' y := by
    funext p
    show (x _ + x' _) * y _ = x _ * y _ + x' _ * y _
    ring
  mul_add_right _ x y y' := by
    funext p
    show x _ * (y _ + y' _) = x _ * y _ + x _ * y' _
    ring
  mul_smul_left _ c x y := by
    funext p
    show (c • x _) * y _ = c • (x _ * y _)
    simp only [smul_eq_mul]
    ring
  mul_smul_right _ c x y := by
    funext p
    show x _ * (c • y _) = c • (x _ * y _)
    simp only [smul_eq_mul]
    ring
  mul_assoc _ _ _ _ x y z := by
    funext p
    show (x _ * y _) * z _ = x _ * (y _ * z _)
    ring
  mul_comm := by
    intro a b n h h' x y
    funext p
    have hn : n = 0 := p.down
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    show x _ * y _ = ((-1 : R)) ^ (0 * 0) • (y _ * x _)
    rw [Nat.zero_mul, pow_zero, one_smul]
    ring
  d_add n _ _ := @Subsingleton.elim _ (groundCarrierSubsingleton R (by omega)) _ _
  d_smul n _ _ := @Subsingleton.elim _ (groundCarrierSubsingleton R (by omega)) _ _
  d_d n _ := @Subsingleton.elim _ (groundCarrierSubsingleton R (by omega)) _ _
  d_mul := by
    intro a b n h x y
    exact @Subsingleton.elim _ (groundCarrierSubsingleton R (by omega)) _ _

/-- **The unit of the ground algebra.** -/
def groundCDGAUnit : CDGAUnit (groundCDGA R) where
  one := fun _ => 1
  one_mul b y := by
    funext p
    show (1 : R) * y _ = y _
    rw [one_mul]
  d_one := @Subsingleton.elim _ (groundCarrierSubsingleton R (by omega)) _ _

end GaloisForLFunctions.HTGeometry
