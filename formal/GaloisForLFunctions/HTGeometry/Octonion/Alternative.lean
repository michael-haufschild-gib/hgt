import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

namespace GaloisForLFunctions.HTGeometry.Octonion

/-- Alternative multiplication, the exact nonassociative law used by the Cayley octonions. -/
class IsAlternative (M : Type*) [Mul M] : Prop where
  mul_alternative_left : ∀ x y : M, x * (x * y) = (x * x) * y
  mul_alternative_right : ∀ x y : M, (y * x) * x = y * (x * x)

instance (priority := 100) ofSemigroup {M : Type*} [Semigroup M] : IsAlternative M where
  mul_alternative_left x y := (mul_assoc x x y).symm
  mul_alternative_right x y := mul_assoc y x x

/-- Opposite multiplication preserves alternativity. -/
instance ofOpposite {M : Type*} [NonUnitalNonAssocRing M] [IsAlternative M] : IsAlternative Mᵐᵒᵖ where
  mul_alternative_left x y := by
    exact MulOpposite.unop_injective (IsAlternative.mul_alternative_right x.unop y.unop)
  mul_alternative_right x y := by
    exact MulOpposite.unop_injective (IsAlternative.mul_alternative_left x.unop y.unop)

namespace IsAlternative

variable {M : Type*} [NonUnitalNonAssocRing M]

/-- The associator `(x*y)*z - x*(y*z)`. -/
def associator (x y z : M) : M := (x * y) * z - x * (y * z)

theorem associator_add_left (x y z w : M) :
    associator (x + y) z w = associator x z w + associator y z w := by
  unfold associator
  simp only [add_mul]
  abel

theorem associator_add_mid (x y z w : M) :
    associator x (y + z) w = associator x y w + associator x z w := by
  unfold associator
  simp only [add_mul, mul_add]
  abel

theorem associator_add_right (x y z w : M) :
    associator x y (z + w) = associator x y z + associator x y w := by
  unfold associator
  simp only [mul_add]
  abel

theorem teichmuller (x y z w : M) :
    associator (x * y) z w - associator x (y * z) w + associator x y (z * w) =
      associator x y z * w + x * associator y z w := by
  unfold associator
  simp only [sub_mul, mul_sub]
  abel

variable [IsAlternative M]

theorem associator_self_left (x y : M) : associator x x y = 0 := by
  unfold associator
  rw [mul_alternative_left]
  abel

theorem associator_right_self (x y : M) : associator y x x = 0 := by
  unfold associator
  rw [mul_alternative_right]
  abel

theorem associator_swap_first (x y z : M) : associator x y z = -associator y x z := by
  have h : associator (x + y) (x + y) z = 0 := associator_self_left (x + y) z
  rw [associator_add_left, associator_add_mid, associator_add_mid,
    associator_self_left x z, associator_self_left y z] at h
  have h' : associator x y z + associator y x z = 0 := by
    abel_nf
    rw [zero_add, add_zero] at h
    exact h
  rw [eq_neg_iff_add_eq_zero]
  exact h'

theorem associator_swap_last (x y z : M) : associator x y z = -associator x z y := by
  have h : associator x (y + z) (y + z) = 0 := associator_right_self (y + z) x
  rw [associator_add_mid, associator_add_right, associator_add_right,
    associator_right_self y x, associator_right_self z x] at h
  have h' : associator x y z + associator x z y = 0 := by
    rw [add_zero, zero_add] at h
    exact h
  rw [add_comm] at h'
  exact (neg_eq_iff_add_eq_zero.mpr h').symm

theorem associator_swap_outer (x y z : M) : associator x y z = -associator z y x := by
  rw [associator_swap_first, associator_swap_last y x z, associator_swap_first z y x]

theorem associator_cyclic (x y z : M) : associator x y z = associator y z x := by
  rw [associator_swap_first x y z, associator_swap_last y x z, neg_neg]

theorem associator_outer_self (x y : M) : associator x y x = 0 := by
  have h : associator x y x = -associator x x y := associator_swap_last x y x
  rw [associator_self_left] at h
  rw [h]
  abel

theorem mul_flexible (x y : M) : x * (y * x) = (x * y) * x := by
  have h := associator_outer_self x y
  unfold associator at h
  rw [sub_eq_zero] at h
  exact h.symm

theorem associator_self_mul_self (x y : M) : associator x y (x * x) = 0 := by
  have h : x * (y * (x * x)) = (x * y) * (x * x) := by
    rw [← mul_alternative_right x y, mul_flexible x (y * x), mul_flexible x y,
      mul_alternative_right x (x * y)]
  unfold associator
  rw [h]
  abel

theorem associator_mul_self_self (x y : M) : associator (x * x) y x = 0 := by
  have h : (x * x) * (y * x) = ((x * x) * y) * x := by
    rw [← mul_alternative_left x (y * x), mul_flexible x y, mul_flexible x (x * y),
      mul_alternative_left x y]
  unfold associator
  rw [h]
  abel

theorem moufang_left (x y z : M) : (x * (z * x)) * y = x * (z * (x * y)) := by
  rw [← sub_eq_zero]
  have hstart : (x * (z * x)) * y - x * (z * (x * y)) =
      associator (x * z) x y + associator x z (x * y) := by
    rw [mul_flexible x z]
    unfold associator
    abel
  rw [hstart, associator_swap_first (x * z) x y, associator_swap_last x z (x * y)]
  have e1 : associator x (x * z) y = (x * x * z) * y - x * ((x * z) * y) := by
    unfold associator
    rw [mul_alternative_left]
  have e2 : associator x (x * y) z = (x * x * y) * z - x * ((x * y) * z) := by
    unfold associator
    rw [mul_alternative_left]
  rw [e1, e2]
  have lemA : associator (x * x) z y + associator (x * x) y z = 0 := by
    rw [associator_swap_last (x * x) z y]
    abel
  have lemB : associator x z y + associator x y z = 0 := by
    rw [associator_swap_last x z y]
    abel
  have e3 : (x * x * z) * y = associator (x * x) z y + (x * x) * (z * y) := by
    unfold associator
    abel
  have e4 : (x * x * y) * z = associator (x * x) y z + (x * x) * (y * z) := by
    unfold associator
    abel
  rw [e3, e4]
  rw [show (x * x) * (z * y) = x * (x * (z * y)) by exact (mul_alternative_left _ _).symm,
    show (x * x) * (y * z) = x * (x * (y * z)) by exact (mul_alternative_left _ _).symm]
  have key : -(x * (x * (z * y))) + x * ((x * z) * y) +
      (-(x * (x * (y * z))) + x * ((x * y) * z)) =
      x * (associator x z y + associator x y z) := by
    unfold associator
    simp only [mul_add, mul_sub]
    abel
  rw [lemB, mul_zero] at key
  linear_combination (norm := abel) -lemA + key

/-- The reciprocal Moufang identity, transported through opposite multiplication. -/
theorem moufang_right (x y z : M) : ((y * x) * z) * x = y * (x * (z * x)) := by
  have h := moufang_left (M := Mᵐᵒᵖ) (MulOpposite.op x) (MulOpposite.op y)
    (MulOpposite.op z)
  have h' : y * ((x * z) * x) = ((y * x) * z) * x := by
    simpa using congrArg MulOpposite.unop h
  rw [← mul_flexible x z] at h'
  exact h'.symm

/-- Schafer's associator form of the reciprocal Moufang identity. -/
theorem associator_right_mul_left (y x z : M) :
    associator y (x * z) x = -associator y x z * x := by
  have h := moufang_right x y z
  rw [mul_flexible x z] at h
  unfold associator
  rw [← h]
  rw [neg_sub, sub_mul]

/-- Schafer's linearized reciprocal Moufang identity (3.8). -/
theorem associator_right_mul_linearized (y x z u : M) :
    associator y (x * u) z + associator y (z * u) x =
      -associator y x u * z - associator y z u * x := by
  have h := associator_right_mul_left y (x + z) u
  rw [add_mul, associator_add_mid, associator_add_right, associator_add_right,
    associator_add_mid] at h
  simp only [neg_add, add_mul, mul_add] at h
  have hxx := associator_right_mul_left y x u
  have hzz := associator_right_mul_left y z u
  rw [hxx, hzz] at h
  have hnormal :
      -associator y x u * x +
          (associator y (x * u) z + (associator y (z * u) x + -associator y z u * z)) =
        -associator y x u * x +
          (-associator y z u * z + (-associator y x u * z + -associator y z u * x)) := by
    calc
      _ = (-associator y x u * x + associator y (x * u) z) +
          (associator y (z * u) x + -associator y z u * z) := by abel
      _ = (-associator y x u * x + -associator y z u * x) +
          (-associator y x u * z + -associator y z u * z) := h
      _ = _ := by abel
  have h' := add_left_cancel hnormal
  have h'' :
      (associator y (x * u) z + associator y (z * u) x) + -associator y z u * z =
        (-associator y x u * z + -associator y z u * x) + -associator y z u * z := by
    calc
      _ = associator y (x * u) z +
          (associator y (z * u) x + -associator y z u * z) := by abel
      _ = -associator y z u * z +
          (-associator y x u * z + -associator y z u * x) := h'
      _ = _ := by abel
  simpa only [neg_mul, sub_eq_add_neg] using add_right_cancel h''

/-- The common-leading-letter reduction in Artin's two-generator proof. -/
theorem artin_common_prefix_reduction (p x q r : M) :
    associator p (x * q) (x * r) =
      associator (p * q) x r * x + associator (x * r) x q * p +
        associator (x * r) p q * x := by
  rw [associator_swap_outer]
  have hlin := associator_right_mul_linearized (x * r) x p q
  have hmove : associator (x * r) (p * q) x = associator (p * q) x r * x := by
    rw [associator_swap_first, associator_right_mul_left]
    simp only [neg_mul, neg_neg]
  rw [hmove] at hlin
  simp only [sub_eq_add_neg, neg_mul] at hlin
  have hsum :
      associator (x * r) (x * q) p + associator (p * q) x r * x +
          associator (x * r) x q * p + associator (x * r) p q * x = 0 := by
    linear_combination (norm := abel) hlin
  apply neg_eq_iff_add_eq_zero.mpr
  calc
    associator (x * r) (x * q) p +
        (associator (p * q) x r * x + associator (x * r) x q * p +
          associator (x * r) p q * x) =
        associator (x * r) (x * q) p + associator (p * q) x r * x +
          associator (x * r) x q * p + associator (x * r) p q * x := by abel
    _ = 0 := hsum

theorem left_bumping (x y z : M) : associator x y (z * x) = x * associator y z x := by
  rw [← sub_eq_zero, associator_swap_last x y (z * x)]
  have e1 : associator x (z * x) y = x * (z * (x * y)) - x * ((z * x) * y) := by
    unfold associator
    rw [moufang_left]
  rw [e1]
  have cyc : associator y z x = associator z x y := associator_cyclic y z x
  have key : -(x * (z * (x * y)) - x * ((z * x) * y)) - x * associator y z x =
      x * (associator z x y - associator y z x) := by
    unfold associator
    simp only [mul_sub]
    abel
  rw [key, cyc, sub_self, mul_zero]

end IsAlternative
end GaloisForLFunctions.HTGeometry.Octonion
