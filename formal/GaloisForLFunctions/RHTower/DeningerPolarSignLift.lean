import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The polar-sign lift of an almost-involution

An invertible self-adjoint element whose square is one modulo a two-sided ideal has a canonical
exact self-adjoint involution: divide by the positive part of its polar decomposition.  The
resulting sign differs from the original element by an ideal element, and so do its Hardy
projectors.

The construction only uses that the positive part `T` is self-adjoint, commutes with `S`, squares
to `S²`, and is invertible with `T + 1` invertible.  Those are exactly what continuous functional
calculus supplies for `T = |S|`, and stating them as hypotheses keeps the theorem algebraic.

* `deningerPolarSign_isSelfAdjoint`, `deningerPolarSign_sq` : the sign is a self-adjoint
  involution.
* `deningerPolarSign_sub_mem` : the sign differs from the original element by an ideal element.
* `deningerPolarProjector_sub_mem` : the Hardy projectors differ by ideal elements.
-/

namespace RHTower

section PolarSign

variable {A : Type*} [Ring A] [StarRing A]

/-- The sign of the polar decomposition, given the positive part and its inverse. -/
def deningerPolarSign (S Tinv : A) : A := S * Tinv

section Involution

variable {S T Tinv : A}

/-- The inverse of the positive part is self-adjoint. -/
theorem deningerPolarInv_isSelfAdjoint (hT : IsSelfAdjoint T)
    (hright : T * Tinv = 1) : IsSelfAdjoint Tinv := by
  have hstar : star Tinv = star Tinv * (T * Tinv) := by rw [hright, mul_one]
  rw [IsSelfAdjoint]
  calc star Tinv = star Tinv * (T * Tinv) := hstar
    _ = (star Tinv * star T) * Tinv := by rw [hT.star_eq, mul_assoc]
    _ = star (T * Tinv) * Tinv := by rw [star_mul]
    _ = Tinv := by rw [hright, star_one, one_mul]

omit [StarRing A] in
/-- The original element commutes with the inverse of the positive part. -/
theorem deningerPolar_commute_inv (hcomm : Commute S T)
    (hleft : Tinv * T = 1) (hright : T * Tinv = 1) : Commute S Tinv := by
  have h1 : Tinv * (T * S) * Tinv = S * Tinv := by
    rw [← mul_assoc Tinv T S, hleft, one_mul]
  have h2 : Tinv * (S * T) * Tinv = Tinv * S := by
    have hre : Tinv * (S * T) * Tinv = (Tinv * S) * (T * Tinv) := by noncomm_ring
    rw [hre, hright, mul_one]
  rw [Commute, SemiconjBy]
  calc S * Tinv = Tinv * (T * S) * Tinv := h1.symm
    _ = Tinv * (S * T) * Tinv := by rw [hcomm.eq]
    _ = Tinv * S := h2

/-- **The polar sign is self-adjoint.** -/
theorem deningerPolarSign_isSelfAdjoint (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hcomm : Commute S T) (hleft : Tinv * T = 1) (hright : T * Tinv = 1) :
    IsSelfAdjoint (deningerPolarSign S Tinv) := by
  have hTinv : IsSelfAdjoint Tinv := deningerPolarInv_isSelfAdjoint hT hright
  have hcommInv : Commute S Tinv := deningerPolar_commute_inv hcomm hleft hright
  rw [IsSelfAdjoint, deningerPolarSign, star_mul, hS.star_eq, hTinv.star_eq]
  exact hcommInv.eq.symm

omit [StarRing A] in
/-- **The polar sign is an involution.** -/
theorem deningerPolarSign_sq (hcomm : Commute S T) (hsq : T * T = S * S)
    (hleft : Tinv * T = 1) (hright : T * Tinv = 1) :
    deningerPolarSign S Tinv * deningerPolarSign S Tinv = 1 := by
  have hcommInv : Commute S Tinv := deningerPolar_commute_inv hcomm hleft hright
  calc deningerPolarSign S Tinv * deningerPolarSign S Tinv
      = S * (Tinv * S) * Tinv := by
        rw [deningerPolarSign]
        noncomm_ring
    _ = S * (S * Tinv) * Tinv := by rw [hcommInv.eq]
    _ = (S * S) * (Tinv * Tinv) := by noncomm_ring
    _ = (T * T) * (Tinv * Tinv) := by rw [hsq]
    _ = T * (T * Tinv) * Tinv := by noncomm_ring
    _ = 1 := by rw [hright, mul_one, hright]

end Involution

section Ideal

variable {S T Tinv U : A} (N : TwoSidedIdeal A)

omit [StarRing A] in
/-- The positive part is one modulo the ideal.  The factorization
`T - 1 = (T² - 1)(T + 1)⁻¹` is supplied as a hypothesis; continuous functional calculus gives it
for `T = |S|`, where `T + 1` is invertible by positivity. -/
theorem deningerPolarPositive_sub_one_mem
    (hfactor : T - 1 = (S * S - 1) * U) (hmem : S * S - 1 ∈ N) : T - 1 ∈ N := by
  rw [hfactor]
  exact N.mul_mem_right _ _ hmem

omit [StarRing A] in
/-- The inverse of the positive part is one modulo the ideal. -/
theorem deningerPolarInv_sub_one_mem (hleft : Tinv * T = 1)
    (hT : T - 1 ∈ N) : Tinv - 1 ∈ N := by
  have hkey : Tinv - 1 = -(Tinv * (T - 1)) := by
    rw [mul_sub, hleft, mul_one]
    noncomm_ring
  rw [hkey]
  exact N.neg_mem (N.mul_mem_left _ _ hT)

omit [StarRing A] in
/-- **The polar sign differs from the original element by an ideal element.** -/
theorem deningerPolarSign_sub_mem (hleft : Tinv * T = 1)
    (hT : T - 1 ∈ N) : deningerPolarSign S Tinv - S ∈ N := by
  have hkey : deningerPolarSign S Tinv - S = S * (Tinv - 1) := by
    rw [deningerPolarSign, mul_sub, mul_one]
  rw [hkey]
  exact N.mul_mem_left _ _ (deningerPolarInv_sub_one_mem N hleft hT)

end Ideal

section Projectors

variable {A : Type*} [Ring A] [StarRing A] [Invertible (2 : A)] {S T Tinv : A}
variable (N : TwoSidedIdeal A)

/-- The Hardy projector attached to an involution. -/
def deningerHardyProjector (C : A) : A := ⅟(2 : A) * (1 + C)

omit [StarRing A] in
/-- **The exact Hardy projectors differ from the almost-projectors by ideal elements.** -/
theorem deningerPolarProjector_sub_mem (hleft : Tinv * T = 1)
    (hT : T - 1 ∈ N) :
    deningerHardyProjector (deningerPolarSign S Tinv) - deningerHardyProjector S ∈ N := by
  have hkey : deningerHardyProjector (deningerPolarSign S Tinv) - deningerHardyProjector S
      = ⅟(2 : A) * (deningerPolarSign S Tinv - S) := by
    rw [deningerHardyProjector, deningerHardyProjector, ← mul_sub]
    noncomm_ring
  rw [hkey]
  exact N.mul_mem_left _ _ (deningerPolarSign_sub_mem N hleft hT)

end Projectors

end PolarSign

end RHTower
