import GaloisForLFunctions.RHTower.DeningerPolarSignLift
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The positive part of an invertible self-adjoint element

Continuous functional calculus supplies the positive part `|S| = (S²)^{1/2}` with exactly the
four properties the polar-sign lift needs: it is self-adjoint, commutes with `S`, squares to
`S²`, and — when `S` is invertible — is invertible.

* `deningerAbs` : the positive part.
* `deningerAbs_isSelfAdjoint`, `deningerAbs_commute`, `deningerAbs_mul_self` : the three
  algebraic properties.
* `deningerAbsInv` : the inverse, with both inverse laws.
-/

namespace RHTower

open CFC

section PositivePart

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NonnegSpectrumClass ℝ A]

/-- The positive part `|S| = (S²)^{1/2}` of a self-adjoint element. -/
noncomputable def deningerAbs (S : A) : A := CFC.sqrt (S * S)

theorem deningerAbs_nonneg (S : A) : 0 ≤ deningerAbs S := CFC.sqrt_nonneg _

/-- The positive part is self-adjoint. -/
theorem deningerAbs_isSelfAdjoint (S : A) : IsSelfAdjoint (deningerAbs S) :=
  (deningerAbs_nonneg S).isSelfAdjoint

/-- **The positive part commutes with the element.** -/
theorem deningerAbs_commute (S : A) : Commute S (deningerAbs S) := by
  have hcomm : Commute (S * S) S := (Commute.refl S).mul_left (Commute.refl S)
  rw [deningerAbs, CFC.sqrt_eq_cfc]
  exact (hcomm.cfc_nnreal _).symm

/-- **The positive part squares to the square.** -/
theorem deningerAbs_mul_self {S : A} (hS : IsSelfAdjoint S) :
    deningerAbs S * deningerAbs S = S * S := by
  refine CFC.sqrt_mul_sqrt_self _ ?_
  simpa [sq] using hS.sq_nonneg

/-- The positive part commutes with the square. -/
theorem deningerAbs_commute_sq {S : A} (hS : IsSelfAdjoint S) :
    Commute (deningerAbs S) (S * S) := by
  rw [Commute, SemiconjBy, ← deningerAbs_mul_self hS]
  noncomm_ring

section Invertible

variable {S : A} [Invertible S]

/-- The square of an invertible element is invertible. -/
noncomputable instance : Invertible (S * S) := Invertible.mul inferInstance inferInstance

/-- The inverse of the positive part. -/
noncomputable def deningerAbsInv (S : A) [Invertible S] : A := deningerAbs S * ⅟(S * S)

theorem deningerAbs_mul_absInv (hS : IsSelfAdjoint S) :
    deningerAbs S * deningerAbsInv S = 1 := by
  rw [deningerAbsInv, ← mul_assoc, deningerAbs_mul_self hS, mul_invOf_self]

theorem deningerAbsInv_mul_abs (hS : IsSelfAdjoint S) :
    deningerAbsInv S * deningerAbs S = 1 := by
  have hcomm : Commute (deningerAbs S) (⅟(S * S)) :=
    (deningerAbs_commute_sq hS).invOf_right
  rw [deningerAbsInv, mul_assoc, ← hcomm.eq, ← mul_assoc, deningerAbs_mul_self hS,
    mul_invOf_self]

/-- **The polar sign of an invertible self-adjoint element is a self-adjoint involution.** -/
theorem deningerAbs_polarSign_isSelfAdjoint (hS : IsSelfAdjoint S) :
    IsSelfAdjoint (deningerPolarSign S (deningerAbsInv S)) :=
  deningerPolarSign_isSelfAdjoint hS (deningerAbs_isSelfAdjoint S) (deningerAbs_commute S)
    (deningerAbsInv_mul_abs hS) (deningerAbs_mul_absInv hS)

theorem deningerAbs_polarSign_sq (hS : IsSelfAdjoint S) :
    deningerPolarSign S (deningerAbsInv S) * deningerPolarSign S (deningerAbsInv S) = 1 :=
  deningerPolarSign_sq (deningerAbs_commute S) (deningerAbs_mul_self hS)
    (deningerAbsInv_mul_abs hS) (deningerAbs_mul_absInv hS)

end Invertible

omit [StarOrderedRing A] in
/-- A nonnegative element has invertible `1 + ·`: its spectrum misses `-1`. -/
theorem isUnit_one_add_of_nonneg {T : A} (h : 0 ≤ T) : IsUnit (1 + T) := by
  have hnot : (-1 : ℝ) ∉ spectrum ℝ T := by
    intro hmem
    have hge := spectrum_nonneg_of_nonneg h hmem
    linarith
  rw [spectrum.mem_iff, not_not] at hnot
  have hmap : (algebraMap ℝ A (-1)) = -1 := by simp
  rw [hmap] at hnot
  have hneg : (-1 : A) - T = -(1 + T) := by abel
  rw [hneg] at hnot
  exact (IsUnit.neg_iff _).mp hnot

/-- **The positive part is one modulo the ideal.**  This is the card's factorization `(5)`, with
the inverse of `1 + |S|` supplied by positivity. -/
theorem deningerAbs_sub_one_mem {S : A} (hS : IsSelfAdjoint S) (N : TwoSidedIdeal A)
    (hmem : S * S - 1 ∈ N) : deningerAbs S - 1 ∈ N := by
  obtain ⟨u, hu⟩ := isUnit_one_add_of_nonneg (deningerAbs_nonneg S)
  have hexp : (deningerAbs S - 1) * (1 + deningerAbs S)
      = deningerAbs S * deningerAbs S - 1 := by noncomm_ring
  have hfac : (deningerAbs S - 1) * (u : A) = S * S - 1 := by
    rw [hu, hexp, deningerAbs_mul_self hS]
  have hsolve : deningerAbs S - 1 = (S * S - 1) * (↑u⁻¹ : A) := by
    rw [← hfac, mul_assoc, u.mul_inv, mul_one]
  exact deningerPolarPositive_sub_one_mem N hsolve hmem

section IdealInvertible

variable {S : A} [Invertible S]

/-- **Clause 3 for the polar sign of an invertible self-adjoint element.** -/
theorem deningerAbs_polarSign_sub_mem (hS : IsSelfAdjoint S) (N : TwoSidedIdeal A)
    (hmem : S * S - 1 ∈ N) : deningerPolarSign S (deningerAbsInv S) - S ∈ N :=
  deningerPolarSign_sub_mem N (deningerAbsInv_mul_abs hS) (deningerAbs_sub_one_mem hS N hmem)

/-- **Clause 5 for the polar sign of an invertible self-adjoint element.** -/
theorem deningerAbs_polarProjector_sub_mem [Invertible (2 : A)] (hS : IsSelfAdjoint S)
    (N : TwoSidedIdeal A) (hmem : S * S - 1 ∈ N) :
    deningerHardyProjector (deningerPolarSign S (deningerAbsInv S))
      - deningerHardyProjector S ∈ N :=
  deningerPolarProjector_sub_mem N (deningerAbsInv_mul_abs hS)
    (deningerAbs_sub_one_mem hS N hmem)

end IdealInvertible

end PositivePart

end RHTower
