import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittPerfectFieldGaloisDescent
import Mathlib.Algebra.Ring.TransferInstance

/-!
# Literal rational-Witt ring over a perfect field

Perfect-field Galois descent identifies the coefficient extension of the literal base carrier with
the absolute-Galois fixed subring of the algebraic-closure rational-Witt ring.  This module uses
that proved identification to construct the missing commutative Witt-ring structure over every
perfect field.

The resulting comparison is an actual ring equivalence with the fixed subring.  Ring addition is
proved to be multiplication of literal normalized rational functions, and Teichmüller elements
satisfy `[a] * [b] = [ab]`.  Thus Deninger's Theorem 1.2, equation (4), is represented at ring level, not
only as an equality of underlying fixed-point carriers.
-/

namespace RHTower

noncomputable section

def deningerRationalWittLiteralGaloisFixedSubring (K : Type*) [Field K] :
    Subring (DeningerRationalWittRing (AlgebraicClosure K)) where
  carrier := {w | ∀ g : DeningerRationalWittAbsoluteGalois K,
    deningerRationalWittLiteralGaloisAction K g w = w}
  zero_mem' := fun g => map_zero _
  one_mem' := fun g => map_one _
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  neg_mem' {x} hx g := by rw [map_neg, hx g]
  mul_mem' {x y} hx hy g := by rw [map_mul, hx g, hy g]

@[ext] structure DeningerPerfectRationalWittRing (K : Type*) [Field K] where
  additiveVal : Additive (DeningerRationalWittAdditive K)

noncomputable def deningerPerfectRationalWittToFixed
    (K : Type*) [Field K] (w : DeningerPerfectRationalWittRing K) :
    deningerRationalWittLiteralGaloisFixedSubring K :=
  ⟨deningerRationalWittPerfectBaseLift K (Additive.toMul w.additiveVal),
    fun g => deningerRationalWittPerfectBaseLift_galoisFixed K _ g⟩

theorem deningerPerfectRationalWittToFixed_injective
    (K : Type*) [Field K] : Function.Injective (deningerPerfectRationalWittToFixed K) := by
  intro x y hxy
  apply DeningerPerfectRationalWittRing.ext
  apply Additive.toMul.injective
  apply deningerRationalWittAdditiveMap_injective
    (algebraMap K (AlgebraicClosure K))
    (algebraMap K (AlgebraicClosure K)).injective
  have hv := congrArg
    (fun z : deningerRationalWittLiteralGaloisFixedSubring K => Additive.toMul z.1.additiveVal) hxy
  exact hv

noncomputable def deningerPerfectRationalWittFromFixed
    (K : Type*) [Field K] [PerfectField K]
    (w : deningerRationalWittLiteralGaloisFixedSubring K) : DeningerPerfectRationalWittRing K :=
  ⟨Additive.ofMul (Classical.choose
    ((deningerRationalWittLiteral_galoisFixed_iff_exists_base K w.1).mp w.2))⟩

theorem deningerPerfectRationalWittFromFixed_spec
    (K : Type*) [Field K] [PerfectField K]
    (w : deningerRationalWittLiteralGaloisFixedSubring K) :
    Additive.ofMul
        (deningerRationalWittAdditiveMap
          (algebraMap K (AlgebraicClosure K))
          (Additive.toMul (deningerPerfectRationalWittFromFixed K w).additiveVal)) =
      w.1.additiveVal := by
  exact Classical.choose_spec
    ((deningerRationalWittLiteral_galoisFixed_iff_exists_base K w.1).mp w.2)

noncomputable def deningerPerfectRationalWittCarrierEquivFixed
    (K : Type*) [Field K] [PerfectField K] :
    DeningerPerfectRationalWittRing K ≃ deningerRationalWittLiteralGaloisFixedSubring K where
  toFun := deningerPerfectRationalWittToFixed K
  invFun := deningerPerfectRationalWittFromFixed K
  left_inv w := by
    apply deningerPerfectRationalWittToFixed_injective K
    apply Subtype.ext
    apply DeningerRationalWittRing.ext
    exact deningerPerfectRationalWittFromFixed_spec K (deningerPerfectRationalWittToFixed K w)
  right_inv w := by
    apply Subtype.ext
    apply DeningerRationalWittRing.ext
    exact deningerPerfectRationalWittFromFixed_spec K w

noncomputable instance deningerPerfectRationalWittCommRing
    (K : Type*) [Field K] [PerfectField K] : CommRing (DeningerPerfectRationalWittRing K) :=
  (deningerPerfectRationalWittCarrierEquivFixed K).commRing

noncomputable def deningerPerfectRationalWittRingEquivFixed
    (K : Type*) [Field K] [PerfectField K] :
    DeningerPerfectRationalWittRing K ≃+* deningerRationalWittLiteralGaloisFixedSubring K :=
  Equiv.ringEquiv (deningerPerfectRationalWittCarrierEquivFixed K)

theorem deningerPerfectRationalWittRingEquivFixed_apply
    (K : Type*) [Field K] [PerfectField K] (w : DeningerPerfectRationalWittRing K) :
    (deningerPerfectRationalWittRingEquivFixed K w).1 =
      deningerRationalWittPerfectBaseLift K (Additive.toMul w.additiveVal) := by
  rfl

theorem deningerPerfectRationalWitt_additiveVal_add
    (K : Type*) [Field K] [PerfectField K] (x y : DeningerPerfectRationalWittRing K) :
    (x + y).additiveVal = x.additiveVal + y.additiveVal := by
  apply Additive.toMul.injective
  apply deningerRationalWittAdditiveMap_injective
    (algebraMap K (AlgebraicClosure K))
    (algebraMap K (AlgebraicClosure K)).injective
  change deningerRationalWittAdditiveMap
      (algebraMap K (AlgebraicClosure K))
      (Additive.toMul
        (deningerPerfectRationalWittFromFixed K
          (deningerPerfectRationalWittToFixed K x + deningerPerfectRationalWittToFixed K y)).additiveVal) = _
  have hs := congrArg Additive.toMul
    (deningerPerfectRationalWittFromFixed_spec K
      (deningerPerfectRationalWittToFixed K x + deningerPerfectRationalWittToFixed K y))
  change deningerRationalWittAdditiveMap
      (algebraMap K (AlgebraicClosure K))
      (Additive.toMul
        (deningerPerfectRationalWittFromFixed K
          (deningerPerfectRationalWittToFixed K x + deningerPerfectRationalWittToFixed K y)).additiveVal) =
    Additive.toMul
      (((deningerPerfectRationalWittToFixed K x + deningerPerfectRationalWittToFixed K y :
        deningerRationalWittLiteralGaloisFixedSubring K) :
          DeningerRationalWittRing (AlgebraicClosure K)).additiveVal) at hs
  have hsub :
      (((deningerPerfectRationalWittToFixed K x + deningerPerfectRationalWittToFixed K y :
        deningerRationalWittLiteralGaloisFixedSubring K) :
          DeningerRationalWittRing (AlgebraicClosure K)).additiveVal) =
        (deningerPerfectRationalWittToFixed K x).1.additiveVal +
          (deningerPerfectRationalWittToFixed K y).1.additiveVal :=
    deningerRationalWittRing_additiveVal_add _ _
  rw [hsub] at hs
  simpa [deningerPerfectRationalWittToFixed, deningerRationalWittPerfectBaseLift] using hs

noncomputable def deningerPerfectRationalWittTeichmuller
    {K : Type*} [Field K] (a : K) : DeningerPerfectRationalWittRing K :=
  ⟨Additive.ofMul (deningerRationalWittTeichmuller a)⟩

theorem deningerPerfectRationalWittRingEquivFixed_teichmuller
    (K : Type*) [Field K] [PerfectField K] (a : K) :
    (deningerPerfectRationalWittRingEquivFixed K (deningerPerfectRationalWittTeichmuller a)).1 =
      deningerRationalWittRingTeichmuller
        (algebraMap K (AlgebraicClosure K) a) := by
  apply DeningerRationalWittRing.ext
  change Additive.ofMul
      (deningerRationalWittAdditiveMap
        (algebraMap K (AlgebraicClosure K))
        (deningerRationalWittTeichmuller a)) = _
  rw [deningerRationalWittAdditiveMap_teichmuller]
  rfl

theorem deningerPerfectRationalWittTeichmuller_mul
    (K : Type*) [Field K] [PerfectField K] (a b : K) :
    deningerPerfectRationalWittTeichmuller a * deningerPerfectRationalWittTeichmuller b =
      deningerPerfectRationalWittTeichmuller (a * b) := by
  apply (deningerPerfectRationalWittRingEquivFixed K).injective
  rw [map_mul]
  apply Subtype.ext
  change (deningerPerfectRationalWittRingEquivFixed K (deningerPerfectRationalWittTeichmuller a)).1 *
      (deningerPerfectRationalWittRingEquivFixed K (deningerPerfectRationalWittTeichmuller b)).1 =
    (deningerPerfectRationalWittRingEquivFixed K (deningerPerfectRationalWittTeichmuller (a * b))).1
  rw [deningerPerfectRationalWittRingEquivFixed_teichmuller,
    deningerPerfectRationalWittRingEquivFixed_teichmuller,
    deningerPerfectRationalWittRingEquivFixed_teichmuller,
    deningerRationalWittRingTeichmuller_mul, map_mul]

end
end RHTower
