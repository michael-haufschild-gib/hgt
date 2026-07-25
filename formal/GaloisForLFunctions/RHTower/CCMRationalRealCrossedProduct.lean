import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import GaloisForLFunctions.RHTower.CCMRationalQuaternionicMoritaFiber

/-!
# Real structure on the algebraic rational CCM crossed product

This file extends the rational CCM monomial twist

`αₖ(φ)(x) = sign(k) * conj (φ (-x))`

from single monomials to the full finite-support skew group algebra.  It proves unconditionally
that the resulting map is a conjugate-linear, unital, multiplicative involution.

The wrapper `CCMRationalScaling` prevents Lean's existing scalar action of `ℚˣ` from being
confused with the left-translation action used in the crossed product.

Only the algebraic finite-support core is treated. No Schwartz topology, bornology, trace-class
completion, cyclic homology, positivity, zero spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Rational scaling labels, separated from the scalar action of `ℚˣ` on coefficient values. -/
structure CCMRationalScaling where
  val : CCMRationalUnit

/-- The scaling-label wrapper is canonically equivalent to `ℚˣ`. -/
def ccmRationalScalingEquiv : CCMRationalScaling ≃ CCMRationalUnit where
  toFun := CCMRationalScaling.val
  invFun := CCMRationalScaling.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Group CCMRationalScaling := ccmRationalScalingEquiv.group

@[simp]
theorem ccmRationalScaling_one_val :
    (1 : CCMRationalScaling).val = 1 :=
  rfl

@[simp]
theorem ccmRationalScaling_mul_val (k l : CCMRationalScaling) :
    (k * l).val = k.val * l.val :=
  rfl

/-- Rational scaling acts on coefficient functions by left translation. -/
instance : SMul CCMRationalScaling (CCMRationalUnit → ℂ) where
  smul k φ := ccmRationalLeftScale k.val φ

/-- Left translation is an action by coefficient-ring automorphisms. -/
instance : MulSemiringAction CCMRationalScaling (CCMRationalUnit → ℂ) where
  smul_zero k := by
    funext x
    rfl
  smul_add k φ ψ := by
    funext x
    rfl
  smul_one k := by
    funext x
    rfl
  smul_mul k φ ψ := by
    funext x
    rfl
  one_smul φ := by
    funext x
    change φ ((1 : CCMRationalScaling).val⁻¹ * x) = φ x
    rw [ccmRationalScaling_one_val]
    simp
  mul_smul k l φ := by
    funext x
    change φ ((k * l).val⁻¹ * x) =
      φ (l.val⁻¹ * (k.val⁻¹ * x))
    rw [ccmRationalScaling_mul_val, mul_inv_rev]
    congr 1
    group

/-- Finite-support algebraic rational CCM crossed product. -/
abbrev CCMRationalAlgebraicCrossedProduct :=
  SkewMonoidAlgebra (CCMRationalUnit → ℂ) CCMRationalScaling

/-- Real structure on the finite-support rational CCM crossed product. -/
def ccmRationalCrossedProductRealStructure
    (F : CCMRationalAlgebraicCrossedProduct) :
    CCMRationalAlgebraicCrossedProduct :=
  F.sum fun k φ =>
    SkewMonoidAlgebra.single k
      (ccmRationalMonomialRealTwist k.val φ)

@[simp]
theorem ccmRationalCrossedProductRealStructure_single
    (k : CCMRationalScaling) (φ : CCMRationalUnit → ℂ) :
    ccmRationalCrossedProductRealStructure
        (SkewMonoidAlgebra.single k φ) =
      SkewMonoidAlgebra.single k
        (ccmRationalMonomialRealTwist k.val φ) := by
  unfold ccmRationalCrossedProductRealStructure
  rw [SkewMonoidAlgebra.sum_single_index]
  rw [show ccmRationalMonomialRealTwist k.val 0 = 0 by
    funext x
    simp [ccmRationalMonomialRealTwist]]
  exact SkewMonoidAlgebra.single_zero k

/-- The crossed-product Real structure is additive. -/
theorem ccmRationalCrossedProductRealStructure_add
    (F G : CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductRealStructure (F + G) =
      ccmRationalCrossedProductRealStructure F +
        ccmRationalCrossedProductRealStructure G := by
  classical
  unfold ccmRationalCrossedProductRealStructure
  apply SkewMonoidAlgebra.sum_add_index'
  · intro k
    rw [show ccmRationalMonomialRealTwist k.val 0 = 0 by
      funext x
      simp [ccmRationalMonomialRealTwist]]
    exact SkewMonoidAlgebra.single_zero k
  · intro k φ ψ
    rw [ccmRationalMonomialRealTwist_add, SkewMonoidAlgebra.single_add]

/-- The crossed-product Real structure is complex conjugate-linear. -/
theorem ccmRationalCrossedProductRealStructure_smul
    (z : ℂ) (F : CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductRealStructure (z • F) =
      star z • ccmRationalCrossedProductRealStructure F := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp [ccmRationalCrossedProductRealStructure]
  | add F G hF hG =>
      rw [smul_add, ccmRationalCrossedProductRealStructure_add,
        ccmRationalCrossedProductRealStructure_add, hF, hG, smul_add]
  | single k φ =>
      rw [SkewMonoidAlgebra.smul_single,
        ccmRationalCrossedProductRealStructure_single,
        ccmRationalMonomialRealTwist_smul,
        ccmRationalCrossedProductRealStructure_single,
        SkewMonoidAlgebra.smul_single]

/-- Crossed-product Real structure bundled as a conjugate-linear map. -/
def ccmRationalCrossedProductRealStructureₛₗ :
    CCMRationalAlgebraicCrossedProduct →ₗ⋆[ℂ]
      CCMRationalAlgebraicCrossedProduct where
  toFun := ccmRationalCrossedProductRealStructure
  map_add' := ccmRationalCrossedProductRealStructure_add
  map_smul' := ccmRationalCrossedProductRealStructure_smul

/-- The crossed-product Real structure is involutive. -/
theorem ccmRationalCrossedProductRealStructure_sq
    (F : CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductRealStructure
        (ccmRationalCrossedProductRealStructure F) = F := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp [ccmRationalCrossedProductRealStructure]
  | add F G hF hG =>
      rw [ccmRationalCrossedProductRealStructure_add,
        ccmRationalCrossedProductRealStructure_add, hF, hG]
  | single k φ =>
      simp [ccmRationalMonomialRealTwist_sq]

/-- The crossed-product Real structure preserves the unit. -/
theorem ccmRationalCrossedProductRealStructure_one :
    ccmRationalCrossedProductRealStructure 1 = 1 := by
  rw [SkewMonoidAlgebra.one_def,
    ccmRationalCrossedProductRealStructure_single]
  congr 1
  funext x
  simp [ccmRationalMonomialRealTwist, ccmRationalUnitSign]

/-- The crossed-product Real structure preserves multiplication. -/
theorem ccmRationalCrossedProductRealStructure_mul
    (F G : CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductRealStructure (F * G) =
      ccmRationalCrossedProductRealStructure F *
        ccmRationalCrossedProductRealStructure G := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp [ccmRationalCrossedProductRealStructure]
  | add F₁ F₂ hF₁ hF₂ =>
      rw [add_mul, ccmRationalCrossedProductRealStructure_add,
        ccmRationalCrossedProductRealStructure_add, hF₁, hF₂, add_mul]
  | single k φ =>
      induction G using SkewMonoidAlgebra.induction_on with
      | zero => simp [ccmRationalCrossedProductRealStructure]
      | add G₁ G₂ hG₁ hG₂ =>
          rw [mul_add, ccmRationalCrossedProductRealStructure_add,
            ccmRationalCrossedProductRealStructure_add, hG₁, hG₂, mul_add]
      | single l ψ =>
          simp only [SkewMonoidAlgebra.single_mul_single,
            ccmRationalCrossedProductRealStructure_single,
            ccmRationalScaling_mul_val]
          congr 1
          exact ccmRationalMonomialRealTwist_product k.val l.val φ ψ

end RHTower
end GaloisForLFunctions
