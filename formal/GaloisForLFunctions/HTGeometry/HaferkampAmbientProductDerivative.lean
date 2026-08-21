import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitArchitecture

/-!
# Algebraic first variation of an ordered finite matrix product

Mathlib equips literal finite matrices with their product topology but not a
`NormedRing` structure, so its generic product-derivative theorem cannot be
applied directly.  This file records the exact algebraic Jacobian of a
time-ordered matrix word.  Later chart calculus identifies it with the
ordinary real derivative of the circuit contraction map.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Ordered ambient matrix product underlying a fixed circuit contraction. -/
def ambientOrderedMatrixProduct {N : Type*} [Fintype N] [DecidableEq N]
    (R : ℕ) (gates : Fin R → Matrix N N ℂ) : Matrix N N ℂ :=
  (List.ofFn gates).reverse.prod

/-- Algebraic first variation of an ordered ambient matrix product.  The
`i`-th summand inserts its input variation at location `i`, retaining the
literal prefix and suffix products. -/
def ambientOrderedMatrixProductDerivative
    {N : Type*} [Fintype N] [DecidableEq N] (R : ℕ)
    (gates : Fin R → Matrix N N ℂ) :
    (Fin R → Matrix N N ℂ) →ₗ[ℂ] Matrix N N ℂ :=
  ∑ i : Fin R,
    (LinearMap.mulLeft ℂ
      ((List.ofFn gates).drop i.1.succ).reverse.prod).comp
      ((LinearMap.mulRight ℂ
        ((List.ofFn gates).take i.1).reverse.prod).comp
        (LinearMap.proj i))

/-- A variation supported at exactly one gate location. -/
def ambientCoordinateDirection
    {N : Type*} [Fintype N] [DecidableEq N]
    {R : ℕ} (i : Fin R) (H : Matrix N N ℂ) : Fin R → Matrix N N ℂ :=
  Function.update 0 i H

/-- The algebraic Jacobian on a one-location variation is precisely the
prefix--variation--suffix product. -/
theorem ambientOrderedMatrixProductDerivative_apply_coordinateDirection
    {N : Type*} [Fintype N] [DecidableEq N] {R : ℕ}
    (gates : Fin R → Matrix N N ℂ) (i : Fin R) (H : Matrix N N ℂ) :
    ambientOrderedMatrixProductDerivative R gates
      (ambientCoordinateDirection i H) =
      ((List.ofFn gates).drop i.1.succ).reverse.prod * H *
        ((List.ofFn gates).take i.1).reverse.prod := by
  classical
  unfold ambientOrderedMatrixProductDerivative
  simp only [LinearMap.sum_apply]
  change (∑ x : Fin R,
      ((List.ofFn gates).drop x.1.succ).reverse.prod *
        (ambientCoordinateDirection i H x *
          ((List.ofFn gates).take x.1).reverse.prod)) = _
  rw [Finset.sum_eq_single i]
  · simp [ambientCoordinateDirection, mul_assoc]
  · intro x _ hxi
    simp [ambientCoordinateDirection, hxi]
  · simp

/-- The ambient product specializes exactly to the matrix underlying the
paper's fixed-architecture contraction. -/
theorem ambientOrderedMatrixProduct_eq_contraction
    {n R : ℕ} (A : TwoQubitArchitecture n R)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    ambientOrderedMatrixProduct R (fun r =>
      (A.gateLift r (gates r) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) =
      (A.contraction gates : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  simp [ambientOrderedMatrixProduct, TwoQubitArchitecture.contraction,
    Function.comp_def]

end

end GaloisForLFunctions.HTGeometry
