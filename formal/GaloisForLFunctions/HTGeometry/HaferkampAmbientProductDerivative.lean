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

/-- If a physical gate word factors at one selected coordinate and every
later gate is the identity, the ordered-product derivative at that coordinate
is its inserted matrix followed by the reverse product of earlier gates. -/
theorem ambientOrderedMatrixProductDerivative_list_coordinate_of_suffix_one
    {N : Type*} [Fintype N] [DecidableEq N]
    (matrices before after : List (Matrix N N ℂ)) (gate : Matrix N N ℂ)
    (hmatrices : matrices = before ++ gate :: after)
    (hafter : ∀ M ∈ after, M = 1) (H : Matrix N N ℂ) :
    let i : Fin matrices.length := ⟨before.length, by rw [hmatrices]; simp⟩
    ambientOrderedMatrixProductDerivative matrices.length (fun j => matrices.get j)
      (ambientCoordinateDirection i H) = H * before.reverse.prod := by
  dsimp
  rw [ambientOrderedMatrixProductDerivative_apply_coordinateDirection]
  change ((List.ofFn matrices.get).drop before.length.succ).reverse.prod * H *
      ((List.ofFn matrices.get).take before.length).reverse.prod =
    H * before.reverse.prod
  rw [List.ofFn_get]
  rw [hmatrices]
  have hdrop : List.drop before.length.succ (before ++ gate :: after) = after := by
    rw [List.drop_append, List.drop_eq_nil_of_le (Nat.le_succ _)]
    rw [Nat.succ_sub (Nat.le_refl _)]
    simp only [Nat.sub_self, List.drop_succ_cons,
      List.drop_zero, List.nil_append]
  have htake : List.take before.length (before ++ gate :: after) = before := by
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  rw [hdrop, htake]
  have hafterReverse : ∀ M ∈ after.reverse, M = 1 := by
    intro M hM
    exact hafter M (by simpa using hM)
  rw [List.prod_eq_one hafterReverse]
  simp

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
