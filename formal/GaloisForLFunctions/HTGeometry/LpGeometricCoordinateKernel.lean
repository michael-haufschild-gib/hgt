import GaloisForLFunctions.HTGeometry.LpFiniteCoordinateOperator
import GaloisForLFunctions.HTGeometry.HardyGeometricResolvent

/-!
# Geometric kernels in one product coordinate

The lifted KMS matrix is supported on pairs agreeing in every other coordinate.
Removing the identity removes precisely its local diagonal on that support.
-/

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.HTGeometry

variable {I : Type}

private theorem hardySingle_eq_of_decidable (d₁ d₂ : DecidableEq ℕ) (j : ℕ) :
    (@lp.single ℕ (fun _ => ℂ) (fun _ => inferInstance) d₁ 2 j (1 : ℂ) : HardyDisk) =
      @lp.single ℕ (fun _ => ℂ) (fun _ => inferInstance) d₂ 2 j (1 : ℂ) :=
  congrArg (fun d : DecidableEq ℕ =>
    (@lp.single ℕ (fun _ => ℂ) (fun _ => inferInstance) d 2 j (1 : ℂ) : HardyDisk))
      (Subsingleton.elim d₁ d₂)

/-- A geometric fibre has the exact KMS entries on its complementary-coordinate diagonal. -/
theorem lpCoordinateKMS_single_apply (i : I) {q : ℝ} (hq : ‖(q : ℂ)‖ < 1)
    (e x : I → ℕ) :
    lpCoordinateOperator (B := ℕ) i (hardyGeometricKMS hq)
      (lp.single 2 e (1 : ℂ)) x =
      (if (fun j : {j : I // j ≠ i} => x j) =
        (fun j : {j : I // j ≠ i} => e j) then 1 else 0) *
          (q : ℂ) ^ (max (x i) (e i) - min (x i) (e i)) := by
  rw [lpCoordinateOperator_single_apply]
  congr 1
  exact (congrArg (fun y : HardyDisk => hardyGeometricKMS hq y (x i))
    (hardySingle_eq_of_decidable (fun a b => Classical.propDecidable (a = b))
      instDecidableEqNat (e i))).trans (hardyGeometricKMS_single_apply hq (e i) (x i))

/-- Subtracting the global identity is exactly subtracting the local diagonal
inside the matching-coordinate fibre. -/
theorem lpCoordinateKMS_sub_one_single_apply (i : I) {q : ℝ} (hq : ‖(q : ℂ)‖ < 1)
    (e x : I → ℕ) :
    (lpCoordinateOperator (B := ℕ) i (hardyGeometricKMS hq) - 1)
      (lp.single 2 e (1 : ℂ)) x =
      if (fun j : {j : I // j ≠ i} => x j) =
          (fun j : {j : I // j ≠ i} => e j) then
        (q : ℂ) ^ (max (x i) (e i) - min (x i) (e i)) -
          if x i = e i then 1 else 0
      else 0 := by
  have hfull : x = e ↔
      ((fun j : {j : I // j ≠ i} => x j) = (fun j : {j : I // j ≠ i} => e j) ∧
        x i = e i) := by
    constructor
    · intro h
      exact ⟨congrArg (fun f : I → ℕ => fun j : {j : I // j ≠ i} => f j) h, congrFun h i⟩
    · rintro ⟨hrest, hi⟩
      funext j
      by_cases hj : j = i
      · subst j
        exact hi
      · exact congrFun hrest ⟨j, hj⟩
  change lpCoordinateOperator (B := ℕ) i (hardyGeometricKMS hq)
      (lp.single 2 e (1 : ℂ)) x - (lp.single 2 e (1 : ℂ) : lp (fun _ : I → ℕ => ℂ) 2) x = _
  rw [lpCoordinateKMS_single_apply, lp.single_apply, Pi.single_apply]
  by_cases hrest : (fun j : {j : I // j ≠ i} => x j) = (fun j : {j : I // j ≠ i} => e j)
  · simp only [if_pos hrest, one_mul]
    by_cases hi : x i = e i
    · rw [if_pos (hfull.mpr ⟨hrest, hi⟩), if_pos hi]
    · rw [if_neg (fun h => hi (hfull.mp h).2), if_neg hi]
  · simp only [if_neg hrest, if_neg (fun h => hrest (hfull.mp h).1), zero_mul, sub_zero]

end GaloisForLFunctions.HTGeometry
