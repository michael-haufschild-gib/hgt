import GaloisForLFunctions.HTGeometry.ComplexEventSquareRealificationNoGo
import Mathlib.Tactic.Linarith

/-!
# One-sided complex-orientation reversal kills a realified event passage

The doubled-real form of a complex matrix intertwines canonical source and target complex
structures. Reversing both structures preserves this relation. Reversing exactly one endpoint is
compatible only with the zero matrix.

This is a standard linear-algebraic synchronization law. It does not derive a physical phase,
connection, force, or spacetime. In particular it shows that ordinary nonzero complex-linear
transport cannot turn a local sign choice of the imaginary unit into a rich curvature: a
nontrivial physical sewing defect would need structure beyond one-sided sign reversal of
complex-linear passages.
-/

open Matrix
open scoped Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {m n : Type*}

/-- Realification sends the zero complex matrix to the zero doubled-real matrix. -/
theorem complexMatrixRealification_zero :
    complexMatrixRealification (0 : Matrix m n ℂ) = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexMatrixRealification, complexMatrixRealPart,
      complexMatrixImagPart]

/-- Reversing complex orientation at both endpoints preserves every realified complex passage. -/
theorem complexMatrixRealification_joint_orientation_reversal
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    (-doubledRealComplexStructure (n := m)) * complexMatrixRealification X =
      complexMatrixRealification X * (-doubledRealComplexStructure (n := n)) := by
  have h := complexMatrixRealification_intertwines_complexStructure X
  simpa only [Matrix.neg_mul, Matrix.mul_neg] using congrArg Neg.neg h

/-- Reversing only target complex orientation is compatible exactly with the zero passage. -/
theorem complexMatrixRealification_target_orientation_reversal_iff_zero
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    doubledRealComplexStructure (n := m) * complexMatrixRealification X =
        complexMatrixRealification X * (-doubledRealComplexStructure (n := n)) ↔
      X = 0 := by
  constructor
  · intro h
    have hneg :
        doubledRealComplexStructure (n := m) * complexMatrixRealification X =
          -(complexMatrixRealification X *
            doubledRealComplexStructure (n := n)) := by
      simpa only [Matrix.mul_neg] using h
    have hstandard :=
      complexMatrixRealification_intertwines_complexStructure X
    have hphase :
        complexMatrixRealification X * doubledRealComplexStructure (n := n) =
          -(complexMatrixRealification X *
            doubledRealComplexStructure (n := n)) :=
      hstandard.symm.trans hneg
    rw [realification_mul_doubledRealComplexStructure] at hphase
    ext i j
    apply Complex.ext
    · have hre := congrFun (congrFun hphase (Sum.inl i)) (Sum.inr j)
      simp [complexMatrixRealification, complexMatrixImagPart] at hre
      change (X i j).re = 0
      linarith
    · have him := congrFun (congrFun hphase (Sum.inl i)) (Sum.inl j)
      simp [complexMatrixRealification, complexMatrixRealPart] at him
      change (X i j).im = 0
      linarith
  · rintro rfl
    rw [complexMatrixRealification_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- Reversing only source complex orientation is compatible exactly with the zero passage. -/
theorem complexMatrixRealification_source_orientation_reversal_iff_zero
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    (-doubledRealComplexStructure (n := m)) * complexMatrixRealification X =
        complexMatrixRealification X * doubledRealComplexStructure (n := n) ↔
      X = 0 := by
  constructor
  · intro h
    apply (complexMatrixRealification_target_orientation_reversal_iff_zero X).mp
    have hn := congrArg Neg.neg h
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hn
  · rintro rfl
    rw [complexMatrixRealification_zero, Matrix.mul_zero, Matrix.zero_mul]

end GaloisForLFunctions.HTGeometry
