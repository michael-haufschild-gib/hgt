import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactProductDGrades1
import Mathlib.Tactic.LinearCombination

/-!
# The middle determinant product, drift-graded (2)

The grade `d` part of a product is the sum of the products of the factors'
grades over `i+j = d`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Exact product expansion used in the determinant. -/
theorem oddCompactProductD_eq (u a w : ℝ) :
    oddCompactReflectedScalar8 u a w*oddCompactCrossAD u a w = oddCompactProductD u a w := by
  rw [oddCompactReflectedScalar8_grades]
  unfold oddCompactProductD oddCompactCrossAD
  linear_combination oddCompactProductDGrade0_eq u a w +
    oddCompactProductDGrade1_eq u a w +
    oddCompactProductDGrade2_eq u a w +
    oddCompactProductDGrade3_eq u a w +
    oddCompactProductDGrade4_eq u a w +
    oddCompactProductDGrade5_eq u a w +
    oddCompactProductDGrade6_eq u a w +
    oddCompactProductDGrade7_eq u a w +
    oddCompactProductDGrade8_eq u a w +
    oddCompactProductDGrade9_eq u a w +
    oddCompactProductDGrade10_eq u a w +
    oddCompactProductDGrade11_eq u a w +
    oddCompactProductDGrade12_eq u a w +
    oddCompactProductDGrade13_eq u a w +
    oddCompactProductDGrade14_eq u a w +
    oddCompactProductDGrade15_eq u a w +
    oddCompactProductDGrade16_eq u a w +
    oddCompactProductDGrade17_eq u a w +
    oddCompactProductDGrade18_eq u a w +
    oddCompactProductDGrade19_eq u a w +
    oddCompactProductDGrade20_eq u a w +
    oddCompactProductDGrade21_eq u a w +
    oddCompactProductDGrade22_eq u a w +
    oddCompactProductDGrade23_eq u a w +
    oddCompactProductDGrade24_eq u a w +
    oddCompactProductDGrade25_eq u a w +
    oddCompactProductDGrade26_eq u a w +
    oddCompactProductDGrade27_eq u a w +
    oddCompactProductDGrade28_eq u a w +
    oddCompactProductDGrade30_eq u a w

end
end HTGeometry
