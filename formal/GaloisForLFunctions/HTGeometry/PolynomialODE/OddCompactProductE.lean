import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactProductEGrades1
import Mathlib.Tactic.LinearCombination

/-!
# The leading determinant product, drift-graded (2)

The grade `d` part of a product is the sum of the products of the factors'
grades over `i+j = d`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 28 of the leading determinant product. -/
def oddCompactProductEGrade28 (u a _w : ℝ) : ℝ :=
  ((602248618125 : ℝ)*u^(28 : ℕ) +
    (-74126641225 : ℝ)*u^(28 : ℕ)*a^(1 : ℕ)) / (685529707511808 : ℝ)

/-- Drift degree 28 of the leading determinant product. -/
theorem oddCompactProductEGrade28_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade14 u a w =
      oddCompactProductEGrade28 u a w := by
  unfold oddCompactProductEGrade28 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 30 of the leading determinant product. -/
def oddCompactProductEGrade30 (u _a _w : ℝ) : ℝ :=
  ((-30655625 : ℝ)*u^(30 : ℕ)) / (4231664861184 : ℝ)

/-- Drift degree 30 of the leading determinant product. -/
theorem oddCompactProductEGrade30_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade16 u a w =
      oddCompactProductEGrade30 u a w := by
  unfold oddCompactProductEGrade30 oddCompactReflectedScalar10Grade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadPart5Grade16
  ring

/-- The leading determinant product, stored as its drift grades. -/
def oddCompactProductE (u a w : ℝ) : ℝ :=
  oddCompactProductEGrade0 u a w +
    oddCompactProductEGrade1 u a w +
    oddCompactProductEGrade2 u a w +
    oddCompactProductEGrade3 u a w +
    oddCompactProductEGrade4 u a w +
    oddCompactProductEGrade5 u a w +
    oddCompactProductEGrade6 u a w +
    oddCompactProductEGrade7 u a w +
    oddCompactProductEGrade8 u a w +
    oddCompactProductEGrade9 u a w +
    oddCompactProductEGrade10 u a w +
    oddCompactProductEGrade11 u a w +
    oddCompactProductEGrade12 u a w +
    oddCompactProductEGrade13 u a w +
    oddCompactProductEGrade14 u a w +
    oddCompactProductEGrade15 u a w +
    oddCompactProductEGrade16 u a w +
    oddCompactProductEGrade17 u a w +
    oddCompactProductEGrade18 u a w +
    oddCompactProductEGrade19 u a w +
    oddCompactProductEGrade20 u a w +
    oddCompactProductEGrade21 u a w +
    oddCompactProductEGrade22 u a w +
    oddCompactProductEGrade23 u a w +
    oddCompactProductEGrade24 u a w +
    oddCompactProductEGrade25 u a w +
    oddCompactProductEGrade26 u a w +
    oddCompactProductEGrade27 u a w +
    oddCompactProductEGrade28 u a w +
    oddCompactProductEGrade30 u a w

/-- Exact product expansion used in the determinant. -/
theorem oddCompactProductE_eq (u a w : ℝ) :
    (-oddCompactReflectedScalar10 u a w)*oddCompactScalarHead u a w = oddCompactProductE u a w := by
  rw [oddCompactReflectedScalar10_grades, oddCompactScalarHead_grades]
  unfold oddCompactProductE
  linear_combination oddCompactProductEGrade0_eq u a w +
    oddCompactProductEGrade1_eq u a w +
    oddCompactProductEGrade2_eq u a w +
    oddCompactProductEGrade3_eq u a w +
    oddCompactProductEGrade4_eq u a w +
    oddCompactProductEGrade5_eq u a w +
    oddCompactProductEGrade6_eq u a w +
    oddCompactProductEGrade7_eq u a w +
    oddCompactProductEGrade8_eq u a w +
    oddCompactProductEGrade9_eq u a w +
    oddCompactProductEGrade10_eq u a w +
    oddCompactProductEGrade11_eq u a w +
    oddCompactProductEGrade12_eq u a w +
    oddCompactProductEGrade13_eq u a w +
    oddCompactProductEGrade14_eq u a w +
    oddCompactProductEGrade15_eq u a w +
    oddCompactProductEGrade16_eq u a w +
    oddCompactProductEGrade17_eq u a w +
    oddCompactProductEGrade18_eq u a w +
    oddCompactProductEGrade19_eq u a w +
    oddCompactProductEGrade20_eq u a w +
    oddCompactProductEGrade21_eq u a w +
    oddCompactProductEGrade22_eq u a w +
    oddCompactProductEGrade23_eq u a w +
    oddCompactProductEGrade24_eq u a w +
    oddCompactProductEGrade25_eq u a w +
    oddCompactProductEGrade26_eq u a w +
    oddCompactProductEGrade27_eq u a w +
    oddCompactProductEGrade28_eq u a w +
    oddCompactProductEGrade30_eq u a w

end
end HTGeometry
