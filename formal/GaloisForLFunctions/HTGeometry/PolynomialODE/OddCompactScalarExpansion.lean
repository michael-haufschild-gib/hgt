import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactProductC
import Mathlib.Tactic.LinearCombination

/-!
# Factored scalar determinant expansion (0)

`Det = E - D + C` holds in each drift grade separately.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 0 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade0_eq (u a w : ℝ) :
    oddCompactProductEGrade0 u a w - oddCompactProductDGrade0 u a w + oddCompactProductCGrade0 u a w =
      oddCompactScalarDetGrade0 u a w := by
  unfold oddCompactProductCGrade0 oddCompactProductDGrade0 oddCompactProductEGrade0 oddCompactScalarDetGrade0 oddCompactScalarDetPart0Grade0 oddCompactScalarDetPart1Grade0 oddCompactScalarDetPart2Grade0
  ring

/-- Drift degree 1 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade1_eq (u a w : ℝ) :
    oddCompactProductEGrade1 u a w - oddCompactProductDGrade1 u a w + oddCompactProductCGrade1 u a w =
      oddCompactScalarDetGrade1 u a w := by
  unfold oddCompactProductCGrade1 oddCompactProductDGrade1 oddCompactProductEGrade1 oddCompactScalarDetGrade1 oddCompactScalarDetPart2Grade1 oddCompactScalarDetPart3Grade1 oddCompactScalarDetPart4Grade1 oddCompactScalarDetPart5Grade1
  ring

/-- Drift degree 2 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade2_eq (u a w : ℝ) :
    oddCompactProductEGrade2 u a w - oddCompactProductDGrade2 u a w + oddCompactProductCGrade2 u a w =
      oddCompactScalarDetGrade2 u a w := by
  unfold oddCompactProductCGrade2 oddCompactProductCGrade2Part0 oddCompactProductCGrade2Part1 oddCompactProductDGrade2 oddCompactProductDGrade2Part0 oddCompactProductDGrade2Part1 oddCompactProductEGrade2 oddCompactProductEGrade2Part0 oddCompactProductEGrade2Part1 oddCompactScalarDetGrade2 oddCompactScalarDetPart5Grade2 oddCompactScalarDetPart6Grade2 oddCompactScalarDetPart7Grade2
  ring

/-- Drift degree 3 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade3_eq (u a w : ℝ) :
    oddCompactProductEGrade3 u a w - oddCompactProductDGrade3 u a w + oddCompactProductCGrade3 u a w =
      oddCompactScalarDetGrade3 u a w := by
  unfold oddCompactProductCGrade3 oddCompactProductCGrade3Part0 oddCompactProductCGrade3Part1 oddCompactProductDGrade3 oddCompactProductDGrade3Part0 oddCompactProductDGrade3Part1 oddCompactProductEGrade3 oddCompactProductEGrade3Part0 oddCompactProductEGrade3Part1 oddCompactScalarDetGrade3 oddCompactScalarDetPart7Grade3 oddCompactScalarDetPart8Grade3 oddCompactScalarDetPart9Grade3
  ring

/-- Drift degree 4 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade4_eq (u a w : ℝ) :
    oddCompactProductEGrade4 u a w - oddCompactProductDGrade4 u a w + oddCompactProductCGrade4 u a w =
      oddCompactScalarDetGrade4 u a w := by
  unfold oddCompactProductCGrade4 oddCompactProductCGrade4Part0 oddCompactProductCGrade4Part1 oddCompactProductDGrade4 oddCompactProductDGrade4Part0 oddCompactProductDGrade4Part1 oddCompactProductEGrade4 oddCompactProductEGrade4Part0 oddCompactProductEGrade4Part1 oddCompactScalarDetGrade4 oddCompactScalarDetPart10Grade4 oddCompactScalarDetPart11Grade4 oddCompactScalarDetPart12Grade4
  ring

/-- Drift degree 5 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade5_eq (u a w : ℝ) :
    oddCompactProductEGrade5 u a w - oddCompactProductDGrade5 u a w + oddCompactProductCGrade5 u a w =
      oddCompactScalarDetGrade5 u a w := by
  unfold oddCompactProductCGrade5 oddCompactProductCGrade5Part0 oddCompactProductCGrade5Part1 oddCompactProductDGrade5 oddCompactProductDGrade5Part0 oddCompactProductDGrade5Part1 oddCompactProductEGrade5 oddCompactProductEGrade5Part0 oddCompactProductEGrade5Part1 oddCompactScalarDetGrade5 oddCompactScalarDetPart12Grade5 oddCompactScalarDetPart13Grade5 oddCompactScalarDetPart14Grade5
  ring

/-- Drift degree 6 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade6_eq (u a w : ℝ) :
    oddCompactProductEGrade6 u a w - oddCompactProductDGrade6 u a w + oddCompactProductCGrade6 u a w =
      oddCompactScalarDetGrade6 u a w := by
  unfold oddCompactProductCGrade6 oddCompactProductCGrade6Part0 oddCompactProductCGrade6Part1 oddCompactProductDGrade6 oddCompactProductDGrade6Part0 oddCompactProductDGrade6Part1 oddCompactProductEGrade6 oddCompactProductEGrade6Part0 oddCompactProductEGrade6Part1 oddCompactScalarDetGrade6 oddCompactScalarDetPart14Grade6 oddCompactScalarDetPart15Grade6 oddCompactScalarDetPart16Grade6
  ring

/-- Drift degree 7 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade7_eq (u a w : ℝ) :
    oddCompactProductEGrade7 u a w - oddCompactProductDGrade7 u a w + oddCompactProductCGrade7 u a w =
      oddCompactScalarDetGrade7 u a w := by
  unfold oddCompactProductCGrade7 oddCompactProductCGrade7Part0 oddCompactProductCGrade7Part1 oddCompactProductDGrade7 oddCompactProductDGrade7Part0 oddCompactProductDGrade7Part1 oddCompactProductEGrade7 oddCompactProductEGrade7Part0 oddCompactProductEGrade7Part1 oddCompactScalarDetGrade7 oddCompactScalarDetPart16Grade7 oddCompactScalarDetPart17Grade7 oddCompactScalarDetPart18Grade7
  ring

/-- Drift degree 8 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade8_eq (u a w : ℝ) :
    oddCompactProductEGrade8 u a w - oddCompactProductDGrade8 u a w + oddCompactProductCGrade8 u a w =
      oddCompactScalarDetGrade8 u a w := by
  unfold oddCompactProductCGrade8 oddCompactProductCGrade8Part0 oddCompactProductCGrade8Part1 oddCompactProductDGrade8 oddCompactProductDGrade8Part0 oddCompactProductDGrade8Part1 oddCompactProductEGrade8 oddCompactProductEGrade8Part0 oddCompactProductEGrade8Part1 oddCompactScalarDetGrade8 oddCompactScalarDetPart18Grade8 oddCompactScalarDetPart19Grade8 oddCompactScalarDetPart20Grade8
  ring

/-- Drift degree 9 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade9_eq (u a w : ℝ) :
    oddCompactProductEGrade9 u a w - oddCompactProductDGrade9 u a w + oddCompactProductCGrade9 u a w =
      oddCompactScalarDetGrade9 u a w := by
  unfold oddCompactProductCGrade9 oddCompactProductCGrade9Part0 oddCompactProductCGrade9Part1 oddCompactProductDGrade9 oddCompactProductDGrade9Part0 oddCompactProductDGrade9Part1 oddCompactProductEGrade9 oddCompactProductEGrade9Part0 oddCompactProductEGrade9Part1 oddCompactScalarDetGrade9 oddCompactScalarDetPart20Grade9 oddCompactScalarDetPart21Grade9
  ring

/-- Drift degree 10 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade10_eq (u a w : ℝ) :
    oddCompactProductEGrade10 u a w - oddCompactProductDGrade10 u a w + oddCompactProductCGrade10 u a w =
      oddCompactScalarDetGrade10 u a w := by
  unfold oddCompactProductCGrade10 oddCompactProductCGrade10Part0 oddCompactProductCGrade10Part1 oddCompactProductDGrade10 oddCompactProductDGrade10Part0 oddCompactProductDGrade10Part1 oddCompactProductEGrade10 oddCompactProductEGrade10Part0 oddCompactProductEGrade10Part1 oddCompactScalarDetGrade10 oddCompactScalarDetPart21Grade10 oddCompactScalarDetPart22Grade10 oddCompactScalarDetPart23Grade10
  ring

/-- Drift degree 11 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade11_eq (u a w : ℝ) :
    oddCompactProductEGrade11 u a w - oddCompactProductDGrade11 u a w + oddCompactProductCGrade11 u a w =
      oddCompactScalarDetGrade11 u a w := by
  unfold oddCompactProductCGrade11 oddCompactProductDGrade11 oddCompactProductDGrade11Part0 oddCompactProductDGrade11Part1 oddCompactProductEGrade11 oddCompactProductEGrade11Part0 oddCompactProductEGrade11Part1 oddCompactScalarDetGrade11 oddCompactScalarDetPart23Grade11 oddCompactScalarDetPart24Grade11
  ring

/-- Drift degree 12 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade12_eq (u a w : ℝ) :
    oddCompactProductEGrade12 u a w - oddCompactProductDGrade12 u a w + oddCompactProductCGrade12 u a w =
      oddCompactScalarDetGrade12 u a w := by
  unfold oddCompactProductCGrade12 oddCompactProductDGrade12 oddCompactProductEGrade12 oddCompactProductEGrade12Part0 oddCompactProductEGrade12Part1 oddCompactScalarDetGrade12 oddCompactScalarDetPart24Grade12 oddCompactScalarDetPart25Grade12
  ring

/-- Drift degree 13 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade13_eq (u a w : ℝ) :
    oddCompactProductEGrade13 u a w - oddCompactProductDGrade13 u a w + oddCompactProductCGrade13 u a w =
      oddCompactScalarDetGrade13 u a w := by
  unfold oddCompactProductCGrade13 oddCompactProductDGrade13 oddCompactProductEGrade13 oddCompactScalarDetGrade13 oddCompactScalarDetPart25Grade13 oddCompactScalarDetPart26Grade13
  ring

/-- Drift degree 14 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade14_eq (u a w : ℝ) :
    oddCompactProductEGrade14 u a w - oddCompactProductDGrade14 u a w + oddCompactProductCGrade14 u a w =
      oddCompactScalarDetGrade14 u a w := by
  unfold oddCompactProductCGrade14 oddCompactProductDGrade14 oddCompactProductEGrade14 oddCompactScalarDetGrade14 oddCompactScalarDetPart26Grade14 oddCompactScalarDetPart27Grade14 oddCompactScalarDetPart28Grade14
  ring

/-- Drift degree 15 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade15_eq (u a w : ℝ) :
    oddCompactProductEGrade15 u a w - oddCompactProductDGrade15 u a w + oddCompactProductCGrade15 u a w =
      oddCompactScalarDetGrade15 u a w := by
  unfold oddCompactProductCGrade15 oddCompactProductDGrade15 oddCompactProductEGrade15 oddCompactScalarDetGrade15 oddCompactScalarDetPart28Grade15
  ring

/-- Drift degree 16 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade16_eq (u a w : ℝ) :
    oddCompactProductEGrade16 u a w - oddCompactProductDGrade16 u a w + oddCompactProductCGrade16 u a w =
      oddCompactScalarDetGrade16 u a w := by
  unfold oddCompactProductCGrade16 oddCompactProductDGrade16 oddCompactProductEGrade16 oddCompactScalarDetGrade16 oddCompactScalarDetPart28Grade16 oddCompactScalarDetPart29Grade16
  ring

/-- Drift degree 17 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade17_eq (u a w : ℝ) :
    oddCompactProductEGrade17 u a w - oddCompactProductDGrade17 u a w + oddCompactProductCGrade17 u a w =
      oddCompactScalarDetGrade17 u a w := by
  unfold oddCompactProductCGrade17 oddCompactProductDGrade17 oddCompactProductEGrade17 oddCompactScalarDetGrade17 oddCompactScalarDetPart29Grade17 oddCompactScalarDetPart30Grade17
  ring

/-- Drift degree 18 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade18_eq (u a w : ℝ) :
    oddCompactProductEGrade18 u a w - oddCompactProductDGrade18 u a w + oddCompactProductCGrade18 u a w =
      oddCompactScalarDetGrade18 u a w := by
  unfold oddCompactProductCGrade18 oddCompactProductDGrade18 oddCompactProductEGrade18 oddCompactScalarDetGrade18 oddCompactScalarDetPart30Grade18 oddCompactScalarDetPart31Grade18
  ring

/-- Drift degree 19 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade19_eq (u a w : ℝ) :
    oddCompactProductEGrade19 u a w - oddCompactProductDGrade19 u a w + oddCompactProductCGrade19 u a w =
      oddCompactScalarDetGrade19 u a w := by
  unfold oddCompactProductCGrade19 oddCompactProductDGrade19 oddCompactProductEGrade19 oddCompactScalarDetGrade19 oddCompactScalarDetPart31Grade19
  ring

/-- Drift degree 20 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade20_eq (u a w : ℝ) :
    oddCompactProductEGrade20 u a w - oddCompactProductDGrade20 u a w + oddCompactProductCGrade20 u a w =
      oddCompactScalarDetGrade20 u a w := by
  unfold oddCompactProductCGrade20 oddCompactProductDGrade20 oddCompactProductEGrade20 oddCompactScalarDetGrade20 oddCompactScalarDetPart31Grade20
  ring

/-- Drift degree 21 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade21_eq (u a w : ℝ) :
    oddCompactProductEGrade21 u a w - oddCompactProductDGrade21 u a w + oddCompactProductCGrade21 u a w =
      oddCompactScalarDetGrade21 u a w := by
  unfold oddCompactProductCGrade21 oddCompactProductDGrade21 oddCompactProductEGrade21 oddCompactScalarDetGrade21 oddCompactScalarDetPart32Grade21
  ring

/-- Drift degree 22 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade22_eq (u a w : ℝ) :
    oddCompactProductEGrade22 u a w - oddCompactProductDGrade22 u a w + oddCompactProductCGrade22 u a w =
      oddCompactScalarDetGrade22 u a w := by
  unfold oddCompactProductCGrade22 oddCompactProductDGrade22 oddCompactProductEGrade22 oddCompactScalarDetGrade22 oddCompactScalarDetPart32Grade22
  ring

/-- Drift degree 23 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade23_eq (u a w : ℝ) :
    oddCompactProductEGrade23 u a w - oddCompactProductDGrade23 u a w + oddCompactProductCGrade23 u a w =
      oddCompactScalarDetGrade23 u a w := by
  unfold oddCompactProductCGrade23 oddCompactProductDGrade23 oddCompactProductEGrade23 oddCompactScalarDetGrade23 oddCompactScalarDetPart32Grade23
  ring

/-- Drift degree 24 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade24_eq (u a w : ℝ) :
    oddCompactProductEGrade24 u a w - oddCompactProductDGrade24 u a w + oddCompactProductCGrade24 u a w =
      oddCompactScalarDetGrade24 u a w := by
  unfold oddCompactProductCGrade24 oddCompactProductDGrade24 oddCompactProductEGrade24 oddCompactScalarDetGrade24 oddCompactScalarDetPart32Grade24 oddCompactScalarDetPart33Grade24
  ring

/-- Drift degree 25 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade25_eq (u a w : ℝ) :
    oddCompactProductEGrade25 u a w - oddCompactProductDGrade25 u a w + oddCompactProductCGrade25 u a w =
      oddCompactScalarDetGrade25 u a w := by
  unfold oddCompactProductCGrade25 oddCompactProductDGrade25 oddCompactProductEGrade25 oddCompactScalarDetGrade25 oddCompactScalarDetPart33Grade25
  ring

/-- Drift degree 26 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade26_eq (u a w : ℝ) :
    oddCompactProductEGrade26 u a w - oddCompactProductDGrade26 u a w + oddCompactProductCGrade26 u a w =
      oddCompactScalarDetGrade26 u a w := by
  unfold oddCompactProductCGrade26 oddCompactProductDGrade26 oddCompactProductEGrade26 oddCompactScalarDetGrade26 oddCompactScalarDetPart33Grade26
  ring

/-- Drift degree 27 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade27_eq (u a w : ℝ) :
    oddCompactProductEGrade27 u a w - oddCompactProductDGrade27 u a w + oddCompactProductCGrade27 u a w =
      oddCompactScalarDetGrade27 u a w := by
  unfold oddCompactProductCGrade27 oddCompactProductDGrade27 oddCompactProductEGrade27 oddCompactScalarDetGrade27 oddCompactScalarDetPart33Grade27
  ring

/-- Drift degree 28 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade28_eq (u a w : ℝ) :
    oddCompactProductEGrade28 u a w - oddCompactProductDGrade28 u a w + oddCompactProductCGrade28 u a w =
      oddCompactScalarDetGrade28 u a w := by
  unfold oddCompactProductCGrade28 oddCompactProductDGrade28 oddCompactProductEGrade28 oddCompactScalarDetGrade28 oddCompactScalarDetPart33Grade28
  ring

/-- Drift degree 30 of the complete determinant expansion. -/
theorem oddCompactScalarDetGrade30_eq (u a w : ℝ) :
    oddCompactProductEGrade30 u a w - oddCompactProductDGrade30 u a w + oddCompactProductCGrade30 u a w =
      oddCompactScalarDetGrade30 u a w := by
  unfold oddCompactProductCGrade30 oddCompactProductDGrade30 oddCompactProductEGrade30 oddCompactScalarDetGrade30 oddCompactScalarDetPart33Grade30
  ring

/-- The three normalized products give the complete determinant polynomial. -/
theorem oddCompactScalarDet_products (u a w : ℝ) :
    oddCompactProductE u a w - oddCompactProductD u a w + oddCompactProductC u a w =
      oddCompactScalarDet u a w := by
  rw [oddCompactScalarDet_grades]
  unfold oddCompactProductE oddCompactProductD oddCompactProductC
  linear_combination oddCompactScalarDetGrade0_eq u a w +
    oddCompactScalarDetGrade1_eq u a w +
    oddCompactScalarDetGrade2_eq u a w +
    oddCompactScalarDetGrade3_eq u a w +
    oddCompactScalarDetGrade4_eq u a w +
    oddCompactScalarDetGrade5_eq u a w +
    oddCompactScalarDetGrade6_eq u a w +
    oddCompactScalarDetGrade7_eq u a w +
    oddCompactScalarDetGrade8_eq u a w +
    oddCompactScalarDetGrade9_eq u a w +
    oddCompactScalarDetGrade10_eq u a w +
    oddCompactScalarDetGrade11_eq u a w +
    oddCompactScalarDetGrade12_eq u a w +
    oddCompactScalarDetGrade13_eq u a w +
    oddCompactScalarDetGrade14_eq u a w +
    oddCompactScalarDetGrade15_eq u a w +
    oddCompactScalarDetGrade16_eq u a w +
    oddCompactScalarDetGrade17_eq u a w +
    oddCompactScalarDetGrade18_eq u a w +
    oddCompactScalarDetGrade19_eq u a w +
    oddCompactScalarDetGrade20_eq u a w +
    oddCompactScalarDetGrade21_eq u a w +
    oddCompactScalarDetGrade22_eq u a w +
    oddCompactScalarDetGrade23_eq u a w +
    oddCompactScalarDetGrade24_eq u a w +
    oddCompactScalarDetGrade25_eq u a w +
    oddCompactScalarDetGrade26_eq u a w +
    oddCompactScalarDetGrade27_eq u a w +
    oddCompactScalarDetGrade28_eq u a w +
    oddCompactScalarDetGrade30_eq u a w

/-- Exact normalization of the complete odd determinant. -/
theorem oddCompactDet_eq_scalarPolynomial (u a w : ℝ) :
    oddCompactDet u a w = oddCompactScalarDet u a w := by
  rw [oddCompactDet_eq_reflectedScalars]
  have h (a b c d e : ℝ) :
      a*c*e-a*d^(2 : ℕ)-b^(2 : ℕ)*e+2*b*c*d-c^(3 : ℕ) = e*(a*c-b^(2 : ℕ))-d*(a*d-b*c)+c*(b*d-c^(2 : ℕ)) := by ring
  rw [h, oddCompactHeadScalar_identity, oddCompactCrossAD_eq, oddCompactCrossBD_eq,
    oddCompactProductE_eq, oddCompactProductD_eq, oddCompactProductC_eq,
    oddCompactScalarDet_products]

end
end HTGeometry
