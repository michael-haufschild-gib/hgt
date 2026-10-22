import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactRawModel

namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Relative-shear determinant, retaining the Horner structure in the gap coordinate. -/
def evenCompactRelativeDet (r a v : ℝ) : ℝ :=
  (evenCompactRelativeGapGrade0 r v+a*(evenCompactRelativeGapGrade1 r v+a*(evenCompactRelativeGapGrade2 r v+a*(evenCompactRelativeGapGrade3 r v+a*(evenCompactRelativeGapGrade4 r v+a*(evenCompactRelativeGapGrade5 r v+a*(evenCompactRelativeGapGrade6 r v+a*(evenCompactRelativeGapGrade7 r v+a*(evenCompactRelativeGapGrade8 r v+a*(evenCompactRelativeGapGrade9 r v+a*(evenCompactRelativeGapGrade10 r v+a*(evenCompactRelativeGapGrade11 r v+a*(evenCompactRelativeGapGrade12 r v+a*(evenCompactRelativeGapGrade13 r v+a*(evenCompactRelativeGapGrade14 r v+a*(evenCompactRelativeGapGrade15 r v+a*(evenCompactRelativeGapGrade16 r v+a*(evenCompactRelativeGapGrade17 r v+a*(evenCompactRelativeGapGrade18 r v+a*(evenCompactRelativeGapGrade19 r v+a*(evenCompactRelativeGapGrade20 r v+a*(0 : ℝ))))))))))))))))))))))

/-- All gap-grade shear identities assemble before the gap itself is substituted. -/
theorem evenCompactRawPolynomial_relative_eq (u a v : ℝ) :
    evenCompactRawPolynomial u a (u*(1+v/4)) = evenCompactRelativeDet (u^(2 : ℕ)) a v := by
  unfold evenCompactRawPolynomial
  rw [evenCompactRawGapGrade0_relative_eq, evenCompactRawGapGrade1_relative_eq, evenCompactRawGapGrade2_relative_eq, evenCompactRawGapGrade3_relative_eq, evenCompactRawGapGrade4_relative_eq, evenCompactRawGapGrade5_relative_eq, evenCompactRawGapGrade6_relative_eq, evenCompactRawGapGrade7_relative_eq, evenCompactRawGapGrade8_relative_eq, evenCompactRawGapGrade9_relative_eq, evenCompactRawGapGrade10_relative_eq, evenCompactRawGapGrade11_relative_eq, evenCompactRawGapGrade12_relative_eq, evenCompactRawGapGrade13_relative_eq, evenCompactRawGapGrade14_relative_eq, evenCompactRawGapGrade15_relative_eq, evenCompactRawGapGrade16_relative_eq, evenCompactRawGapGrade17_relative_eq, evenCompactRawGapGrade18_relative_eq, evenCompactRawGapGrade19_relative_eq, evenCompactRawGapGrade20_relative_eq]
  unfold evenCompactRelativeDet
  ring1

end
end HTGeometry
