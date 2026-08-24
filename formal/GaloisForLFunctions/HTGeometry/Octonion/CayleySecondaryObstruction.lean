import GaloisForLFunctions.HTGeometry.Octonion.CayleyShadowConfluence
import GaloisForLFunctions.HTGeometry.TateFractureObstructionBianchiAmplitudeLaw

/-!
# Cayley shadow as a secondary obstruction

A transverse real grade can be invisible to the first Maurer--Cartan obstruction while surviving
in the next obstruction.  The same grade is detected independently by failure of the two Cayley
parenthesizations in the octonions.  Thus the eight-dimensional associator is not an extra copy
of a quadratic detector: it is a faithful coordinate for the first higher obstruction missed by
the quadratic shadow.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- Two-step filtered twist whose first component is nilpotent and whose second component carries
the transverse Cayley grade. -/
def cayleyGradeTwist (grade : ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 1 => !![0, 1; 0, 0]
  | 2 => !![0, 0; grade, 0]
  | _ => 0

/-- Every transverse grade is invisible to the first, quadratic obstruction. -/
theorem cayleyGradeTwist_obstruction_two (grade : ℝ) :
    twistedObstruction (cayleyGradeTwist grade) 2 = 0 := by
  rw [twistedObstruction_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyGradeTwist, Matrix.mul_apply, Fin.sum_univ_two]

/-- The secondary obstruction is exactly the transverse grade on both diagonal entries. -/
theorem cayleyGradeTwist_obstruction_three (grade : ℝ) :
    twistedObstruction (cayleyGradeTwist grade) 3 =
      !![grade, 0; 0, grade] := by
  rw [twistedObstruction_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyGradeTwist]

/-- Secondary coherence sees precisely the grade erased by the quadratic shadow. -/
theorem cayleyGradeTwist_obstruction_three_eq_zero_iff (grade : ℝ) :
    twistedObstruction (cayleyGradeTwist grade) 3 = 0 ↔ grade = 0 := by
  rw [cayleyGradeTwist_obstruction_three]
  constructor
  · intro h
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
    simpa using h00
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Octonionic schedule confluence and vanishing of the first surviving higher obstruction are
two faithful realizations of the same transverse grade. -/
theorem cayleyParenthesizations_confluent_iff_secondaryObstruction_zero
    (phase grade : ℝ) :
    ((cayleyFrameI * cayleyFrameJ) * cayleyTiltedThirdDirection phase grade =
        cayleyFrameI * (cayleyFrameJ * cayleyTiltedThirdDirection phase grade)) ↔
      twistedObstruction (cayleyGradeTwist grade) 3 = 0 := by
  rw [cayleyTiltedParenthesizations_confluent_iff,
    cayleyGradeTwist_obstruction_three_eq_zero_iff]

/-- A nonzero transverse grade is a genuine higher fracture: every quadratic test closes, while
both the secondary Maurer--Cartan obstruction and the octonionic schedule defect survive. -/
theorem cayleyHigherShadow_fracture (phase grade : ℝ) (hgrade : grade ≠ 0) :
    twistedObstruction (cayleyGradeTwist grade) 2 = 0 ∧
      twistedObstruction (cayleyGradeTwist grade) 3 ≠ 0 ∧
      (cayleyFrameI * cayleyFrameJ) * cayleyTiltedThirdDirection phase grade ≠
        cayleyFrameI * (cayleyFrameJ * cayleyTiltedThirdDirection phase grade) := by
  refine ⟨cayleyGradeTwist_obstruction_two grade, ?_, ?_⟩
  · exact (not_congr (cayleyGradeTwist_obstruction_three_eq_zero_iff grade)).2 hgrade
  · exact (not_congr (cayleyTiltedParenthesizations_confluent_iff phase grade)).2 hgrade

end

end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
