import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62EulerBridge

/-!
# Chen--Gupta--Li Lemma 6.2: uncompleted functional-equation factor

This module converts the primitive completed-`L` functional equation into the
uncompleted left-line/right-line equality used by CGL after (6.3), then joins
it to the imprimitive finite Euler correction.
-/

open Complex

noncomputable section

namespace RHTower

/-- The full primitive functional-equation factor at the CGL left contour
point.  It is the source's `G(s-it, χ*)`, written with Mathlib's normalized
Dirichlet gamma factor. -/
def cglLemma62PrimitiveFunctionalFactor
    (P : CGLLemma62PrimitiveCharacter) (z : ℂ) : ℂ :=
  ((P.modulus.value : ℂ) ^ (1 / 2 - z) * P.character.rootNumber *
    P.character⁻¹.gammaFactor (1 - z)) / P.character.gammaFactor z

private theorem cglLemma62_gammaFactor_rightLine_ne_zero
    (P : CGLLemma62PrimitiveCharacter) (t v : ℝ) :
    P.character.gammaFactor (cglLemma62RightPoint t v) ≠ 0 := by
  rcases P.character.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    rw [cglLemma62RightPoint]
    norm_num
  · rw [hodd.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    rw [cglLemma62RightPoint]
    norm_num

private theorem cglLemma62_inverseGammaFactor_rightLine_ne_zero
    (P : CGLLemma62PrimitiveCharacter) (t v : ℝ) :
    P.character⁻¹.gammaFactor (cglLemma62RightPoint t v) ≠ 0 := by
  rcases P.character⁻¹.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    rw [cglLemma62RightPoint]
    norm_num
  · rw [hodd.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    rw [cglLemma62RightPoint]
    norm_num

/-- The primitive uncompleted Dirichlet `L` functional equation on CGL's
left/right contour pair. -/
theorem cglLemma62_primitiveLFunction_left_reflection
    (P : CGLLemma62PrimitiveCharacter) (t v : ℝ) :
    DirichletCharacter.LFunction P.character (cglLemma62LeftPoint t v) =
      cglLemma62PrimitiveFunctionalFactor P (cglLemma62LeftPoint t v) *
        DirichletCharacter.LFunction P.character⁻¹ (cglLemma62RightPoint t v) := by
  have hleft_ne : cglLemma62LeftPoint t v ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [cglLemma62LeftPoint] at hre
  have hright_eq : (1 : ℂ) - cglLemma62LeftPoint t v = cglLemma62RightPoint t v := by
    rw [cglLemma62LeftPoint, cglLemma62RightPoint]
    push_cast
    ring
  have hright_ne : cglLemma62RightPoint t v ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [cglLemma62RightPoint] at hre
  have hcompleted := cglLemma62_primitiveCompletedL_one_sub P
    (1 - cglLemma62LeftPoint t v)
  rw [show (1 : ℂ) - (1 - cglLemma62LeftPoint t v) = cglLemma62LeftPoint t v by ring,
    hright_eq] at hcompleted
  have hleft := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    P.character (cglLemma62LeftPoint t v) (Or.inl hleft_ne)
  have hright := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    P.character⁻¹ (cglLemma62RightPoint t v) (Or.inl hright_ne)
  have hcompleted_right : DirichletCharacter.completedLFunction P.character⁻¹
      (cglLemma62RightPoint t v) =
      DirichletCharacter.LFunction P.character⁻¹ (cglLemma62RightPoint t v) *
        P.character⁻¹.gammaFactor (cglLemma62RightPoint t v) := by
    rw [hright, div_mul_cancel₀ _ (cglLemma62_inverseGammaFactor_rightLine_ne_zero P t v)]
  rw [hleft, hcompleted, hcompleted_right, cglLemma62PrimitiveFunctionalFactor, hright_eq]
  have harg : cglLemma62RightPoint t v - (1 / 2 : ℂ) =
      (1 / 2 : ℂ) - cglLemma62LeftPoint t v := by
    rw [← hright_eq]
    ring
  rw [harg]
  ring

/-- **CGL (6.3), complete uncompleted reflection.**  The original ambient
character `L`-function on the shifted left contour is its reflected inverse
character `L`-function times the primitive functional and finite Euler
factors. -/
theorem cglLemma62InducedCharacter_lfunction_left_reflection
    (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    DirichletCharacter.LFunction B.character (cglLemma62LeftPoint t v) =
      cglLemma62PrimitiveFunctionalFactor B.primitive (cglLemma62LeftPoint t v) *
        cglLemma62EulerCorrection B t v *
          DirichletCharacter.LFunction B.character⁻¹ (cglLemma62RightPoint t v) := by
  rw [cglLemma62InducedCharacter_lfunction_leftFactor,
    cglLemma62_primitiveLFunction_left_reflection]
  rw [show cglLemma62PrimitiveFunctionalFactor B.primitive (cglLemma62LeftPoint t v) *
      DirichletCharacter.LFunction B.primitive.character⁻¹ (cglLemma62RightPoint t v) *
        cglLemma62EulerLeftFactor B t v =
      cglLemma62PrimitiveFunctionalFactor B.primitive (cglLemma62LeftPoint t v) *
        (cglLemma62EulerLeftFactor B t v *
          DirichletCharacter.LFunction B.primitive.character⁻¹ (cglLemma62RightPoint t v)) by
      ring]
  rw [← cglLemma62EulerCorrection_reflected_lfunction]
  ring

end RHTower
