import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteShift

/-!
# Chen--Gupta--Li Lemma 6.2: reflected tail contour extension

The complementary Dirichlet tail is represented off CGL's initial reflected
line by the ambient inverse-character `L`-function less its finite prefix.
On the convergence half-plane this continuation is proved equal to the
literal `m>M` Dirichlet series.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's complementary reflected Dirichlet tail, analytically continued off
the initial line as the ambient `L`-function minus its exact finite prefix. -/
def cglLemma62TailContourIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    cglLemma62PrimitiveFunctionalFactor B.primitive (s - (t : ℂ) * I) *
      cglLemma62EulerCorrectionAt B (s - (t : ℂ) * I) *
        (DirichletCharacter.LFunction B.character⁻¹ (1 - s + (t : ℂ) * I) -
          cglLemma62DirichletHead B.character⁻¹ M (1 - s + (t : ℂ) * I))

/-- In CGL's absolute-convergence half-plane, the analytic tail continuation
is literally the complementary Dirichlet series. -/
theorem cglLemma62_lfunction_sub_head_eq_tail
    (B : CGLLemma62InducedCharacter) (M : ℕ) (s : CGLAbsoluteConvergencePoint) :
    DirichletCharacter.LFunction B.character⁻¹ s.1 -
        cglLemma62DirichletHead B.character⁻¹ M s.1 =
      cglLemma62DirichletTail B.character⁻¹ M s := by
  have h := cglLemma62_lseries_eq_head_add_tail B.character⁻¹ M s
  rw [← DirichletCharacter.LFunction_eq_LSeries B.character⁻¹ s.2] at h
  calc
    DirichletCharacter.LFunction B.character⁻¹ s.1 -
        cglLemma62DirichletHead B.character⁻¹ M s.1 =
      (cglLemma62DirichletHead B.character⁻¹ M s.1 +
        cglLemma62DirichletTail B.character⁻¹ M s) -
          cglLemma62DirichletHead B.character⁻¹ M s.1 := by rw [h]
    _ = cglLemma62DirichletTail B.character⁻¹ M s := by ring

/-- The off-line tail continuation restricts exactly to CGL's reflected
`m>M` integrand on `Re(s)=-1`. -/
theorem cglLemma62_tailContourIntegrand_eq_line
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t v : ℝ) (M : ℕ) :
    cglLemma62TailContourIntegrand w N B t M ((-1 : ℂ) + (v : ℂ) * I) =
      cglLemma62ReflectedTailIntegrand w N B t M v := by
  have hleft : ((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I =
      cglLemma62LeftPoint t v := by
    unfold cglLemma62LeftPoint
    push_cast
    ring
  have hright : 1 - ((-1 : ℂ) + (v : ℂ) * I) + (t : ℂ) * I =
      cglLemma62RightPoint t v := by
    unfold cglLemma62RightPoint
    push_cast
    ring
  have htail := cglLemma62_lfunction_sub_head_eq_tail B M (cglLemma62RightPointAC t v)
  unfold cglLemma62TailContourIntegrand cglLemma62ReflectedTailIntegrand
  rw [hleft, hright, cglLemma62EulerCorrectionAt_eq_line]
  exact congrArg (fun z : ℂ =>
    cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
      (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
        cglLemma62PrimitiveFunctionalFactor B.primitive (cglLemma62LeftPoint t v) *
          cglLemma62EulerCorrection B t v * z) htail

end

end RHTower
