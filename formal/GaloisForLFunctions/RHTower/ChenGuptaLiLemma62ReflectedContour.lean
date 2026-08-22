import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62NonprincipalShift

/-!
# Chen--Gupta--Li Lemma 6.2: reflected nonprincipal contour

After the pole-free first displacement, CGL's primitive functional equation
and finite Euler correction turn the `Re(s)=-1` line into the reflected
inverse-character line.  This module closes that equality before the source
splits its absolutely convergent Dirichlet series into finite and tail terms.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- The exact reflected integrand on CGL's left first-shift line. -/
def cglLemma62ReflectedLineIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t v : ℝ) : ℂ :=
  cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
    (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      cglLemma62PrimitiveFunctionalFactor B.primitive (cglLemma62LeftPoint t v) *
        cglLemma62EulerCorrection B t v *
          DirichletCharacter.LFunction B.character⁻¹ (cglLemma62RightPoint t v)

/-- On `Re(s)=-1`, CGL's literal imprimitive integrand equals its reflected
inverse-character integrand.  All primitivity and induction data are carried
by the certified character packet. -/
theorem cglLemma62_reflected_line_pointwise
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    cglLemma62ContourIntegrand w N B t ((-1 : ℂ) + (v : ℂ) * I) =
      cglLemma62ReflectedLineIntegrand w N B t v := by
  have harg : ((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I =
      cglLemma62LeftPoint t v := by
    unfold cglLemma62LeftPoint
    push_cast
    ring
  unfold cglLemma62ContourIntegrand cglLemma62ReflectedLineIntegrand
  rw [harg, cglLemma62InducedCharacter_lfunction_left_reflection]
  ring

/-- The left vertical integral is the reflected CGL line integral. -/
theorem cglLemma62_reflected_line_verticalIntegral
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    VerticalIntegral (cglLemma62ContourIntegrand w N B t) (-1) =
      I • ∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v := by
  unfold VerticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  simpa using cglLemma62_reflected_line_pointwise w N B t v

/-- **CGL Lemma 6.2 reflection, exact nonprincipal branch.** The initial
vertical Mellin integral is the reflected inverse-character line integral,
with no caller-supplied contour or functional-equation premise. -/
theorem cglLemma62_nonprincipal_initialVerticalIntegral_eq_reflected
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    VerticalIntegral (cglLemma62ContourIntegrand w N B t) 2 =
      I • ∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v := by
  calc
    VerticalIntegral (cglLemma62ContourIntegrand w N B t) 2 =
        VerticalIntegral (cglLemma62ContourIntegrand w N B t) (-1) :=
      cglLemma62_nonprincipal_firstShift_verticalIntegral_eq w N B t
    _ = _ := cglLemma62_reflected_line_verticalIntegral w N B t

end

end RHTower
