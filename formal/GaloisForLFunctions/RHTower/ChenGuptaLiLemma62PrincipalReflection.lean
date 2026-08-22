import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalShift
import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# Chen--Gupta--Li Lemma 6.2: principal-character reflection

On the shifted principal contour, the trivial Dirichlet `L`-function is its
finite Euler product times `ζ`.  The zeta functional equation then reflects
the literal `Re(s)=-1` line to the absolutely convergent `Re(s)=2` line.  This
module records that exact reflection, with the principal residue retained
separately by the first-shift identity.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- The shifted `L`-function argument in CGL's principal branch. -/
def cglLemma62PrincipalLeftPoint (t v : ℝ) : ℂ :=
  (-1 : ℂ) + ((v - t : ℝ) : ℂ) * I

/-- The right-line argument obtained by reflecting the principal ζ-factor. -/
def cglLemma62PrincipalRightPoint (t v : ℝ) : ℂ :=
  (2 : ℂ) + ((t - v : ℝ) : ℂ) * I

/-- The finite Euler factor of the trivial character on CGL's left line. -/
def cglLemma62PrincipalEulerLeftFactor (Q : CGLPositiveModulus) (z : ℂ) : ℂ :=
  ∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-z))

/-- The exact principal reflected CGL integrand.  Its ζ-factor is on the
absolutely convergent right line and its finite Euler factor remains on the
literal left argument. -/
def cglLemma62PrincipalReflectedLineIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t v : ℝ) : ℂ :=
  cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
    (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      cglLemma62PrincipalEulerLeftFactor Q (cglLemma62PrincipalLeftPoint t v) *
        zetaChi (cglLemma62PrincipalLeftPoint t v) *
          riemannZeta (cglLemma62PrincipalRightPoint t v)

/-- The literal principal CGL contour integrand on `Re(s)=-1` equals its
Euler-corrected ζ-reflection. -/
theorem cglLemma62_principal_reflected_line_pointwise
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t v : ℝ) :
    cglLemma62PrincipalContourIntegrand w N Q t ((-1 : ℂ) + (v : ℂ) * I) =
      cglLemma62PrincipalReflectedLineIntegrand w N Q t v := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  have harg : ((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I =
      cglLemma62PrincipalLeftPoint t v := by
    unfold cglLemma62PrincipalLeftPoint
    push_cast
    ring
  have hleft0 : cglLemma62PrincipalLeftPoint t v ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [cglLemma62PrincipalLeftPoint] at hre
  have hleft1 : cglLemma62PrincipalLeftPoint t v ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [cglLemma62PrincipalLeftPoint] at hre
    norm_num at hre
  have hright : (1 : ℂ) - cglLemma62PrincipalLeftPoint t v =
      cglLemma62PrincipalRightPoint t v := by
    unfold cglLemma62PrincipalLeftPoint cglLemma62PrincipalRightPoint
    push_cast
    ring
  have hgamma : Gammaℝ (1 - cglLemma62PrincipalLeftPoint t v) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [hright]
    simp [cglLemma62PrincipalRightPoint]
  unfold cglLemma62PrincipalContourIntegrand
  rw [harg, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hleft1]
  rw [zeta_eq_zetaChi_mul hleft0 hleft1 hgamma, hright]
  unfold cglLemma62PrincipalReflectedLineIntegrand cglLemma62PrincipalEulerLeftFactor
  ring

/-- The left principal vertical contour is its reflected ζ-line integral. -/
theorem cglLemma62_principal_left_verticalIntegral_eq_reflected
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) :
    VerticalIntegral (cglLemma62PrincipalContourIntegrand w N Q t) (-1) =
      I • ∫ v : ℝ, cglLemma62PrincipalReflectedLineIntegrand w N Q t v := by
  unfold VerticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  simpa using cglLemma62_principal_reflected_line_pointwise w N Q t v

/-- **CGL Lemma 6.2, exact principal branch.**  The initial principal contour
is its finite Euler-product residue plus the normalized reflected ζ-line.
No contour or functional-equation premise is exposed to the caller. -/
theorem cglLemma62_principal_initialVerticalIntegral'_eq_residue_add_reflected
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) :
    VerticalIntegral' (cglLemma62PrincipalContourIntegrand w N Q t) 2 =
      cglLemma62PrincipalResidueCoefficient w N Q t +
        (1 / (2 * Real.pi * I)) •
          (I • ∫ v : ℝ, cglLemma62PrincipalReflectedLineIntegrand w N Q t v) := by
  have hshift := cglLemma62_principal_firstShift_verticalIntegral'_sub w N Q t
  have hleft := cglLemma62_principal_left_verticalIntegral_eq_reflected w N Q t
  calc
    VerticalIntegral' (cglLemma62PrincipalContourIntegrand w N Q t) 2 =
        cglLemma62PrincipalResidueCoefficient w N Q t +
          VerticalIntegral' (cglLemma62PrincipalContourIntegrand w N Q t) (-1) := by
            linear_combination hshift
    _ = _ := by
      rw [VerticalIntegral', hleft]

end

end RHTower
