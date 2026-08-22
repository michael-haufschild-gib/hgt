import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailAnalytic

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A positive CGL tail-contour depth.  Positivity is exactly what puts the
reflected far-line Dirichlet argument strictly inside `Re(s)>1`. -/
structure CGLLemma62TailContourDepth where
  value : ℕ
  positive : 0 < value

/-- The far left line used in CGL's `m>M` tail displacement. -/
def cglLemma62FarLeftPoint (d : CGLLemma62TailContourDepth) (v : ℝ) : ℂ :=
  (-2 * (d.value : ℝ) : ℂ) + (v : ℂ) * I

/-- The Dirichlet-series argument dual to CGL's far left contour point. -/
def cglLemma62FarRightPoint (t : ℝ) (d : CGLLemma62TailContourDepth) (v : ℝ) : ℂ :=
  1 - cglLemma62FarLeftPoint d v + (t : ℂ) * I

/-- The far-right argument comes with its closed absolute-convergence proof. -/
def cglLemma62FarRightPointAC (t : ℝ) (d : CGLLemma62TailContourDepth) (v : ℝ) :
    CGLAbsoluteConvergencePoint :=
  ⟨cglLemma62FarRightPoint t d v, by
    unfold cglLemma62FarRightPoint cglLemma62FarLeftPoint
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, zero_mul,
      add_zero]
    norm_num
    exact_mod_cast d.positive⟩

/-- CGL's literal `m>M` far-line tail integrand. -/
def cglLemma62FarTailIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (d : CGLLemma62TailContourDepth)
    (v : ℝ) : ℂ :=
  cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v) *
    (N.value : ℂ) ^ (cglLemma62FarLeftPoint d v) *
      cglLemma62PrimitiveFunctionalFactor B.primitive
        (cglLemma62FarLeftPoint d v - (t : ℂ) * I) *
        cglLemma62EulerCorrectionAt B
          (cglLemma62FarLeftPoint d v - (t : ℂ) * I) *
          cglLemma62DirichletTail B.character⁻¹ M (cglLemma62FarRightPointAC t d v)

/-- On `Re(s)=-2k`, the analytically continued CGL tail is literally its
absolutely convergent complementary Dirichlet series. -/
theorem cglLemma62_tailContourIntegrand_eq_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (d : CGLLemma62TailContourDepth)
    (v : ℝ) :
    cglLemma62TailContourIntegrand w N B t M (cglLemma62FarLeftPoint d v) =
      cglLemma62FarTailIntegrand w N B t M d v := by
  have hright : 1 - cglLemma62FarLeftPoint d v + (t : ℂ) * I =
      (cglLemma62FarRightPointAC t d v).1 := rfl
  have htail := cglLemma62_lfunction_sub_head_eq_tail B M (cglLemma62FarRightPointAC t d v)
  unfold cglLemma62TailContourIntegrand cglLemma62FarTailIntegrand
  rw [hright, htail]

end

end RHTower
