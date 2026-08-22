import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailIntegrability

/-!
# Chen--Gupta--Li Lemma 6.2: tail contour displacement

This is CGL's pole-free movement of the analytically continued complementary
Dirichlet tail from `Re(s)=-1` to `Re(s)=-2k`.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's continued complementary tail has equal vertical integrals on the
two sides of its pole-free tail rectangle. -/
theorem cglLemma62_tailContour_verticalIntegral_eq
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    VerticalIntegral (cglLemma62TailContourIntegrand w N B t M.value) (-1) =
      VerticalIntegral (cglLemma62TailContourIntegrand w N B t M.value)
        (-2 * (d.value : ℝ)) := by
  unfold VerticalIntegral
  congr 1
  apply GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (c := -2 * (d.value : ℝ)) (d := (-1 : ℝ))
  · have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
    linarith
  · exact cglLemma62TailContourIntegrand_differentiableOn w N B t M.value d.value
  · simpa using cglLemma62_tailContour_left_integrable w N B t M d
  · simpa using cglLemma62_tailContour_right_integrable w N B t M d
  · have h := (cglLemma62_tailContour_horizontal_bottom w N B t M d).comp
      tendsto_neg_atTop_atBot
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with T
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u
    intro _
    congr 1
  · exact cglLemma62_tailContour_horizontal_top w N B t M d

/-- The right vertical tail integral is literally CGL's reflected `m>M`
integrand on its original line. -/
theorem cglLemma62_tailContour_rightVerticalIntegral_eq_reflectedTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) :
    VerticalIntegral (cglLemma62TailContourIntegrand w N B t M.value) (-1) =
      I • ∫ v : ℝ, cglLemma62ReflectedTailIntegrand w N B t M.value v := by
  unfold VerticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  convert cglLemma62_tailContourIntegrand_eq_line w N B t v M.value using 1
  norm_num

/-- The far-left vertical tail integral is literally CGL's absolutely
convergent complementary Dirichlet tail. -/
theorem cglLemma62_tailContour_leftVerticalIntegral_eq_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    VerticalIntegral (cglLemma62TailContourIntegrand w N B t M.value)
        (-2 * (d.value : ℝ)) =
      I • ∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v := by
  unfold VerticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  convert cglLemma62_tailContourIntegrand_eq_farTail w N B t M.value d v using 1
  congr 1
  unfold cglLemma62FarLeftPoint
  push_cast
  ring

/-- CGL's reflected complementary tail moves without residue to the far-left
line where its literal complementary Dirichlet series converges absolutely. -/
theorem cglLemma62_reflectedTail_verticalIntegral_eq_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    I • ∫ v : ℝ, cglLemma62ReflectedTailIntegrand w N B t M.value v =
      I • ∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v := by
  calc
    I • ∫ v : ℝ, cglLemma62ReflectedTailIntegrand w N B t M.value v =
        VerticalIntegral (cglLemma62TailContourIntegrand w N B t M.value) (-1) :=
      (cglLemma62_tailContour_rightVerticalIntegral_eq_reflectedTail w N B t M).symm
    _ = VerticalIntegral (cglLemma62TailContourIntegrand w N B t M.value)
        (-2 * (d.value : ℝ)) :=
      cglLemma62_tailContour_verticalIntegral_eq w N B t M d
    _ = I • ∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v :=
      cglLemma62_tailContour_leftVerticalIntegral_eq_farTail w N B t M d

end

end RHTower
