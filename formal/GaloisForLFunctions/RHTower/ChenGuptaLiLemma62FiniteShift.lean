import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteIntegrability

/-!
# Chen--Gupta--Li Lemma 6.2: finite reflected contour displacement

This is CGL's pole-free movement of the finite reflected Dirichlet polynomial
from `Re(s)=-1` to `Re(s)=1/2`.  It uses the literal integrand, established
strip holomorphy, both vertical `L¹` certificates, and both horizontal limits.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The two vertical integrals of CGL's literal finite reflected integrand
are equal across its pole-free displacement strip. -/
theorem cglLemma62_finiteContour_verticalIntegral_eq
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    VerticalIntegral (cglLemma62FiniteContourIntegrand w N B t M) (1 / 2) =
      VerticalIntegral (cglLemma62FiniteContourIntegrand w N B t M) (-1) := by
  unfold VerticalIntegral
  congr 1
  apply GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (c := (-1 : ℝ)) (d := (1 / 2 : ℝ)) (by norm_num)
  · exact cglLemma62FiniteContourIntegrand_differentiableOn w N B t M
  · simpa using cglLemma62_finiteContourIntegrand_left_integrable w N B t M
  · simpa using cglLemma62_finiteContourIntegrand_right_integrable w N B t M
  · have h := (cglLemma62_finiteContourIntegrand_horizontal_bottom w N B t M).comp
      tendsto_neg_atTop_atBot
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with T
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u
    intro _
    congr 1
  · exact cglLemma62_finiteContourIntegrand_horizontal_top w N B t M

/-- The left vertical finite-contour integral is exactly CGL's reflected
finite Dirichlet polynomial on its original line. -/
theorem cglLemma62_finiteContour_leftVerticalIntegral_eq_reflectedFinite
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    VerticalIntegral (cglLemma62FiniteContourIntegrand w N B t M) (-1) =
      I • ∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M v := by
  unfold VerticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  convert cglLemma62_finiteContourIntegrand_eq_line w N B t v M using 1
  norm_num

/-- CGL's finite reflected Dirichlet polynomial moves from the reflected
left line to `Re(s)=1/2` with no residue. -/
theorem cglLemma62_reflectedFinite_verticalIntegral_eq_right
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    I • ∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M v =
      VerticalIntegral (cglLemma62FiniteContourIntegrand w N B t M) (1 / 2) := by
  calc
    I • ∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M v =
        VerticalIntegral (cglLemma62FiniteContourIntegrand w N B t M) (-1) :=
      (cglLemma62_finiteContour_leftVerticalIntegral_eq_reflectedFinite w N B t M).symm
    _ = VerticalIntegral (cglLemma62FiniteContourIntegrand w N B t M) (1 / 2) :=
      (cglLemma62_finiteContour_verticalIntegral_eq w N B t M).symm

end

end RHTower
