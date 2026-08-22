import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62HorizontalEdges

/-!
# Chen--Gupta--Li Lemma 6.2: nonprincipal first contour displacement

This closes the pole-free branch of CGL's first contour movement.  The CGL
integrand is entire for a certified induced nonprincipal character; the two
vertical edges are integrable and both finite horizontal edges vanish by the
closed fifth-order Mellin estimate.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- CGL's `Re(s)=2` nonprincipal Mellin contour equals its `Re(s)=-1`
contour.  All holomorphy, absolute-integrability, and horizontal-tail facts
are discharged from the certified CGL data; no premise is accepted from a
caller. -/
theorem cglLemma62_nonprincipal_firstShift_verticalIntegral_eq
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    VerticalIntegral (cglLemma62ContourIntegrand w N B t) 2 =
      VerticalIntegral (cglLemma62ContourIntegrand w N B t) (-1) := by
  unfold VerticalIntegral
  congr 1
  apply GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (c := (-1 : ℝ)) (d := 2) (by norm_num)
  · intro s _
    unfold cglLemma62ContourIntegrand
    have hH : DifferentiableAt ℂ (cglLemma62MellinTransform w) s :=
      (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
    have hNne : (N.value : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (N.value : ℂ) ^ z) s :=
      differentiableAt_id.const_cpow (Or.inl hNne)
    have hL : DifferentiableAt ℂ
        (fun z : ℂ => DirichletCharacter.LFunction B.character (z - (t : ℂ) * I)) s := by
      exact (DirichletCharacter.differentiable_LFunction B.nonprincipal
        (s - (t : ℂ) * I)).comp s
          (differentiableAt_id.sub (differentiableAt_const ((t : ℂ) * I)))
    change DifferentiableWithinAt ℂ
      ((cglLemma62MellinTransform w * fun z : ℂ => (N.value : ℂ) ^ z) *
        fun z : ℂ => DirichletCharacter.LFunction B.character (z - (t : ℂ) * I))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) 2) s
    exact ((hH.mul hpow).mul hL).differentiableWithinAt
  · simpa using cglLemma62_nonprincipalContourIntegrand_left_integrable w N B t
  · simpa using cglLemma62_nonprincipalContourIntegrand_right_integrable w N B t
  · exact (cglLemma62_nonprincipalContourIntegrand_horizontal_bottom w N B t).comp
      tendsto_neg_atTop_atBot
  · simpa using cglLemma62_nonprincipalContourIntegrand_horizontal_top w N B t

end

end RHTower
