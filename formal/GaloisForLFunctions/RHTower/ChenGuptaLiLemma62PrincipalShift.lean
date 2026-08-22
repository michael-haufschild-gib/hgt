import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalHorizontalEdges
import GaloisForLFunctions.HTGeometry.VerticalContourShift

/-!
# Chen--Gupta--Li Lemma 6.2: principal first contour displacement

The literal principal CGL integrand has one simple pole at `1 + it`.
The closed strip bounds make both horizontal sides vanish and both vertical
sides integrable, so the normalized initial and shifted vertical integrals
differ by exactly its finite Euler-product residue.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- CGL's principal `Re(s)=2` contour minus its `Re(s)=-1` contour is exactly
the finite Euler-product residue crossed at `s = 1 + it`. All analytic facts
are discharged from certified CGL data; callers provide no premises. -/
theorem cglLemma62_principal_firstShift_verticalIntegral'_sub
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) :
    VerticalIntegral' (cglLemma62PrincipalContourIntegrand w N Q t) 2 -
      VerticalIntegral' (cglLemma62PrincipalContourIntegrand w N Q t) (-1) =
      cglLemma62PrincipalResidueCoefficient w N Q t := by
  apply GaloisForLFunctions.HTGeometry.verticalIntegral'_sub_of_simple_pole
    (σ := (-1 : ℝ)) (σ' := 2) (p := cglLemma62PrincipalPole t)
  · norm_num [cglLemma62PrincipalPole]
  · norm_num [cglLemma62PrincipalPole]
  · exact cglLemma62PrincipalContourIntegrand_holomorphicOn_offPole w N Q t
  · exact cglLemma62PrincipalContourIntegrand_simplePoleBigO w N Q t
  · exact cglLemma62_principalContourIntegrand_horizontal_bottom w N Q t
  · exact cglLemma62_principalContourIntegrand_horizontal_top w N Q t
  · simpa using cglLemma62_principalContourIntegrand_left_integrable w N Q t
  · simpa using cglLemma62_principalContourIntegrand_right_integrable w N Q t

end

end RHTower
