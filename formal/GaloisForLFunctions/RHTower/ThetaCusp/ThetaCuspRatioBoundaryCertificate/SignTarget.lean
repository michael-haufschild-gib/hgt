import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioNonlinearBoundaryQuotient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CompactAssembly
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

theorem nonlinearBoundary_root76 {h : ℂ} (hh : h≠0) (s : ℂ) :
    (nonlinearBoundaryZ h s)^2=
      boundaryA (nonlinearBoundaryV h s) h⁻¹+
        boundaryB h⁻¹*nonlinearBoundaryZ h s := by
  apply (boundary_root_iff _ _ _).mpr
  have hm := compact_boundary_mass h (nonlinearBoundaryR h s)
    (nonlinearBoundaryT h s) hh
  rw [nonlinearBoundary_error] at hm
  simpa [nonlinearBoundaryZ,nonlinearBoundaryV,nonlinearBoundarySeed,mul_comm] using hm

theorem reducedBoundaryCore_compact76 {h : ℂ} (hh : h≠0) (s u : ℂ)
    (hv : nonlinearBoundaryV h s≠0) :
    h^6*(((6:ℂ)^24*24^9)⁻¹)*eval (basePoint h s u) reducedNonlinearBoundaryCore=
      boundaryCompactA75 h (nonlinearBoundaryR h s)+
        h*nonlinearBoundaryZ h s*boundaryCompactB75 h (nonlinearBoundaryR h s) := by
  apply mul_left_cancel₀ hv
  have hb := boundaryCompactSlope_evaluate75 hh (nonlinearBoundaryR h s)
    (nonlinearBoundaryZ h s) (nonlinearBoundary_root76 hh s)
  have hc := congrArg (eval (basePoint h s u)) nonlinearBoundaryCorePoly_factor
  simp only [nonlinearBoundaryCorePoly_eval,map_mul,nonlinearBoundaryVPoly_eval] at hc
  have hs := nonlinearBoundary_sourceSlope hh s
  change h^16*eval (basePoint (nonlinearBoundaryV h s) h⁻¹ (nonlinearBoundaryZ h s))
    ThetaRatioSquare.slope=nonlinearBoundaryCore h s at hs
  change h^22*(((6:ℂ)^24*24^9)⁻¹)*eval
    (basePoint (nonlinearBoundaryV h s) h⁻¹ (nonlinearBoundaryZ h s))
    ThetaRatioSquare.slope=nonlinearBoundaryV h s*
      (boundaryCompactA75 h (nonlinearBoundaryR h s)+
        h*nonlinearBoundaryZ h s*boundaryCompactB75 h (nonlinearBoundaryR h s)) at hb
  linear_combination hb-h^6*(((6:ℂ)^24*24^9)⁻¹)*(hs+hc)

end
end HTGeometry.ThetaRatioInfinity
