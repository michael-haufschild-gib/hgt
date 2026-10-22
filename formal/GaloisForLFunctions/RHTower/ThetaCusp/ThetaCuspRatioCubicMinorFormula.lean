import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicMinorAssembly
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def nonlinearMinorThirdRatioNorm (r : ℂ) :
    {c : ℂ // (affineJet3 r scaledMinor+(r^2/24)*affineJet1 r (pderiv Coord.J scaledMinor)-
      (7*r^2/72)*criticalValue r (pderiv Coord.J scaledMinor))/principalMass=c} := by
  have he := congrArg (fun z : ℂ => z/principalMass) (nonlinearMinorThirdNorm r).property
  have h8j := criticalMoment8_J r
  change eval (basePoint 0 r (r/12)) (pderiv Coord.J scaledMoment8)=_ at h8j
  conv at he =>
    rhs
    norm_num [nonlinearMinorThirdNorm,Nat.rawCast,Int.rawCast,NNRat.rawCast,
      affineJet1,affineD,criticalValue,principalMass]
    rw [show r*(1/12:ℂ)=r/12 by ring,h8j]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
