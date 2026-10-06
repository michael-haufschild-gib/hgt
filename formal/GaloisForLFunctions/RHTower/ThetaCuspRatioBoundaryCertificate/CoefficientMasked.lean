import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.CoefficientForms
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open HTGeometry.EvenCompactBernstein

theorem boundaryTermForm77_mask (c : ℝ) (a p j A : ℕ) (x : ℕ → ℝ) :
    boundaryTermForm77 c a p j A x=
      ∑ l ∈ Finset.range (j+1), ∑ m ∈ Finset.range (l+1),
        if a+2*l+m≤A then
          (boundaryTermScalar77 c j l m*boundaryH77^(a+2*l+m)*boundaryS77^(p+j+l))*
            (((96-(a+2*l+m)).choose (A-(a+2*l+m))) : ℝ)*x (p+j+l)
        else 0 := by
  simp only [boundaryTermForm77,degreeElevationCoefficient,mul_ite,ite_mul,mul_zero,zero_mul]

end
end HTGeometry.ThetaRatioInfinity
