import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.CoefficientMasked
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open HTGeometry.EvenCompactBernstein

def boundaryClockEndpointForm77 (c : ℝ) (a p j : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (j+1),
    c*boundaryH77^a*boundaryS77^(p+j)*
      ((7/72*boundaryH77^3*boundaryS77+(-1/12)*boundaryH77^2*boundaryS77)^l*
        (j.choose l:ℝ))*x (p+j+l)

theorem boundaryTermForm77_clock_endpoint (c : ℝ) (a p j : ℕ) (x : ℕ → ℝ)
    (ha : a+3*j≤96) :
    boundaryTermForm77 c a p j 96 x=boundaryClockEndpointForm77 c a p j x := by
  symm
  unfold boundaryClockEndpointForm77 boundaryTermForm77
  apply Finset.sum_congr rfl
  intro l hl
  have hlj : l≤j := by have := Finset.mem_range.mp hl; omega
  rw [add_pow]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hml : m≤l := by have := Finset.mem_range.mp hm; omega
  have he : a+2*l+m≤96 := by omega
  have hc : degreeElevationCoefficient 96 (a+2*l+m) 96=1 := by
    simp [degreeElevationCoefficient,he]
  have hh : boundaryH77^(a+2*l+m)=
      boundaryH77^a*(boundaryH77^3)^m*(boundaryH77^2)^(l-m) := by
    rw [←pow_mul,←pow_mul,←pow_add,←pow_add]
    congr 1
    omega
  have hs : boundaryS77^(p+j+l)=boundaryS77^(p+j)*boundaryS77^m*boundaryS77^(l-m) := by
    rw [←pow_add,←pow_add]
    congr 1
    omega
  rw [hc,hh,hs]
  simp only [mul_pow,boundaryTermScalar77]
  ring

end
end HTGeometry.ThetaRatioInfinity
