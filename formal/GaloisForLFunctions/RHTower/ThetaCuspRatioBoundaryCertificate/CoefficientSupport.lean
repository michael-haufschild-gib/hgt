import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Bernstein
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open HTGeometry.EvenCompactBernstein

theorem boundaryTermCoefficient77_zero_clock (c : ℝ) (a p j A B : ℕ)
    (ha : A<a) : boundaryTermCoefficient77 c a p j A B=0 := by
  unfold boundaryTermCoefficient77
  apply Finset.sum_eq_zero
  intro l hl
  apply Finset.sum_eq_zero
  intro m hm
  have hz : ¬a+2*l+m≤A := by omega
  simp [degreeElevationCoefficient,hz]

theorem boundaryTermCoefficient77_zero_parameter (c : ℝ) (a p j A B : ℕ)
    (hb : B<p+j) : boundaryTermCoefficient77 c a p j A B=0 := by
  unfold boundaryTermCoefficient77
  apply Finset.sum_eq_zero
  intro l hl
  apply Finset.sum_eq_zero
  intro m hm
  have hz : ¬p+j+l≤B := by omega
  simp [degreeElevationCoefficient,hz]

end
end HTGeometry.ThetaRatioInfinity
