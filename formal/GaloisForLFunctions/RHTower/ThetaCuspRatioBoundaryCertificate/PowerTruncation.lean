import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.FullPowerRows

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open HTGeometry.EvenCompactBernstein

theorem boundaryFullCoefficientForm77_power_rows_truncated (A : ℕ) (x : ℕ → ℝ)
    (hA : A≤96) :
    boundaryFullCoefficientForm77 A x=
      ∑ e ∈ Finset.range (A+1),
        boundaryH77^e*degreeElevationCoefficient 96 e A*
          boundaryFullPowerRow77 e (fun q => boundaryS77^q*x q) := by
  rw [boundaryFullCoefficientForm77_power_rows]
  symm
  apply Finset.sum_subset
  · intro e he
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp he
    omega
  · intro e he hn
    have hnot : ¬e≤A := by
      intro hle
      apply hn
      apply Finset.mem_range.mpr
      omega
    simp only [degreeElevationCoefficient,hnot,if_false,mul_zero,zero_mul]

end
end HTGeometry.ThetaRatioInfinity
