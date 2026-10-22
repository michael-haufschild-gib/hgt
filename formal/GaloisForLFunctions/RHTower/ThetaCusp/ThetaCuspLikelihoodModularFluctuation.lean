import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodModularSeam

/-!
# Strict modular-seam fluctuation for the theta likelihood spectrum

Two exact descriptions of the normalized higher theta tail meet at the modular fixed point.
Modular reflection fixes its first tilted spectral moment through the boundary logarithmic slope
of the first theta atom.  Independently, infinite support of the positive likelihood measure makes
its order-two moment Hankel determinant strictly positive.

Their conjunction forces a strict lower bound on the second tilted moment.  The bound is lost if
either modular stationarity is removed or the spectral carrier collapses to one point, so it is
not a reformulation of either input theorem alone.
-/

namespace RHTower

noncomputable section

/-- **Strict modular-seam fluctuation law.**  At the theta modular fixed coordinate, the exact
first-atom boundary slope lies strictly inside the order-two likelihood moment cone. -/
theorem thetaCuspLikelihoodModularSeam_strictFluctuation :
    thetaCuspFirstAtomBoundaryLogSlope ^ (2 : ℕ) *
          (1 + thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 0) ^ (2 : ℕ) <
      (2 * Real.pi) ^ (2 : ℕ) *
        thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 0 *
        thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 2 := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 := by
    unfold thetaCuspLikelihoodCoordinate
    norm_num
    nlinarith [Real.pi_gt_three]
  have hdet :=
    det_thetaCuspHigherLikelihoodSpectralMoment_hankel_pos hB0 2
  have hdet' :
      0 <
        thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 0 *
          thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 2 -
        thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 1 *
          thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 1 := by
    simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two] using hdet
  have hbary := thetaCuspHigherLikelihoodSpectralMoment_seam_barycenter
  have hsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hbary
  have hpi : 0 < (2 * Real.pi) ^ (2 : ℕ) := by positivity
  have hscaled := mul_pos hpi hdet'
  nlinarith

end

end RHTower
