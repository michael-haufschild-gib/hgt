import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspNonparabolicHeight
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeSquareResidualFourierMean

/-! The original native cutoff keeps every lower-height image and is exact above height one-half. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMCuspProjection
noncomputable section

/-- The unchanged original cutoff height profile, with both Weyl coefficients retained. -/
def nativeSquareCutoffHeight (q : XiZeroCopy) (y : ℝ) : ℂ :=
  cutoff ![0,y]*principalSquare q ![0,y]

theorem nativeSquareCutoffHeight_zero (q : XiZeroCopy) (y : ℝ) (hy : y ≤ 2) :
    nativeSquareCutoffHeight q y = 0 := by
  unfold nativeSquareCutoffHeight cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by change y-2 ≤ 0; linarith)]
  simp

/-- The regrouped seed is definitionally the original source subtraction. -/
theorem squareCutoffSeed_eq_heightSeed (q : XiZeroCopy) :
    squareCutoffSeed q = cuspHeightSeed (nativeSquareCutoffHeight q) := rfl

/-- Exact row realization of the full original cutoff, with its original normalization. -/
theorem squareCutoffSeed_periodize_eq_rows (q : XiZeroCopy) (z : UpperHalfPlane) :
    periodize (squareCutoffSeed q) z =
      ∑' v : gammaSetHalf, nativeSquareCutoffHeight q (gammaSetMatrix v.1 • z).im := by
  rw [squareCutoffSeed_eq_heightSeed]
  exact periodize_cuspHeightSeed_eq_rows _ (nativeSquareCutoffHeight_zero q) z

/-- The actual native correction separates into its parabolic value and all nonparabolic rows. -/
theorem squareCutoffSeed_periodize_eq_height_add_nonparabolic (q : XiZeroCopy) (z : UpperHalfPlane) :
    periodize (squareCutoffSeed q) z = nativeSquareCutoffHeight q z.im+
      cuspNonparabolicHeightSum (nativeSquareCutoffHeight q) z := by
  rw [squareCutoffSeed_eq_heightSeed]
  exact periodize_cuspHeightSeed_eq_height_add_nonparabolic _ (nativeSquareCutoffHeight_zero q) z

/-- The globally modular source equals the literal original source at every height at least one-half. -/
theorem globalSquareResidual_eq_original_above_half (q : XiZeroCopy) (z : UpperHalfPlane)
    (hy : 1/2 ≤ z.im) : globalSquareResidual q z = squareResidual q (coordinates z) := by
  rw [globalSquareResidual_eq_periodized,squareCutoffSeed_eq_heightSeed,
    periodize_cuspHeightSeed_eq_height _ (nativeSquareCutoffHeight_zero q) z hy]
  rfl

/-- The full cutoff orbit mean has the literal original value above height one-half. -/
theorem squareCutoffStripMean_eq_original_above_half (q : XiZeroCopy) (y : ℝ) (hy : 1/2 ≤ y) :
    squareCutoffStripMean q y = nativeSquareCutoffHeight q y := by
  have hy0 : 0 < y := by linarith
  unfold squareCutoffStripMean
  have he (x : ℝ) : periodize (squareCutoffSeed q) (ofComplex (⟨x,y⟩:ℂ)) =
      nativeSquareCutoffHeight q y := by
    rw [squareCutoffSeed_eq_heightSeed]
    have him : (ofComplex (⟨x,y⟩:ℂ)).im = y := by
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      rfl
    rw [periodize_cuspHeightSeed_eq_height _ (nativeSquareCutoffHeight_zero q) _
      (by rw [him]; exact hy),him]
  simp_rw [he]
  simp

/-- The actual residual Fourier mean has no omitted orbit correction above the proved threshold. -/
theorem residualStripMean_eq_original_fourier_above_half (q : XiZeroCopy) (y : ℝ) (hy : 1/2 ≤ y) :
    residualStripMean q y = (1-cutoff ![0,y])*principalSquare q ![0,y]+
      4*(∑' N, amplitude (center q) y N^2) := by
  rw [residualStripMean_eq_fourier q (by linarith),squareCutoffStripMean_eq_original_above_half q y hy]
  unfold nativeSquareCutoffHeight principalSquare
  ring

end
end RHTower.D4BMJointSource
