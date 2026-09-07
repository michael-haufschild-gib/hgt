import GaloisForLFunctions.RHTower.ThetaCuspEvenSeamJets

/-! # Exact determinant and Schur normalization at the literal theta seam -/
namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- The uncorrected determinant of the literal even four-by-four source block. -/
def thetaCuspNativeEvenFourDet (x : ℝ) : ℝ := (thetaCuspNativeEvenFourCompensated 0 x).det

/-- The literal matrix determinant equals the scalar Hankel cofactor polynomial. -/
theorem thetaCuspNativeEvenFourDet_eq (x : ℝ) :
    thetaCuspNativeEvenFourDet x =
      hankelFourDet (thetaCuspNativeReflectionJet 0 x) (-thetaCuspNativeReflectionJet 2 x)
        (thetaCuspNativeReflectionJet 4 x) (-thetaCuspNativeReflectionJet 6 x)
        (thetaCuspNativeReflectionJet 8 x) (-thetaCuspNativeReflectionJet 10 x)
        (thetaCuspNativeReflectionJet 12 x) := by
  have he : thetaCuspNativeEvenFourCompensated 0 x =
      !![thetaCuspNativeReflectionJet 0 x, -thetaCuspNativeReflectionJet 2 x,
          thetaCuspNativeReflectionJet 4 x, -thetaCuspNativeReflectionJet 6 x;
        -thetaCuspNativeReflectionJet 2 x, thetaCuspNativeReflectionJet 4 x,
          -thetaCuspNativeReflectionJet 6 x, thetaCuspNativeReflectionJet 8 x;
        thetaCuspNativeReflectionJet 4 x, -thetaCuspNativeReflectionJet 6 x,
          thetaCuspNativeReflectionJet 8 x, -thetaCuspNativeReflectionJet 10 x;
        -thetaCuspNativeReflectionJet 6 x, thetaCuspNativeReflectionJet 8 x,
          -thetaCuspNativeReflectionJet 10 x, thetaCuspNativeReflectionJet 12 x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [thetaCuspNativeEvenFourCompensated]
  rw [thetaCuspNativeEvenFourDet, he, det_hankelFour]

/-- The determinant retains exactly the actual head and Schur coordinate. -/
theorem thetaCuspNativeEvenFourDet_eq_head_mul_schur {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspNativeEvenFourDet x =
      (thetaCuspNativeEvenHead x).det*thetaCuspNativeEvenFourSchur x := by
  have h := finiteHankelMatrix_succ_det_eq_schur (thetaCuspNativeEvenHead_posDef hx)
  have he : thetaCuspNativeEvenFourCompensated 0 x =
      finiteHankelMatrix (fun k => (-1 : ℝ)^k*thetaCuspNativeReflectionJet (2*k) x) 4 := by
    ext i j
    simp [thetaCuspNativeEvenFourCompensated, finiteHankelMatrix]
  rw [thetaCuspNativeEvenFourDet, he]
  exact h

/-- The positive seam head determinant has its exact mass-normalized polynomial. -/
theorem thetaCuspNativeEvenHead_zero_det_eq_polynomial :
    (thetaCuspNativeEvenHead 0).det = thetaCuspSelfDualThetaMass^6 *
      HTGeometry.modularThetaEvenSeamHeadPolynomial (thetaCuspSelfDualModularScale^2) := by
  have h0 := thetaCuspNativeEvenMoment_zero_eq_polynomial (0 : Fin 7)
  have h1 := thetaCuspNativeEvenMoment_zero_eq_polynomial (1 : Fin 7)
  have h2 := thetaCuspNativeEvenMoment_zero_eq_polynomial (2 : Fin 7)
  have h3 := thetaCuspNativeEvenMoment_zero_eq_polynomial (3 : Fin 7)
  have h4 := thetaCuspNativeEvenMoment_zero_eq_polynomial (4 : Fin 7)
  norm_num at h0 h1 h2 h3 h4
  rw [← HTGeometry.modularThetaEvenSeamHeadPolynomial_eq]
  norm_num [thetaCuspNativeEvenHead, finiteHankelMatrix, Matrix.det_fin_three] at ⊢
  rw [h0, h2, h4]
  have he1 : thetaCuspNativeReflectionJet 2 0 =
      -thetaCuspSelfDualThetaMass^2*HTGeometry.modularThetaEvenSeamMomentPolynomial 1
        (thetaCuspSelfDualModularScale^2) := by nlinarith only [h1]
  have he3 : thetaCuspNativeReflectionJet 6 0 =
      -thetaCuspSelfDualThetaMass^2*HTGeometry.modularThetaEvenSeamMomentPolynomial 3
        (thetaCuspSelfDualModularScale^2) := by nlinarith only [h3]
  rw [he1, he3]
  ring

/-- Exact normalized even rank-four determinant, with all infinite source incidence retained. -/
theorem thetaCuspNativeEvenFourDet_zero_eq_polynomial :
    thetaCuspNativeEvenFourDet 0 = thetaCuspSelfDualThetaMass^8 *
      HTGeometry.modularThetaEvenSeamFourPolynomial (thetaCuspSelfDualModularScale^2) := by
  have hj (k : Fin 7) := thetaCuspNativeEvenMoment_zero_eq_polynomial k
  rw [thetaCuspNativeEvenFourDet_eq, ← HTGeometry.modularThetaEvenSeamFourPolynomial_eq]
  have h0 := hj 0
  have h1 := hj 1
  have h2 := hj 2
  have h3 := hj 3
  have h4 := hj 4
  have h5 := hj 5
  have h6 := hj 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  rw [h0, h1, h2, h3, h4, h5, h6]
  unfold hankelFourDet
  ring

end
end RHTower
