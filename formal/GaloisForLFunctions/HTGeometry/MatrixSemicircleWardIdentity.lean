import GaloisForLFunctions.HTGeometry.FreeFockMatrixValuedSpectralLaw

/-!
# Ward identity for the full matrix Dyson equation

The imaginary part of any matrix Dyson solution satisfies the exact finite-dimensional Ward
identity.  This is the positive, noncommutative boundary equation needed by full matrix-semicircle
atom analysis; no diagonal or column-sparsity hypothesis occurs.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [Fintype K]

/-- The matrix-semicircle covariance map commutes with conjugate transpose. -/
theorem matrixSemicircleCovariance_conjTranspose
    (A : K → Matrix I I ℂ) (X : Matrix I I ℂ) :
    (matrixSemicircleCovariance A X)ᴴ =
      matrixSemicircleCovariance A Xᴴ := by
  rw [matrixSemicircleCovariance, matrixSemicircleCovariance,
    Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

/-- Full matrix Ward identity.  If `G` solves
`(zI + η(G))G = -I`, then
`Gᴴ (Im(z)I + η(Im G)) G = Im G`. -/
theorem matrixSemicircleDyson_ward
    [DecidableEq I]
    (A : K → Matrix I I ℂ) (G : Matrix I I ℂ) (z : ℂ)
    (hdyson :
      (z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A G) * G = -1) :
    Gᴴ * ((z.im : ℂ) • (1 : Matrix I I ℂ) +
        matrixSemicircleCovariance A (matrixHermitianImaginaryPart G)) * G =
      matrixHermitianImaginaryPart G := by
  let B := z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A G
  let H := matrixHermitianImaginaryPart G
  have hBG : B * G = -1 := hdyson
  have hstar : Gᴴ * Bᴴ = -1 := by
    have h := congrArg Matrix.conjTranspose hBG
    simpa [Matrix.conjTranspose_mul] using h
  have hdiff : Gᴴ * (B - Bᴴ) * G = G - Gᴴ := by
    calc
      Gᴴ * (B - Bᴴ) * G = Gᴴ * (B * G) - (Gᴴ * Bᴴ) * G := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = G - Gᴴ := by
        rw [hBG, hstar]
        simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
        abel
  have hGdiff : G - Gᴴ = (2 * Complex.I) • H := by
    ext i j
    simp only [H, matrixHermitianImaginaryPart, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul]
    have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
    ring_nf
    rw [hI]
    ring
  have hBstar : Bᴴ = star z • (1 : Matrix I I ℂ) +
      matrixSemicircleCovariance A Gᴴ := by
    simp only [B, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, matrixSemicircleCovariance_conjTranspose]
  have hzstar : z - star z = (2 * Complex.I) * (z.im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have hEtaSub : matrixSemicircleCovariance A (G - Gᴴ) =
      matrixSemicircleCovariance A G - matrixSemicircleCovariance A Gᴴ := by
    simp [matrixSemicircleCovariance, Finset.sum_sub_distrib,
      Matrix.mul_sub, Matrix.sub_mul]
  have hBdiff : B - Bᴴ =
      (2 * Complex.I) • ((z.im : ℂ) • (1 : Matrix I I ℂ) +
        matrixSemicircleCovariance A H) := by
    rw [hBstar]
    calc
      B - (star z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A Gᴴ) =
          (z - star z) • (1 : Matrix I I ℂ) +
            (matrixSemicircleCovariance A G - matrixSemicircleCovariance A Gᴴ) := by
        simp only [B]
        module
      _ = (2 * Complex.I) • ((z.im : ℂ) • (1 : Matrix I I ℂ)) +
            matrixSemicircleCovariance A (G - Gᴴ) := by
        rw [hzstar, hEtaSub]
        module
      _ = (2 * Complex.I) • ((z.im : ℂ) • (1 : Matrix I I ℂ)) +
            matrixSemicircleCovariance A ((2 * Complex.I) • H) := by rw [← hGdiff]
      _ = _ := by rw [matrixSemicircleCovariance_smul]; module
  rw [hBdiff, hGdiff, Matrix.mul_smul, Matrix.smul_mul] at hdiff
  exact (smul_right_injective (Matrix I I ℂ)
    (by norm_num [Complex.I_ne_zero] : (2 * Complex.I : ℂ) ≠ 0)) hdiff

end

end GaloisForLFunctions.HTGeometry
