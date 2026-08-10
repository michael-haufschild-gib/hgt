import GaloisForLFunctions.RHTower.GaussQuasiInnerBlocks

/-!
# Fourier coefficients of the shifted block

The normalized shifted block of the moving-translation estimate is

`v_n = (conj d_n)^{-1} · e_(-n) · D* B e_n`.

Its Fourier coefficients are computed here: the prime block shifts the index, the diagonal block
multiplies by the conjugate symbol, and the exponential monomial shifts the index back, so

`fourierCoeff v_n j = conj(d_(n+j)) · b̂(j) / conj(d_n)`.

That is exactly the coefficient family whose distance from `e^{-2π i j δ_n} b̂(j)` the `ℓ²`
estimate controls.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-! ## Fourier coefficients of the diagonal blocks -/

theorem fourierCoeff_gaussDiagonalBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff ((gaussDiagonalBlock hm k p u : AddCircle (1 : ℝ) → ℂ)) l
      = gaussSampleValue k p l * fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) l := by
  have hrepr : (fourierBasis (T := (1 : ℝ))).repr (gaussDiagonalBlock hm k p u)
      = GaloisForLFunctions.lpDiagonalCLM (fun i : ℤ => gaussSampleValue k p i)
          (gaussSampleValueBound_nonneg hm k p) (norm_gaussSampleValue_le hm k p)
          ((fourierBasis (T := (1 : ℝ))).repr u) := by
    rw [gaussDiagonalBlock, conjugateOperator]
    simp
  rw [← fourierBasis_repr, ← fourierBasis_repr, hrepr]
  exact GaloisForLFunctions.lpDiagonalCLM_apply _ _ _ _ _

theorem fourierCoeff_gaussDiagonalBlockStar {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff ((gaussDiagonalBlockStar hm k p u : AddCircle (1 : ℝ) → ℂ)) l
      = starRingEnd ℂ (gaussSampleValue k p l) *
        fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) l := by
  have hrepr : (fourierBasis (T := (1 : ℝ))).repr (gaussDiagonalBlockStar hm k p u)
      = GaloisForLFunctions.lpDiagonalCLM
          (fun i : ℤ => starRingEnd ℂ (gaussSampleValue k p i))
          (gaussSampleValueBound_nonneg hm k p) (norm_conj_gaussSampleValue_le hm k p)
          ((fourierBasis (T := (1 : ℝ))).repr u) := by
    rw [gaussDiagonalBlockStar, conjugateOperator]
    simp
  rw [← fourierBasis_repr, ← fourierBasis_repr, hrepr]
  exact GaloisForLFunctions.lpDiagonalCLM_apply _ _ _ _ _

/-! ## Multiplication by an exponential monomial -/

theorem norm_fourier_eq_one (n : ℤ) (z : AddCircle (1 : ℝ)) : ‖fourier n z‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- Multiplication by the `n`th exponential monomial, as an operator on `L²(ℝ/ℤ)`. -/
def fourierMulBlock (n : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MeasureTheory.lpBoundedMulCLM (fourier n).continuous.measurable zero_le_one
    (fun z => le_of_eq (norm_fourier_eq_one n z))

/-- Multiplying by an exponential monomial shifts the Fourier index. -/
theorem fourierCoeff_fourierMulBlock (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff ((fourierMulBlock n u : AddCircle (1 : ℝ) → ℂ)) l
      = fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) (l - n) := by
  have hae : (fourierMulBlock n u : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => fourier n z * (u : AddCircle (1 : ℝ) → ℂ) z :=
    MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ u
  rw [fourierCoeff_congr_ae hae l,
    GaloisForLFunctions.fourierCoeff_fourier_mul ((u : AddCircle (1 : ℝ) → ℂ)) l n]

/-! ## The normalized shifted block -/

/-- The normalized shifted block `v_n = (conj d_n)^{-1} e_(-n) D* B e_n`. -/
def gaussShiftedBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ •
    fourierMulBlock (-n)
      (gaussDiagonalBlockStar hm k p
        (gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt)
          (fourierLp 2 n)))

/-- **The coefficients of the shifted block.** -/
theorem fourierCoeff_gaussShiftedBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (n j : ℤ) :
    fourierCoeff ((gaussShiftedBlock hm k p n : AddCircle (1 : ℝ) → ℂ)) j
      = (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ *
        (starRingEnd ℂ (gaussSampleValue k p (n + j)) *
          gaussPrimeScaleFourierCoefficient (p : ℝ) j) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hsmul : ((gaussShiftedBlock hm k p n : AddCircle (1 : ℝ) → ℂ))
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ *
          ((fourierMulBlock (-n)
            (gaussDiagonalBlockStar hm k p
              (gaussPrimeScaleBlock hp (fourierLp 2 n))) : AddCircle (1 : ℝ) → ℂ) z) := by
    filter_upwards [Lp.coeFn_smul (starRingEnd ℂ (gaussSampleValue k p n))⁻¹
      (fourierMulBlock (-n)
        (gaussDiagonalBlockStar hm k p (gaussPrimeScaleBlock hp (fourierLp 2 n))))] with z hz
    rw [gaussShiftedBlock, hz, Pi.smul_apply, smul_eq_mul]
  rw [fourierCoeff_congr_ae hsmul j, GaloisForLFunctions.fourierCoeff_const_mul, fourierCoeff_fourierMulBlock,
    fourierCoeff_gaussDiagonalBlockStar, fourierCoeff_gaussPrimeScaleBlock_fourierLp hp,
    show j - -n = n + j from by ring, show n + j - n = j from by ring]

end

end RHTower
