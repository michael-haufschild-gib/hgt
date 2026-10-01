import GaloisForLFunctions.RHTower.SteinhausFullGaussianCompactTruncation
import GaloisForLFunctions.RHTower.SmoothAFEReflectedTruncatedGaussianTransfer
import GaloisForLFunctions.RHTower.SteinhausTruncatedGaussianChannelEnergy

open Complex
noncomputable section
namespace RHTower

/-- The scalar and node-vector coherent normalizations agree exactly. -/
theorem relativeTruncatedFullGaussianCofactorMode_eq_scalar
    {J : ℕ} (s : Fin J → ℂ) (t : ℝ) (A : ℂ) {R : ℝ} (hR : 0 < R)
    (L : ℕ) (ω : SteinhausModel.Omega) (j : Fin J) :
    relativeTruncatedFullGaussianCofactorMode s t A R L ω j =
      relativeTruncatedFullGaussianCofactorScalarMode (s j) t A R L ω := by
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  unfold relativeTruncatedFullGaussianCofactorMode relativeTruncatedFullGaussianCofactorScalarMode
  rw [show -(s j + (t : ℂ) * I) = -((t : ℂ) * I) + -s j by ring,
    Complex.cpow_add _ _ hRC]
  ring

/-- Spectral row shared by every free prime in the literal reflected channel. -/
def reflectedCompactGaussianRow (s : ℂ) (N tau : ℝ) : ℂ :=
  (Real.sqrt N : ℂ) * zetaChi (s + (tau : ℂ) * I) * (N : ℂ) ^ (s - 1)

/-- Prime amplitude retains the exact cofactor scale and both coherent phases. -/
def compactGaussianPrimeAmplitude (N p t tau : ℝ) (A : ℂ) : ℂ :=
  ((N / p : ℝ) : ℂ) * A * ((N / p : ℝ) : ℂ) ^ ((t : ℂ) * I) *
    (p : ℂ) ^ ((tau : ℂ) * I) / (Real.sqrt N : ℂ)

/-- Exact prime amplitude size, independent of both phase frequencies. -/
theorem norm_compactGaussianPrimeAmplitude {N p : ℝ} (hN : 0 < N) (hp : 0 < p)
    (t tau : ℝ) (A : ℂ) :
    ‖compactGaussianPrimeAmplitude N p t tau A‖ = (N / p) * ‖A‖ / Real.sqrt N := by
  have hR : 0 < N / p := div_pos hN hp
  simp only [compactGaussianPrimeAmplitude, norm_div, norm_mul,
    Complex.norm_of_nonneg hR.le, Complex.norm_of_nonneg (Real.sqrt_nonneg N),
    Complex.norm_cpow_eq_rpow_re_of_pos hR, Complex.norm_cpow_eq_rpow_re_of_pos hp,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, sub_self, Real.rpow_zero, mul_one]

/-- The literal reflected-primal coefficient channel factors into one common spectral
row, one exact scalar prime amplitude, and the compact normalized truncated mode. -/
theorem reflectedPrimalChannel_eq_compactGaussian_mode
    (d b tau t : ℝ) (N L p : ℕ) (hN : 0 < N) (hp : 0 < p)
    {A : ℂ} (hA : A ≠ 0) (ω : SteinhausModel.Omega) :
    steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d (tau + b) 1 N) L p ω =
      reflectedCompactGaussianRow (rightDisplacedLinePt d b) N tau *
        compactGaussianPrimeAmplitude N p t tau A *
        relativeTruncatedFullGaussianCofactorScalarMode (rightDisplacedLinePt d b) t A
          ((N : ℝ) / p) (L / p) (steinhausLogPhaseShift ω tau) := by
  let s := rightDisplacedLinePt d b
  let R : ℝ := (N : ℝ) / p
  let η := steinhausLogPhaseShift ω tau
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hR : 0 < R := div_pos hNR hpR
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hroot : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((Real.sqrt_pos.mpr hNR).ne')
  have hz : rightDisplacedLinePt d (tau + b) = s + (tau : ℂ) * I := by
    simp only [s, rightDisplacedLinePt, Complex.ofReal_add]
    ring
  have hzm : rightDisplacedLinePt d (tau + b) - 1 = (s - 1) + (tau : ℂ) * I := by
    rw [hz]
    ring
  have hf := truncatedGaussian_prime_channel_factor (fun _ : Fin 1 => s)
    hNR hpR (L / p) η (0 : Fin 1)
  have hm := normalizedTruncatedGaussianCofactorChannel_eq_mode (fun _ : Fin 1 => s)
    t hA hR (L / p) η (0 : Fin 1)
  rw [relativeTruncatedFullGaussianCofactorMode_eq_scalar _ t A hR] at hm
  rw [hm] at hf
  change (p : ℂ) ^ (s - 1) * truncatedFullGaussianCofactor s R (L / p) η =
    (N : ℂ) ^ (s - 1) * (((R : ℂ) * A * (R : ℂ) ^ ((t : ℂ) * I)) *
      relativeTruncatedFullGaussianCofactorScalarMode s t A R (L / p) η) at hf
  rw [reflectedPrimalChannel_eq_truncatedFullGaussianCofactor d b tau N L p hN hp ω,
    hzm, Complex.cpow_add _ _ hpC]
  change (zetaChi (rightDisplacedLinePt d (tau + b)) *
      ((p : ℂ) ^ (s - 1) * (p : ℂ) ^ ((tau : ℂ) * I))) *
      truncatedFullGaussianCofactor s R (L / p) η = _
  calc
    _ = (zetaChi (rightDisplacedLinePt d (tau + b)) * (p : ℂ) ^ ((tau : ℂ) * I)) *
        ((p : ℂ) ^ (s - 1) * truncatedFullGaussianCofactor s R (L / p) η) := by ring
    _ = _ := by
      rw [hf, hz]
      unfold reflectedCompactGaussianRow compactGaussianPrimeAmplitude
      change (zetaChi (s + (tau : ℂ) * I) * (p : ℂ) ^ ((tau : ℂ) * I)) *
          ((N : ℂ) ^ (s - 1) * (((R : ℂ) * A * (R : ℂ) ^ ((t : ℂ) * I)) *
            relativeTruncatedFullGaussianCofactorScalarMode s t A R (L / p) η)) =
        ((Real.sqrt (N : ℝ) : ℂ) * zetaChi (s + (tau : ℂ) * I) * (N : ℂ) ^ (s - 1)) *
          ((R : ℂ) * A * (R : ℂ) ^ ((t : ℂ) * I) * (p : ℂ) ^ ((tau : ℂ) * I) /
            (Real.sqrt (N : ℝ) : ℂ)) *
          relativeTruncatedFullGaussianCofactorScalarMode s t A R (L / p) η
      field_simp

end RHTower
