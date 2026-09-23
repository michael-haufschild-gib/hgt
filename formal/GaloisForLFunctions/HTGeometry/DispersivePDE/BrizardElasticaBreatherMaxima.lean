import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherSymmetry
import Mathlib.Tactic

/-!
# Global peak bounds for Brizard's breather profiles

Exact norm-square factorizations prove that both printed breather profiles attain their global
amplitude maximum at the localization center.  For the Akhmediev profile this confirms the peak
location while retaining the factor `1/sqrt 2` omitted by the prose after equation (35).
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

private theorem norm_ofReal_sub_I_mul_sq (a b : ℝ) :
    ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

private theorem norm_sqrt_two_complex : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]

noncomputable def akhmedievNumeratorSq (φ : BreatherAngle) (ξ τ : ℝ) : ℝ :=
  (Real.cosh (akhmedievOmega φ * τ) * Real.cos (2 * (φ : ℝ)) -
      Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ)) ^ (2 : ℕ) +
    (Real.sinh (akhmedievOmega φ * τ) * Real.sin (2 * (φ : ℝ))) ^ (2 : ℕ)

theorem norm_akhmedievNumerator_sq (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖akhmedievNumerator φ ξ τ‖ ^ (2 : ℕ) = akhmedievNumeratorSq φ ξ τ := by
  simpa only [akhmedievNumerator, akhmedievNumeratorSq] using
    norm_ofReal_sub_I_mul_sq
      (Real.cosh (akhmedievOmega φ * τ) * Real.cos (2 * (φ : ℝ)) -
        Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ))
      (Real.sinh (akhmedievOmega φ * τ) * Real.sin (2 * (φ : ℝ)))

theorem norm_akhmedievBreather_sq (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖akhmedievBreather φ ξ τ‖ ^ (2 : ℕ) =
      akhmedievNumeratorSq φ ξ τ / (2 * akhmedievDenominator φ ξ τ ^ (2 : ℕ)) := by
  rw [akhmedievBreather, norm_div, norm_mul, norm_neg, norm_div,
    norm_linearPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (akhmedievDenominator_pos φ ξ τ), norm_sqrt_two_complex,
    div_pow, div_pow, norm_akhmedievNumerator_sq,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem akhmediev_peak_factorization (φ : BreatherAngle) (ξ τ : ℝ) :
    (1 + 2 * Real.cos (φ : ℝ)) ^ (2 : ℕ) * akhmedievDenominator φ ξ τ ^ (2 : ℕ) -
        akhmedievNumeratorSq φ ξ τ =
      4 * Real.cos (φ : ℝ) * (1 + Real.cos (φ : ℝ)) *
        ((Real.cosh (akhmedievOmega φ * τ) -
              Real.cos (akhmedievWaveNumber φ * ξ)) *
            (Real.cosh (akhmedievOmega φ * τ) -
              Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ)) +
          Real.cos (φ : ℝ) * (1 - Real.cos (φ : ℝ)) *
            (1 - Real.cos (akhmedievWaveNumber φ * ξ) ^ (2 : ℕ))) := by
  rw [akhmedievDenominator, akhmedievNumeratorSq, Real.cos_two_mul,
    Real.sin_two_mul]
  rw [show (Real.sinh (akhmedievOmega φ * τ) *
      (2 * Real.sin (φ : ℝ) * Real.cos (φ : ℝ))) ^ (2 : ℕ) =
      4 * Real.sinh (akhmedievOmega φ * τ) ^ (2 : ℕ) * Real.sin (φ : ℝ) ^ (2 : ℕ) *
        Real.cos (φ : ℝ) ^ (2 : ℕ) by ring]
  have hsin : Real.sin (φ : ℝ) ^ (2 : ℕ) = 1 - Real.cos (φ : ℝ) ^ (2 : ℕ) := by
    nlinarith [Real.sin_sq_add_cos_sq (φ : ℝ)]
  rw [Real.sinh_sq, hsin]
  ring

theorem akhmedievNumeratorSq_le_peak (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievNumeratorSq φ ξ τ ≤
      (1 + 2 * Real.cos (φ : ℝ)) ^ (2 : ℕ) * akhmedievDenominator φ ξ τ ^ (2 : ℕ) := by
  have hcpos := breatherAngle_cos_pos φ
  have hclt := breatherAngle_cos_lt_one φ
  have hcosUpper := Real.cos_le_one (akhmedievWaveNumber φ * ξ)
  have hcosLower := Real.neg_one_le_cos (akhmedievWaveNumber φ * ξ)
  have hcosh := Real.one_le_cosh (akhmedievOmega φ * τ)
  have hfirst₁ : 0 ≤ Real.cosh (akhmedievOmega φ * τ) -
      Real.cos (akhmedievWaveNumber φ * ξ) := by linarith
  have hfirst₂ : 0 ≤ Real.cosh (akhmedievOmega φ * τ) -
      Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ) := by
    have hp : Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ) ≤ 1 := by
      by_cases hy : 0 ≤ Real.cos (akhmedievWaveNumber φ * ξ)
      · nlinarith
      · nlinarith
    linarith
  have hsquare : 0 ≤ 1 - Real.cos (akhmedievWaveNumber φ * ξ) ^ (2 : ℕ) := by
    nlinarith
  have hinside : 0 ≤
      (Real.cosh (akhmedievOmega φ * τ) -
            Real.cos (akhmedievWaveNumber φ * ξ)) *
          (Real.cosh (akhmedievOmega φ * τ) -
            Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ)) +
        Real.cos (φ : ℝ) * (1 - Real.cos (φ : ℝ)) *
          (1 - Real.cos (akhmedievWaveNumber φ * ξ) ^ (2 : ℕ)) := by
    positivity
  have hfactor := akhmediev_peak_factorization φ ξ τ
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.cos (φ : ℝ))
    (by positivity : 0 ≤ 1 + Real.cos (φ : ℝ))) hinside]

/-- Global Akhmediev peak, attained at `(ξ,τ)=(0,0)`. -/
theorem norm_akhmedievBreather_le_center (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖akhmedievBreather φ ξ τ‖ ≤ ‖akhmedievBreather φ 0 0‖ := by
  rw [norm_akhmedievBreather_center]
  have hden : 0 < 2 * akhmedievDenominator φ ξ τ ^ (2 : ℕ) :=
    mul_pos (by norm_num) (sq_pos_of_pos (akhmedievDenominator_pos φ ξ τ))
  have hsq : ‖akhmedievBreather φ ξ τ‖ ^ (2 : ℕ) ≤
      ((1 + 2 * Real.cos (φ : ℝ)) / Real.sqrt 2) ^ (2 : ℕ) := by
    rw [norm_akhmedievBreather_sq]
    apply (div_le_iff₀ hden).2
    have hpeak := akhmedievNumeratorSq_le_peak φ ξ τ
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg
    (by linarith [breatherAngle_cos_pos φ]) (Real.sqrt_nonneg 2))).mp hsq

noncomputable def maNumeratorSq (φ : MaAngle) (ξ τ : ℝ) : ℝ :=
  (Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ) -
      Real.cos (maOmega φ * τ) * Real.cosh (2 * (φ : ℝ))) ^ (2 : ℕ) +
    (Real.sin (maOmega φ * τ) * Real.sinh (2 * (φ : ℝ))) ^ (2 : ℕ)

theorem norm_maNumerator_sq (φ : MaAngle) (ξ τ : ℝ) :
    ‖maNumerator φ ξ τ‖ ^ (2 : ℕ) = maNumeratorSq φ ξ τ := by
  simpa only [maNumerator, maNumeratorSq] using
    norm_ofReal_sub_I_mul_sq
      (Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ) -
        Real.cos (maOmega φ * τ) * Real.cosh (2 * (φ : ℝ)))
      (Real.sin (maOmega φ * τ) * Real.sinh (2 * (φ : ℝ)))

theorem norm_maBreather_sq (φ : MaAngle) (ξ τ : ℝ) :
    ‖maBreather φ ξ τ‖ ^ (2 : ℕ) =
      maNumeratorSq φ ξ τ / (2 * maDenominator φ ξ τ ^ (2 : ℕ)) := by
  rw [maBreather, maCore, norm_div, norm_mul, norm_neg, norm_div,
    norm_linearPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (maDenominator_pos φ ξ τ), norm_sqrt_two_complex,
    div_pow, div_pow, norm_maNumerator_sq,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem ma_peak_factorization (φ : MaAngle) (ξ τ : ℝ) :
    (1 + 2 * Real.cosh (φ : ℝ)) ^ (2 : ℕ) * maDenominator φ ξ τ ^ (2 : ℕ) -
        maNumeratorSq φ ξ τ =
      4 * Real.cosh (φ : ℝ) * (1 + Real.cosh (φ : ℝ)) *
        ((Real.cosh (maWaveNumber φ * ξ) - 1) *
            (Real.cosh (φ : ℝ) ^ (2 : ℕ) *
                (Real.cosh (maWaveNumber φ * ξ) + 1) -
              (Real.cosh (φ : ℝ) + 1)) +
          (1 - Real.cos (maOmega φ * τ)) *
            ((Real.cosh (φ : ℝ) + 1) * Real.cosh (maWaveNumber φ * ξ) -
              (1 + Real.cos (maOmega φ * τ)))) := by
  rw [maDenominator, maNumeratorSq, Real.cosh_two_mul, Real.sinh_two_mul]
  rw [show (Real.sin (maOmega φ * τ) *
      (2 * Real.sinh (φ : ℝ) * Real.cosh (φ : ℝ))) ^ (2 : ℕ) =
      4 * Real.sin (maOmega φ * τ) ^ (2 : ℕ) * Real.sinh (φ : ℝ) ^ (2 : ℕ) *
        Real.cosh (φ : ℝ) ^ (2 : ℕ) by ring]
  have hsin : Real.sin (maOmega φ * τ) ^ (2 : ℕ) =
      1 - Real.cos (maOmega φ * τ) ^ (2 : ℕ) := by
    nlinarith [Real.sin_sq_add_cos_sq (maOmega φ * τ)]
  rw [Real.sinh_sq, hsin]
  ring

theorem maNumeratorSq_le_peak (φ : MaAngle) (ξ τ : ℝ) :
    maNumeratorSq φ ξ τ ≤
      (1 + 2 * Real.cosh (φ : ℝ)) ^ (2 : ℕ) * maDenominator φ ξ τ ^ (2 : ℕ) := by
  have hc := maAngle_one_lt_cosh φ
  have hx := Real.one_le_cosh (maWaveNumber φ * ξ)
  have hyUpper := Real.cos_le_one (maOmega φ * τ)
  have hyLower := Real.neg_one_le_cos (maOmega φ * τ)
  have hbracket₁ : 0 ≤ Real.cosh (φ : ℝ) ^ (2 : ℕ) *
      (Real.cosh (maWaveNumber φ * ξ) + 1) - (Real.cosh (φ : ℝ) + 1) := by
    nlinarith [sq_nonneg (Real.cosh (φ : ℝ) - 1),
      mul_nonneg (sq_nonneg (Real.cosh (φ : ℝ))) (by linarith :
        0 ≤ Real.cosh (maWaveNumber φ * ξ) - 1)]
  have hbracket₂ : 0 ≤ (Real.cosh (φ : ℝ) + 1) *
      Real.cosh (maWaveNumber φ * ξ) - (1 + Real.cos (maOmega φ * τ)) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.cosh (φ : ℝ) + 1)
      (by linarith : 0 ≤ Real.cosh (maWaveNumber φ * ξ) - 1)]
  have hinside : 0 ≤
      (Real.cosh (maWaveNumber φ * ξ) - 1) *
          (Real.cosh (φ : ℝ) ^ (2 : ℕ) *
              (Real.cosh (maWaveNumber φ * ξ) + 1) -
            (Real.cosh (φ : ℝ) + 1)) +
        (1 - Real.cos (maOmega φ * τ)) *
          ((Real.cosh (φ : ℝ) + 1) * Real.cosh (maWaveNumber φ * ξ) -
            (1 + Real.cos (maOmega φ * τ))) := by
    positivity
  have hfactor := ma_peak_factorization φ ξ τ
  nlinarith [mul_nonneg (mul_nonneg
    (by positivity : (0 : ℝ) ≤ 4 * Real.cosh (φ : ℝ))
    (by positivity : 0 ≤ 1 + Real.cosh (φ : ℝ))) hinside]

/-- Global Ma peak, attained at `(ξ,τ)=(0,0)`. -/
theorem norm_maBreather_le_center (φ : MaAngle) (ξ τ : ℝ) :
    ‖maBreather φ ξ τ‖ ≤ ‖maBreather φ 0 0‖ := by
  rw [norm_maBreather_center]
  have hden : 0 < 2 * maDenominator φ ξ τ ^ (2 : ℕ) :=
    mul_pos (by norm_num) (sq_pos_of_pos (maDenominator_pos φ ξ τ))
  have hsq : ‖maBreather φ ξ τ‖ ^ (2 : ℕ) ≤
      ((1 + 2 * Real.cosh (φ : ℝ)) / Real.sqrt 2) ^ (2 : ℕ) := by
    rw [norm_maBreather_sq]
    apply (div_le_iff₀ hden).2
    have hpeak := maNumeratorSq_le_peak φ ξ τ
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg
    (by linarith [Real.cosh_pos (φ : ℝ)]) (Real.sqrt_nonneg 2))).mp hsq

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
