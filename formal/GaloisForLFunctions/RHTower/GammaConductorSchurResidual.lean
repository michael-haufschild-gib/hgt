import GaloisForLFunctions.RHTower.GammaConductorSchurCapacity

/-!
# Strict positivity of the Gamma conductor Schur residual

The normalized Gamma cyclic measure gives a covariance kernel for Fourier modes and a cross
covariance with the centered second spectral moment.  After taking the Schur complement of that
scalar conductor coordinate, the remaining two-frequency kernel is not merely positive
semidefinite: every positive-frequency entry is strictly positive.

This prevents the canonical Gamma covariance from realizing the sign cancellation available to
an abstract positive completion.  It is a source-side architecture theorem and contains no
Riemann-hypothesis or zero-divisor premise.
-/

noncomputable section

namespace RHTower

/-- Covariance of two centered Gamma Fourier modes. -/
def gammaConductorModeCovariance (t u : ℝ) : ℝ :=
  semilocalArchimedeanCharacteristic (t - u) -
    semilocalArchimedeanCharacteristic t * semilocalArchimedeanCharacteristic u

/-- Residual after eliminating the centered second-moment conductor, whose variance is `3/2`. -/
def gammaConductorModeSchurResidual (t u : ℝ) : ℝ :=
  gammaConductorModeCovariance t u -
    semilocalArchimedeanSecondMomentCovarianceKernel t *
      semilocalArchimedeanSecondMomentCovarianceKernel u / (3 / 2)

/-- The scalar bracket controlling the Gamma Schur residual after hyperbolic factorization. -/
def gammaConductorSchurResidualBracket (x : ℝ) : ℝ :=
  (1 - x) ^ (-(1 : ℝ) / 2) - 1 - (3 / 8) * x ^ 2

lemma tanh_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos ((Real.sinh_pos_iff).2 ht) (Real.cosh_pos t)

/-- The scalar Schur-residual bracket is strictly positive on the open unit interval. -/
lemma gammaConductorSchurResidualBracket_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < gammaConductorSchurResidualBracket x := by
  have hneg : -1 ≤ -x := by linarith
  have hne : -x ≠ 0 := neg_ne_zero.mpr hx0.ne'
  have hbern := rpow_one_add_lt_one_add_mul_self hneg hne
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  have hbase : 0 < 1 - x := by linarith
  have hsqrt : 0 < (1 - x) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hbase _
  have hlinear : 0 < 1 - x / 2 := by linarith
  have hinv : (1 - x / 2)⁻¹ < ((1 - x) ^ (1 / 2 : ℝ))⁻¹ := by
    apply (inv_lt_inv₀ hlinear hsqrt).2
    convert! hbern using 1
    ring_nf
  have hlinearInv : 1 + x / 2 < (1 - x / 2)⁻¹ := by
    rw [← one_div]
    rw [lt_div_iff₀ hlinear]
    nlinarith [sq_pos_of_pos hx0]
  have hrpow : (1 - x) ^ (-(1 : ℝ) / 2) = ((1 - x) ^ (1 / 2 : ℝ))⁻¹ := by
    convert Real.rpow_neg hbase.le (1 / 2 : ℝ) using 1
    ring_nf
  rw [gammaConductorSchurResidualBracket, hrpow]
  have hlower : 1 + x / 2 < ((1 - x) ^ (1 / 2 : ℝ))⁻¹ :=
    hlinearInv.trans hinv
  nlinarith [mul_pos hx0 (sub_pos.mpr hx1)]

/-- Exact multiplicative factorization of the Gamma characteristic at a frequency difference. -/
lemma semilocalArchimedeanCharacteristic_sub_factorization
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    semilocalArchimedeanCharacteristic (t - u) =
      semilocalArchimedeanCharacteristic t *
        semilocalArchimedeanCharacteristic u *
          (1 - Real.tanh t * Real.tanh u) ^ (-(1 : ℝ) / 2) := by
  have ht0 : 0 < Real.tanh t := tanh_pos_of_pos ht
  have hu0 : 0 < Real.tanh u := tanh_pos_of_pos hu
  have ht1 : Real.tanh t < 1 := Real.tanh_lt_one t
  have hu1 : Real.tanh u < 1 := Real.tanh_lt_one u
  have hx1 : Real.tanh t * Real.tanh u < 1 := by
    calc
      Real.tanh t * Real.tanh u < Real.tanh t * 1 :=
        mul_lt_mul_of_pos_left hu1 ht0
      _ < 1 := by simpa using ht1
  have hfactor : Real.cosh (t - u) =
      (Real.cosh t * Real.cosh u) *
        (1 - Real.tanh t * Real.tanh u) := by
    rw [Real.cosh_sub, Real.tanh_eq_sinh_div_cosh,
      Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos t).ne', (Real.cosh_pos u).ne']
  rw [semilocalArchimedeanCharacteristic,
    semilocalArchimedeanCharacteristic,
    semilocalArchimedeanCharacteristic, hfactor]
  rw [Real.mul_rpow
      (mul_nonneg (Real.cosh_pos t).le (Real.cosh_pos u).le)
      (sub_nonneg.mpr hx1.le)]
  rw [Real.mul_rpow (Real.cosh_pos t).le (Real.cosh_pos u).le]

/-- Exact formula for the Gamma conductor Schur residual. -/
lemma gammaConductorModeSchurResidual_eq
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    gammaConductorModeSchurResidual t u =
      semilocalArchimedeanCharacteristic t *
        semilocalArchimedeanCharacteristic u *
          gammaConductorSchurResidualBracket
            (Real.tanh t * Real.tanh u) := by
  rw [gammaConductorModeSchurResidual, gammaConductorModeCovariance,
    semilocalArchimedeanCharacteristic_sub_factorization ht hu,
    semilocalArchimedeanSecondMomentCovarianceKernel,
    semilocalArchimedeanSecondMomentCovarianceKernel,
    gammaConductorSchurResidualBracket]
  ring

/-- **Entrywise strict Gamma coherence.**  The Schur residual left after eliminating the centered
second-moment conductor is strictly positive between every two positive frequencies. -/
theorem gammaConductorModeSchurResidual_pos
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    0 < gammaConductorModeSchurResidual t u := by
  rw [gammaConductorModeSchurResidual_eq ht hu]
  apply mul_pos
  · exact mul_pos
      (Real.rpow_pos_of_pos (Real.cosh_pos t) _)
      (Real.rpow_pos_of_pos (Real.cosh_pos u) _)
  · apply gammaConductorSchurResidualBracket_pos
    · exact mul_pos (tanh_pos_of_pos ht) (tanh_pos_of_pos hu)
    · calc
        Real.tanh t * Real.tanh u < Real.tanh t * 1 :=
          mul_lt_mul_of_pos_left (Real.tanh_lt_one u) (tanh_pos_of_pos ht)
        _ < 1 := by simpa using Real.tanh_lt_one t

end RHTower
