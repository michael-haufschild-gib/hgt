import GaloisForLFunctions.HTGeometry.ParityProtectedSchurFloor
import GaloisForLFunctions.RHTower.GammaConductorSchurCapacity
import GaloisForLFunctions.RHTower.SoninSemilocalGammaMoments

/-!
# Gamma even-boundary parity no-go

The normalized archimedean Gamma measure has an exact odd sine covariance kernel.  Its diagonal at
every prime logarithm has a uniform positive lower bound.  Weighting by the actual one-prime Gamma
conductor Schur costs therefore gives a nonsummable, cofinally unbounded residual.

Together with `HTGeometry.parityBoundaryResidualEnergy_lower`, this eliminates every correction
family confined to the reflection-even Gamma/Jacobi sector, regardless of growing boundary
dimension.  Odd boundary channels and signed principal-relative finite parts are outside the
theorem's class.
-/

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped ENNReal BigOperators

namespace RHTower

/-- The protected odd-sector covariance of two Gamma Fourier modes. -/
def gammaOddCovarianceKernel (t u : ℝ) : ℝ :=
  (semilocalArchimedeanCharacteristic (t - u) -
    semilocalArchimedeanCharacteristic (t + u)) / 2

/-- The cosine transform of the actual normalized Gamma measure is its real characteristic. -/
theorem integral_cos_semilocalArchimedeanGammaMeasure (t : ℝ) :
    (∫ s : ℝ, Real.cos (t * s) ∂semilocalArchimedeanGammaMeasure) =
      semilocalArchimedeanCharacteristic t := by
  have hint : Integrable (fun s : ℝ =>
      Complex.exp (((t * s : ℝ) : ℂ) * Complex.I))
      semilocalArchimedeanGammaMeasure := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards with s
    rw [Complex.norm_exp]
    simp
  calc
    (∫ s : ℝ, Real.cos (t * s) ∂semilocalArchimedeanGammaMeasure) =
        ∫ s : ℝ, (Complex.exp (((t * s : ℝ) : ℂ) * Complex.I)).re
          ∂semilocalArchimedeanGammaMeasure := by
            congr 1
            funext s
            exact (Complex.exp_ofReal_mul_I_re (t * s)).symm
    _ = (∫ s : ℝ, Complex.exp (((t * s : ℝ) : ℂ) * Complex.I)
          ∂semilocalArchimedeanGammaMeasure).re := integral_re hint
    _ = semilocalArchimedeanCharacteristic t := by
      rw [integral_cexp_semilocalArchimedeanGammaMeasure]
      simp

/-- The abstract odd kernel is the literal sine Gram of the normalized Gamma measure. -/
theorem integral_sin_mul_sin_semilocalArchimedeanGammaMeasure (t u : ℝ) :
    (∫ s : ℝ, Real.sin (t * s) * Real.sin (u * s)
        ∂semilocalArchimedeanGammaMeasure) =
      gammaOddCovarianceKernel t u := by
  have h1 : Integrable (fun s : ℝ => Real.cos ((t - u) * s))
      semilocalArchimedeanGammaMeasure := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards with s
    simpa using abs_cos_le_one ((t - u) * s)
  have h2 : Integrable (fun s : ℝ => Real.cos ((t + u) * s))
      semilocalArchimedeanGammaMeasure := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards with s
    simpa using abs_cos_le_one ((t + u) * s)
  rw [show (fun s : ℝ => Real.sin (t * s) * Real.sin (u * s)) =
      fun s : ℝ => (Real.cos ((t - u) * s) - Real.cos ((t + u) * s)) / 2 by
    funext s
    rw [show (t - u) * s = t * s - u * s by ring_nf,
      show (t + u) * s = t * s + u * s by ring_nf]
    calc
      Real.sin (t * s) * Real.sin (u * s) =
          (2 * Real.sin (t * s) * Real.sin (u * s)) / 2 := by ring_nf
      _ = (Real.cos (t * s - u * s) - Real.cos (t * s + u * s)) / 2 := by
        rw [Real.two_mul_sin_mul_sin]]
  rw [integral_div, integral_sub h1 h2,
    integral_cos_semilocalArchimedeanGammaMeasure,
    integral_cos_semilocalArchimedeanGammaMeasure]
  rfl

/-- Every pair of positive frequencies has strictly positive odd Gamma covariance. -/
theorem gammaOddCovarianceKernel_pos {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    0 < gammaOddCovarianceKernel t u := by
  have hcosh : Real.cosh (t - u) < Real.cosh (t + u) := by
    rw [Real.cosh_sub, Real.cosh_add]
    nlinarith [(Real.sinh_pos_iff.mpr ht), (Real.sinh_pos_iff.mpr hu)]
  have hpow := Real.rpow_lt_rpow_of_neg (Real.cosh_pos (t - u)) hcosh
    (by norm_num : (-(1 : ℝ) / 2) < 0)
  dsimp [gammaOddCovarianceKernel, semilocalArchimedeanCharacteristic]
  linarith

/-- The odd covariance diagonal is half of the doubled-frequency characteristic deficit. -/
theorem gammaOddCovarianceKernel_self (t : ℝ) :
    gammaOddCovarianceKernel t t =
      (1 - semilocalArchimedeanCharacteristic (2 * t)) / 2 := by
  rw [gammaOddCovarianceKernel, sub_self]
  simp only [semilocalArchimedeanCharacteristic, Real.cosh_zero, Real.one_rpow]
  congr 2
  ring_nf

/-- Uniform positive odd-sector floor at all prime logarithms. -/
def gammaOddPrimeFloor : ℝ := (1 - Real.sqrt 2 / 2) / 2

lemma gammaOddPrimeFloor_pos : 0 < gammaOddPrimeFloor := by
  unfold gammaOddPrimeFloor
  have h := Real.sqrt_two_lt_three_halves
  linarith

/-- Every prime-log sine mode retains at least the same universal Gamma energy. -/
lemma gammaOddCovarianceKernel_log_prime_self_lower (p : Nat.Primes) :
    gammaOddPrimeFloor ≤
      gammaOddCovarianceKernel (Real.log (p : ℝ)) (Real.log (p : ℝ)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hprod := mul_le_mul_of_nonneg_right hp2 hinv0
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  rw [mul_inv_cancel₀ hpne] at hprod
  have hinv : (p : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hscaled : Real.sqrt 2 * (p : ℝ)⁻¹ ≤ Real.sqrt 2 / 2 := by
    calc
      Real.sqrt 2 * (p : ℝ)⁻¹ ≤ Real.sqrt 2 * ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hinv hsqrt0
      _ = Real.sqrt 2 / 2 := by ring_nf
  have hchar :=
    semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg
      (Real.log (p : ℝ))
  rw [Real.exp_neg, Real.exp_log hp0] at hchar
  rw [gammaOddCovarianceKernel_self]
  unfold gammaOddPrimeFloor
  linarith

/-- Actual prime Schur weight times its parity-protected Gamma diagonal. -/
def gammaEvenBoundaryPrimeResidualCost (p : Nat.Primes) : ℝ :=
  gammaConductorPrimeSchurCost p *
    gammaOddCovarianceKernel (Real.log (p : ℝ)) (Real.log (p : ℝ))

lemma gammaEvenBoundaryPrimeResidualCost_nonneg (p : Nat.Primes) :
    0 ≤ gammaEvenBoundaryPrimeResidualCost p := by
  unfold gammaEvenBoundaryPrimeResidualCost
  exact mul_nonneg (gammaConductorPrimeSchurCost_nonneg p)
    (le_trans gammaOddPrimeFloor_pos.le
      (gammaOddCovarianceKernel_log_prime_self_lower p))

/-- The protected source residual dominates a fixed positive multiple of the original Schur cost. -/
lemma gammaEvenBoundaryPrimeResidualCost_lower (p : Nat.Primes) :
    gammaOddPrimeFloor * gammaConductorPrimeSchurCost p ≤
      gammaEvenBoundaryPrimeResidualCost p := by
  unfold gammaEvenBoundaryPrimeResidualCost
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (gammaOddCovarianceKernel_log_prime_self_lower p)
    (gammaConductorPrimeSchurCost_nonneg p)

/-- **Even-boundary source no-go.**  The Schur-cost-weighted odd Gamma residual is not summable
over the primes.  Increasing reflection-even boundary capacity cannot alter this series. -/
theorem not_summable_gammaEvenBoundaryPrimeResidualCost :
    ¬ Summable gammaEvenBoundaryPrimeResidualCost := by
  intro hsum
  have hscaled : Summable
      (fun p : Nat.Primes => gammaOddPrimeFloor * gammaConductorPrimeSchurCost p) := by
    apply Summable.of_nonneg_of_le
    · intro p
      exact mul_nonneg gammaOddPrimeFloor_pos.le
        (gammaConductorPrimeSchurCost_nonneg p)
    · exact gammaEvenBoundaryPrimeResidualCost_lower
    · exact hsum
  have hcost : Summable gammaConductorPrimeSchurCost :=
    (summable_mul_left_iff gammaOddPrimeFloor_pos.ne').mp hscaled
  exact not_summable_gammaConductorPrimeSchurCost hcost

/-- Cofinal form: every proposed finite even-boundary residual budget is exceeded by some finite
prime packet. -/
theorem exists_finset_gammaEvenBoundaryPrimeResidualCost_gt (M : ℝ) :
    ∃ F : Finset Nat.Primes, M < ∑ p ∈ F, gammaEvenBoundaryPrimeResidualCost p := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply not_summable_gammaEvenBoundaryPrimeResidualCost
  exact summable_of_sum_le gammaEvenBoundaryPrimeResidualCost_nonneg h

end RHTower
