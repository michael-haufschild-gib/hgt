import GaloisForLFunctions.RHTower.GammaEvenBoundaryParityNoGo
import GaloisForLFunctions.RHTower.GammaConductorSchurResidual
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiOrthonormal
import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments

/-!
# Exact odd Jacobi exhaustion of the Gamma parity floor

The odd Gamma sine covariance has an exact Mercer expansion in the actual odd archimedean Jacobi
modes.  Deleting the first `K` modes leaves precisely the positive series tail, which tends to zero
on every source frequency.  Choosing the least finite rank at each prime which pushes the actual
Gamma-conductor-weighted tail below `p⁻²` produces a summable all-prime residual.

Thus the even-boundary obstruction is sharp: fixed-isotypic even capacity cannot touch the odd
floor, while source-derived odd Jacobi capacity exhausts it.  No Xi character, zero divisor,
completed target sign, numerical experiment, or asymptotic estimate enters the construction.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators Nat Real

namespace RHTower

/-- Exact multiplicative factorization of the Gamma characteristic at a frequency sum. -/
theorem semilocalArchimedeanCharacteristic_add_factorization
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    semilocalArchimedeanCharacteristic (t + u) =
      semilocalArchimedeanCharacteristic t *
        semilocalArchimedeanCharacteristic u *
          (1 + Real.tanh t * Real.tanh u) ^ (-(1 : ℝ) / 2) := by
  have ht0 : 0 < Real.tanh t := tanh_pos_of_pos ht
  have hu0 : 0 < Real.tanh u := tanh_pos_of_pos hu
  have hfactor : Real.cosh (t + u) =
      (Real.cosh t * Real.cosh u) *
        (1 + Real.tanh t * Real.tanh u) := by
    rw [Real.cosh_add, Real.tanh_eq_sinh_div_cosh,
      Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos t).ne', (Real.cosh_pos u).ne']
  rw [semilocalArchimedeanCharacteristic,
    semilocalArchimedeanCharacteristic,
    semilocalArchimedeanCharacteristic, hfactor]
  rw [Real.mul_rpow
      (mul_nonneg (Real.cosh_pos t).le (Real.cosh_pos u).le)
      (by positivity : 0 ≤ 1 + Real.tanh t * Real.tanh u)]
  rw [Real.mul_rpow (Real.cosh_pos t).le (Real.cosh_pos u).le]

/-- The square of the Jacobi Fourier normalization is the normalized central-binomial
coefficient. -/
theorem semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom
    (n : ℕ) :
    semilocalArchimedeanJacobiNormalization n ^ 2 =
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom n := by
  rw [semilocalArchimedeanJacobiNormalization_sq,
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
    Nat.centralBinom_eq_two_mul_choose,
    Nat.cast_choose ℝ (show n ≤ 2 * n by omega)]
  rw [show 2 * n - n = n by omega]
  have hn : ((n ! : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [hn, hpow]
  calc
    (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
    _ = (2 : ℝ) ^ (2 * n) := by rw [← pow_mul]
    _ = (2 : ℝ) ^ (n * 2) := by congr 1; omega
  all_goals simp [pow_mul]

/-- Full central-binomial generating function in the source's Jacobi normalization. -/
theorem hasSum_semilocalArchimedeanJacobiNormalization_sq_mul_pow
    {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => semilocalArchimedeanJacobiNormalization n ^ 2 * x ^ n)
      ((1 - x) ^ (-(1 : ℝ) / 2)) := by
  have hnegNorm : ‖-x‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs]
    exact hx
  have h := GaloisForLFunctions.negHalf_rpow_hasSum (-x) hnegNorm
  have hterms : ∀ n : ℕ,
      semilocalArchimedeanJacobiNormalization n ^ 2 * x ^ n =
        Ring.choose (-1 / 2 : ℝ) n • (-x) ^ n := by
    intro n
    rw [smul_eq_mul, GaloisForLFunctions.choose_neg_half,
      semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom,
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom, neg_pow x n]
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [show
      (-1 : ℝ) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n *
          ((-1 : ℝ) ^ n * x ^ n) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          ((Nat.centralBinom n : ℝ) / 4 ^ n * x ^ n) by ring,
      hsign, one_mul]
  have h' := h.congr_fun hterms
  simpa only [sub_eq_add_neg] using h'

/-- Odd-index extraction of the Jacobi normalization series. -/
theorem hasSum_semilocalArchimedeanOddJacobiEnergy
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum
      (fun k : ℕ =>
        semilocalArchimedeanJacobiNormalization (2 * k + 1) ^ 2 *
          x ^ (2 * k + 1))
      (((1 - x) ^ (-(1 : ℝ) / 2) -
        (1 + x) ^ (-(1 : ℝ) / 2)) / 2) := by
  have hxabs : |x| < 1 := by simpa [abs_of_nonneg hx0] using hx1
  have hpos := hasSum_semilocalArchimedeanJacobiNormalization_sq_mul_pow hxabs
  have hnegAbs : |-x| < 1 := by simpa using hxabs
  have hneg := hasSum_semilocalArchimedeanJacobiNormalization_sq_mul_pow
    (x := -x) hnegAbs
  let f : ℕ → ℝ := fun n =>
    semilocalArchimedeanJacobiNormalization n ^ 2 * x ^ n
  let g : ℕ → ℝ := fun n =>
    semilocalArchimedeanJacobiNormalization n ^ 2 * (-x) ^ n
  have hfsum : Summable f := by simpa only [f] using hpos.summable
  have hgsum : Summable g := by simpa only [g] using hneg.summable
  have heven : Summable (fun k => f (2 * k)) :=
    hfsum.comp_injective (mul_right_injective₀ (by omega : (2 : ℕ) ≠ 0))
  have hodd : Summable (fun k => f (2 * k + 1)) :=
    hfsum.comp_injective (fun _ _ h => by omega)
  have geven : Summable (fun k => g (2 * k)) :=
    hgsum.comp_injective (mul_right_injective₀ (by omega : (2 : ℕ) ≠ 0))
  have godd : Summable (fun k => g (2 * k + 1)) :=
    hgsum.comp_injective (fun _ _ h => by omega)
  have hsplitPos := tsum_even_add_odd heven hodd
  have hsplitNeg := tsum_even_add_odd geven godd
  rw [hpos.tsum_eq] at hsplitPos
  rw [hneg.tsum_eq] at hsplitNeg
  have hgeven : g ∘ (fun k => 2 * k) = f ∘ (fun k => 2 * k) := by
    funext k
    simp only [Function.comp_apply, f, g]
    rw [neg_pow x (2 * k)]
    rw [show (-1 : ℝ) ^ (2 * k) = 1 by rw [pow_mul]; norm_num, one_mul]
  have hgodd : g ∘ (fun k => 2 * k + 1) =
      fun k => -(f (2 * k + 1)) := by
    funext k
    simp only [Function.comp_apply, f, g]
    rw [neg_pow x (2 * k + 1)]
    rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by
      rw [pow_add, pow_mul]
      norm_num]
    ring
  change (∑' k, (g ∘ fun k => 2 * k) k) +
      (∑' k, (g ∘ fun k => 2 * k + 1) k) = _ at hsplitNeg
  rw [hgeven, hgodd, tsum_neg] at hsplitNeg
  rw [show 1 - -x = 1 + x by ring] at hsplitNeg
  change (∑' k : ℕ, f (2 * k)) +
      -(∑' k : ℕ, f (2 * k + 1)) =
        (1 + x) ^ (-(1 : ℝ) / 2) at hsplitNeg
  have hoddValue :
      (∑' k : ℕ, f (2 * k + 1)) =
        ((1 - x) ^ (-(1 : ℝ) / 2) -
          (1 + x) ^ (-(1 : ℝ) / 2)) / 2 := by
    linarith
  have hoddSum := hodd.hasSum
  rw [hoddValue] at hoddSum
  simpa only [f] using hoddSum

/-- Actual coefficient of the `k`-th odd Gamma-Jacobi mode in a sine wave. -/
def gammaOddJacobiCoefficient (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k *
    semilocalArchimedeanJacobiNormalization (2 * k + 1) *
      semilocalArchimedeanCharacteristic t *
        Real.tanh t ^ (2 * k + 1)

/-- The closed coefficient is the literal `L²(dμΓ)` Jacobi coefficient of the sine wave. -/
theorem integral_oddJacobi_mul_sin_semilocalArchimedeanGammaMeasure
    (k : ℕ) (t : ℝ) :
    (∫ s : ℝ,
      (semilocalArchimedeanJacobiPolynomial (2 * k + 1)).eval s *
        Real.sin (t * s) ∂semilocalArchimedeanGammaMeasure) =
      gammaOddJacobiCoefficient k t := by
  have hint := integrable_semilocalArchimedeanPolynomialFourier_integrand
    (semilocalArchimedeanJacobiPolynomial (2 * k + 1)) t
  have hclosed := semilocalArchimedeanJacobiFourier_eq_closedForm (2 * k + 1) t
  have him := congrArg Complex.im hclosed
  rw [semilocalArchimedeanJacobiFourier,
    semilocalArchimedeanPolynomialFourier] at him
  rw [semilocalArchimedeanJacobiFourierClosedForm] at him
  have hIpow : Complex.I ^ (2 * k + 1) = (-1 : ℝ) ^ k * Complex.I := by
    rw [pow_add, pow_mul, Complex.I_sq, pow_one]
    norm_cast
  rw [hIpow] at him
  have himLeft :
      (∫ s : ℝ,
        (semilocalArchimedeanJacobiPolynomial (2 * k + 1)).eval s *
          Real.sin (t * s) ∂semilocalArchimedeanGammaMeasure) =
      (∫ s : ℝ,
        (((semilocalArchimedeanJacobiPolynomial (2 * k + 1)).eval s : ℝ) : ℂ) *
          Complex.exp ((((t * s : ℝ) : ℂ) * Complex.I))
            ∂semilocalArchimedeanGammaMeasure).im := by
    calc
      (∫ s : ℝ,
          (semilocalArchimedeanJacobiPolynomial (2 * k + 1)).eval s *
            Real.sin (t * s) ∂semilocalArchimedeanGammaMeasure) =
          ∫ s : ℝ,
            ((((semilocalArchimedeanJacobiPolynomial (2 * k + 1)).eval s : ℝ) : ℂ) *
              Complex.exp ((((t * s : ℝ) : ℂ) * Complex.I))).im
              ∂semilocalArchimedeanGammaMeasure := by
        apply integral_congr_ae
        filter_upwards with s
        rw [mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im]
      _ = _ := integral_im hint
  have himRight :
      ((((-1 : ℝ) ^ k : ℂ) * Complex.I *
          (semilocalArchimedeanJacobiNormalization (2 * k + 1) : ℂ) *
          (semilocalArchimedeanCharacteristic t : ℂ) *
          (Real.tanh t : ℂ) ^ (2 * k + 1))).im =
        (-1 : ℝ) ^ k *
          semilocalArchimedeanJacobiNormalization (2 * k + 1) *
          semilocalArchimedeanCharacteristic t *
          Real.tanh t ^ (2 * k + 1) := by
    have heq :
        (((-1 : ℝ) ^ k : ℂ) * Complex.I *
            (semilocalArchimedeanJacobiNormalization (2 * k + 1) : ℂ) *
            (semilocalArchimedeanCharacteristic t : ℂ) *
            (Real.tanh t : ℂ) ^ (2 * k + 1)) =
          ((((-1 : ℝ) ^ k *
            semilocalArchimedeanJacobiNormalization (2 * k + 1) *
            semilocalArchimedeanCharacteristic t *
            Real.tanh t ^ (2 * k + 1) : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [heq, mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero]
  rw [himRight] at him
  exact himLeft.trans (by simpa [gammaOddJacobiCoefficient] using him)

/-- **Exact odd Gamma-Jacobi Mercer law.**  The full protected sine covariance is exhausted by
the actual odd Jacobi ladder. -/
theorem hasSum_gammaOddJacobiCoefficient_mul
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    HasSum (fun k : ℕ =>
      gammaOddJacobiCoefficient k t * gammaOddJacobiCoefficient k u)
      (gammaOddCovarianceKernel t u) := by
  have htanh0 : 0 < Real.tanh t := tanh_pos_of_pos ht
  have hutanh0 : 0 < Real.tanh u := tanh_pos_of_pos hu
  have hx0 : 0 ≤ Real.tanh t * Real.tanh u := (mul_pos htanh0 hutanh0).le
  have hx1 : Real.tanh t * Real.tanh u < 1 := by
    calc
      Real.tanh t * Real.tanh u < Real.tanh t * 1 :=
        mul_lt_mul_of_pos_left (Real.tanh_lt_one u) htanh0
      _ < 1 := by simpa using Real.tanh_lt_one t
  have hsum := hasSum_semilocalArchimedeanOddJacobiEnergy hx0 hx1
  have hscaled := hsum.mul_left
    (semilocalArchimedeanCharacteristic t *
      semilocalArchimedeanCharacteristic u)
  have hterms : (fun k : ℕ =>
      gammaOddJacobiCoefficient k t * gammaOddJacobiCoefficient k u) =
      fun k : ℕ =>
        (semilocalArchimedeanCharacteristic t *
          semilocalArchimedeanCharacteristic u) *
        (semilocalArchimedeanJacobiNormalization (2 * k + 1) ^ 2 *
          (Real.tanh t * Real.tanh u) ^ (2 * k + 1)) := by
    funext k
    unfold gammaOddJacobiCoefficient
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [show
      ((-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k + 1) *
          semilocalArchimedeanCharacteristic t * Real.tanh t ^ (2 * k + 1)) *
        ((-1 : ℝ) ^ k * semilocalArchimedeanJacobiNormalization (2 * k + 1) *
          semilocalArchimedeanCharacteristic u * Real.tanh u ^ (2 * k + 1)) =
        (semilocalArchimedeanCharacteristic t * semilocalArchimedeanCharacteristic u) *
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          (semilocalArchimedeanJacobiNormalization (2 * k + 1) ^ 2 *
            (Real.tanh t * Real.tanh u) ^ (2 * k + 1)) by ring,
      hsign, mul_one]
  rw [hterms]
  convert! hscaled using 1
  rw [gammaOddCovarianceKernel,
    semilocalArchimedeanCharacteristic_sub_factorization ht hu,
    semilocalArchimedeanCharacteristic_add_factorization ht hu]
  ring

/-- Residual sine Gram after eliminating the first `K` actual odd Jacobi modes. -/
def gammaOddJacobiResidualKernel (K : ℕ) (t u : ℝ) : ℝ :=
  gammaOddCovarianceKernel t u -
    ∑ k ∈ Finset.range K,
      gammaOddJacobiCoefficient k t * gammaOddJacobiCoefficient k u

/-- Finite odd capacity leaves exactly the unspent Mercer tail. -/
theorem gammaOddJacobiResidualKernel_eq_tail
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (K : ℕ) :
    gammaOddJacobiResidualKernel K t u =
      ∑' k : ℕ,
        gammaOddJacobiCoefficient (k + K) t *
          gammaOddJacobiCoefficient (k + K) u := by
  have hsum := hasSum_gammaOddJacobiCoefficient_mul ht hu
  have hsplit := hsum.summable.sum_add_tsum_nat_add K
  rw [hsum.tsum_eq] at hsplit
  unfold gammaOddJacobiResidualKernel
  linarith

theorem gammaOddJacobiResidualKernel_self_nonneg
    {t : ℝ} (ht : 0 < t) (K : ℕ) :
    0 ≤ gammaOddJacobiResidualKernel K t t := by
  rw [gammaOddJacobiResidualKernel_eq_tail ht ht]
  apply tsum_nonneg
  intro k
  exact mul_self_nonneg _

/-- Odd Jacobi capacity exhausts the protected diagonal at every positive source frequency. -/
theorem tendsto_gammaOddJacobiResidualKernel_self
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun K => gammaOddJacobiResidualKernel K t t)
      atTop (nhds 0) := by
  have htail := tendsto_sum_nat_add
    (fun k : ℕ => gammaOddJacobiCoefficient k t ^ 2)
  refine htail.congr' ?_
  filter_upwards with K
  rw [gammaOddJacobiResidualKernel_eq_tail ht ht]
  apply tsum_congr
  intro k
  ring

theorem exists_gammaOddJacobiPrimeCapacity (p : Nat.Primes) :
    ∃ K : ℕ,
      gammaConductorPrimeSchurCost p *
          gammaOddJacobiResidualKernel K (Real.log (p : ℝ)) (Real.log (p : ℝ)) ≤
        ((p : ℝ) ^ 2)⁻¹ := by
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hlim := (tendsto_gammaOddJacobiResidualKernel_self hpLog).const_mul
    (gammaConductorPrimeSchurCost p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have htarget : 0 < ((p : ℝ) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hp0)
  have hevent : ∀ᶠ K in atTop,
      gammaConductorPrimeSchurCost p *
          gammaOddJacobiResidualKernel K (Real.log (p : ℝ)) (Real.log (p : ℝ)) <
        ((p : ℝ) ^ 2)⁻¹ :=
    (tendsto_order.1 hlim).2 _ (by simpa using htarget)
  obtain ⟨K, hK⟩ := hevent.exists
  exact ⟨K, hK.le⟩

/-- Least source rank making the actual weighted odd residual at `p` no larger than `p⁻²`. -/
def gammaOddJacobiPrimeCapacity (p : Nat.Primes) : ℕ :=
  Nat.find (exists_gammaOddJacobiPrimeCapacity p)

theorem gammaOddJacobiPrimeCapacity_spec (p : Nat.Primes) :
    gammaConductorPrimeSchurCost p *
        gammaOddJacobiResidualKernel (gammaOddJacobiPrimeCapacity p)
          (Real.log (p : ℝ)) (Real.log (p : ℝ)) ≤
      ((p : ℝ) ^ 2)⁻¹ :=
  Nat.find_spec (exists_gammaOddJacobiPrimeCapacity p)

/-- Actual weighted residual left by the least source-adaptive odd Jacobi rank. -/
def gammaOddJacobiPrimeResidualCost (p : Nat.Primes) : ℝ :=
  gammaConductorPrimeSchurCost p *
    gammaOddJacobiResidualKernel (gammaOddJacobiPrimeCapacity p)
      (Real.log (p : ℝ)) (Real.log (p : ℝ))

theorem gammaOddJacobiPrimeResidualCost_nonneg (p : Nat.Primes) :
    0 ≤ gammaOddJacobiPrimeResidualCost p := by
  unfold gammaOddJacobiPrimeResidualCost
  exact mul_nonneg (gammaConductorPrimeSchurCost_nonneg p)
    (gammaOddJacobiResidualKernel_self_nonneg
      (Real.log_pos (by exact_mod_cast p.prop.one_lt)) _)

/-- **All-prime odd-capacity saturation.**  Actual source-derived odd Jacobi capacity turns the
formerly nonsummable protected Gamma diagonal into a summable residual. -/
theorem summable_gammaOddJacobiPrimeResidualCost :
    Summable gammaOddJacobiPrimeResidualCost := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  exact Summable.of_nonneg_of_le
    gammaOddJacobiPrimeResidualCost_nonneg
    (fun p => gammaOddJacobiPrimeCapacity_spec p)
    hprime

/-- Cofinal finite-packet trace control supplied by the adaptive odd Jacobi ranks. -/
theorem sum_gammaOddJacobiPrimeResidualCost_le_tsum_inv_sq
    (F : Finset Nat.Primes) :
    ∑ p ∈ F, gammaOddJacobiPrimeResidualCost p ≤
      ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
  calc
    ∑ p ∈ F, gammaOddJacobiPrimeResidualCost p ≤
        ∑ p ∈ F, ((p : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum fun p _ => gammaOddJacobiPrimeCapacity_spec p
    _ ≤ ∑' p : Nat.Primes, ((p : ℝ) ^ 2)⁻¹ := by
      apply Summable.sum_le_tsum
      · intro p _
        positivity
      · exact (Real.summable_nat_pow_inv.mpr (by norm_num)).comp_injective
          Subtype.val_injective
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
      have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
        Real.summable_nat_pow_inv.mpr (by norm_num)
      exact tsum_comp_le_tsum_of_inj hnat (fun _ => by positivity)
        Subtype.val_injective

end RHTower
