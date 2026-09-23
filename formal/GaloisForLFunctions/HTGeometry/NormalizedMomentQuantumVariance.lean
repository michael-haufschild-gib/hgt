import GaloisForLFunctions.HTGeometry.VacuumFeshbachValue

/-!
# Normalized moment states and quantum variance

A moment functional with nonzero vacuum mass becomes a normalized expectation after division by
its value on `1`.  Its ordinary variance is exactly the vacuum Feshbach remainder divided by that
mass.  Consequently the pure-state quantum Fisher value attached to a moment observable is four
times this normalized variance.

These are static value identities.  They apply to every moment functional in `HTGeometry`, not
only to a zeta or Sonin specialization.

Physics provenance: for a pure state under unitary parameter encoding, quantum Fisher information
is four times the generator variance.  See S. L. Braunstein and C. M. Caves, Physical Review
Letters 72 (1994), 3439--3443, DOI 10.1103/PhysRevLett.72.3439.

Successive size-biased states are related by the likelihood ratio `X / E[X]`.  Hence the Pearson
chi-square divergence from the next size-biased state to the current one is exactly the squared
coefficient of variation `Var(X) / E[X]^(2 : ℕ)`.  Size biasing is surveyed by Arratia--Goldstein--
Kochman, Probability Surveys 16 (2019), 1--61, DOI 10.1214/13-PS221; the encompassing convex
divergence class is due to Ali--Silvey, Journal of the Royal Statistical Society B 28 (1966),
131--142, DOI 10.1111/j.2517-6161.1966.tb00626.x.  The finite-change chi-square variance bound is
the Hammersley--Chapman--Robbins bound; see Chapman--Robbins, Annals of Mathematical Statistics 22
(1951), 581--586, DOI 10.1214/aoms/1177729548.

The change of any power expectation under one further size bias is its covariance with the
weighting coordinate divided by the current mean.  This is the no-transmission term of the
Robertson--Price selection identity.  See G. R. Price, Nature 227 (1970), 520--521,
DOI 10.1038/227520a0, and Frank--Bruggeman, arXiv:2010.14544, for the common statistical-mechanics
and population interpretation.
-/

open Polynomial

namespace HTGeometry

noncomputable section

/-- Expectation in the moment state normalized by its vacuum mass. -/
def momentNormalizedExpectation (s : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  momentFunctional s p / s 0

/-- Variance of a polynomial observable in the normalized moment state. -/
def momentNormalizedVariance (s : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  momentNormalizedExpectation s (p ^ (2 : ℕ)) - momentNormalizedExpectation s p ^ (2 : ℕ)

/-- Covariance of two polynomial observables in the normalized moment state. -/
def momentNormalizedCovariance
    (s : ℕ → ℝ) (p q : Polynomial ℝ) : ℝ :=
  momentNormalizedExpectation s (p * q) -
    momentNormalizedExpectation s p * momentNormalizedExpectation s q

/-- Variance is self-covariance. -/
theorem momentNormalizedCovariance_self
    (s : ℕ → ℝ) (p : Polynomial ℝ) :
    momentNormalizedCovariance s p p = momentNormalizedVariance s p := by
  unfold momentNormalizedCovariance momentNormalizedVariance
  simp only [pow_two]

/-- Normalized covariance is symmetric. -/
theorem momentNormalizedCovariance_comm
    (s : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentNormalizedCovariance s p q = momentNormalizedCovariance s q p := by
  unfold momentNormalizedCovariance
  rw [mul_comm p q,
    mul_comm (momentNormalizedExpectation s p) (momentNormalizedExpectation s q)]

/-- The normalized moment functional has unit vacuum expectation. -/
theorem momentNormalizedExpectation_one
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) :
    momentNormalizedExpectation s (1 : Polynomial ℝ) = 1 := by
  rw [momentNormalizedExpectation, momentFunctional_one_eq]
  exact div_self h0

/-- Normalized expectation of a monomial is the corresponding moment ratio. -/
@[simp] theorem momentNormalizedExpectation_X_pow
    (s : ℕ → ℝ) (n : ℕ) :
    momentNormalizedExpectation s (X ^ n) = s n / s 0 := by
  rw [momentNormalizedExpectation, momentFunctional_X_pow]

/-- The variance of a monomial is the elementary normalized moment-ratio determinant. -/
theorem momentNormalizedVariance_X_pow
    (s : ℕ → ℝ) (n : ℕ) :
    momentNormalizedVariance s (X ^ n) =
      s (n + n) / s 0 - (s n / s 0) ^ (2 : ℕ) := by
  have hpow : (X ^ n : Polynomial ℝ) ^ (2 : ℕ) = X ^ (n + n) := by
    rw [pow_two, ← pow_add]
  rw [momentNormalizedVariance, hpow, momentNormalizedExpectation_X_pow,
    momentNormalizedExpectation_X_pow]

/-- The vacuum Feshbach remainder is the vacuum mass times normalized variance. -/
theorem momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (p : Polynomial ℝ) :
    momentVacuumFeshbachRemainder s p =
      s 0 * momentNormalizedVariance s p := by
  unfold momentVacuumFeshbachRemainder momentNormalizedVariance
    momentNormalizedExpectation
  field_simp [h0]

/-- The canonically centered representative has zero normalized expectation. -/
theorem momentNormalizedExpectation_centered
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (p : Polynomial ℝ) :
    momentNormalizedExpectation s (momentVacuumCenteredPolynomial s p) = 0 := by
  rw [momentNormalizedExpectation,
    momentFunctional_momentVacuumCenteredPolynomial s h0 p, zero_div]

/-- The normalized square of the centered representative is exactly its variance. -/
theorem momentNormalizedExpectation_centered_sq
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (p : Polynomial ℝ) :
    momentNormalizedExpectation s ((momentVacuumCenteredPolynomial s p) ^ (2 : ℕ)) =
      momentNormalizedVariance s p := by
  rw [momentNormalizedExpectation,
    momentFunctional_momentVacuumCenteredPolynomial_sq s h0 p,
    momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance s h0 p]
  field_simp [h0]

/-- Pure-state moment quantum Fisher information is exactly four times normalized variance. -/
theorem pureStateQuantumFisherValue_moment_eq_four_mul_normalizedVariance
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (p : Polynomial ℝ) :
    pureStateQuantumFisherValue (s 0)
        (momentFunctional s p) (momentFunctional s (p ^ (2 : ℕ))) =
      4 * momentNormalizedVariance s p := by
  rw [pureStateQuantumFisherValue_moment_eq s h0 p,
    momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance s h0 p]
  field_simp [h0]

/-- With positive vacuum mass, normalized variance positivity is exactly Feshbach positivity. -/
theorem momentNormalizedVariance_nonneg_iff_feshbach
    (s : ℕ → ℝ) (h0 : 0 < s 0) (p : Polynomial ℝ) :
    0 ≤ momentNormalizedVariance s p ↔
      0 ≤ momentVacuumFeshbachRemainder s p := by
  rw [momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance s h0.ne' p,
    mul_nonneg_iff_of_pos_left h0]

/-- Variance never exceeds the normalized uncentered second moment. -/
theorem momentNormalizedVariance_le_secondMoment
    (s : ℕ → ℝ) (p : Polynomial ℝ) :
    momentNormalizedVariance s p ≤
      momentNormalizedExpectation s (p ^ (2 : ℕ)) := by
  unfold momentNormalizedVariance
  exact sub_le_self _ (sq_nonneg _)

/-! ### Size-biased moment states -/

/-- The `k`-th size-biased moment state.  If `s_n = ∫ x^n dμ`, this is the moment sequence of
`x^k dμ / s_k` before normalization. -/
def momentSizeBiasedSequence (s : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun n => s (k + n)

/-- The mean of `X` in the `k`-th size-biased state is the adjacent moment ratio. -/
theorem momentNormalizedExpectation_X_sizeBiased
    (s : ℕ → ℝ) (k : ℕ) :
    momentNormalizedExpectation (momentSizeBiasedSequence s k) X =
      s (k + 1) / s k := by
  simpa [momentSizeBiasedSequence] using
    momentNormalizedExpectation_X_pow (momentSizeBiasedSequence s k) 1

/-- Every power expectation in a size-biased state is a shifted moment ratio. -/
theorem momentNormalizedExpectation_X_pow_sizeBiased
    (s : ℕ → ℝ) (k n : ℕ) :
    momentNormalizedExpectation (momentSizeBiasedSequence s k) (X ^ n) =
      s (k + n) / s k := by
  simp [momentSizeBiasedSequence]

/-- The susceptibility of `X` in the `k`-th size-biased state is the adjacent normalized
moment determinant.  In equilibrium statistical mechanics this variance is the static linear
response to a field coupled to `X`. -/
theorem momentNormalizedVariance_X_sizeBiased
    (s : ℕ → ℝ) (k : ℕ) :
    momentNormalizedVariance (momentSizeBiasedSequence s k) X =
      s (k + 2) / s k - (s (k + 1) / s k) ^ (2 : ℕ) := by
  simpa [momentSizeBiasedSequence] using
    momentNormalizedVariance_X_pow (momentSizeBiasedSequence s k) 1

/-- Denominator-free fluctuation identity for a size-biased moment state. -/
theorem sq_mass_mul_momentNormalizedVariance_X_sizeBiased
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) :
    s k ^ (2 : ℕ) *
        momentNormalizedVariance (momentSizeBiasedSequence s k) X =
      s k * s (k + 2) - s (k + 1) ^ (2 : ℕ) := by
  rw [momentNormalizedVariance_X_sizeBiased]
  field_simp [hk]

/-! ### Pearson information between successive size-biased states -/

/-- Algebraic Pearson chi-square value from the `(k+1)`-st size-biased moment state to the
`k`-th state.  For a positive representing measure, the Radon--Nikodym derivative is
`X / E_k[X]`, so this quotient is the literal Pearson chi-square divergence. -/
def momentSizeBiasPearsonChiSq (s : ℕ → ℝ) (k : ℕ) : ℝ :=
  momentNormalizedVariance (momentSizeBiasedSequence s k) X /
    momentNormalizedExpectation (momentSizeBiasedSequence s k) X ^ (2 : ℕ)

/-- The Pearson value is the susceptibility-to-squared-signal ratio. -/
theorem momentSizeBiasPearsonChiSq_eq_variance_div_mean_sq
    (s : ℕ → ℝ) (k : ℕ) :
    momentSizeBiasPearsonChiSq s k =
      momentNormalizedVariance (momentSizeBiasedSequence s k) X /
        momentNormalizedExpectation (momentSizeBiasedSequence s k) X ^ (2 : ℕ) := by
  rfl

/-- Moment-ratio formula for the Pearson information between successive size biases. -/
theorem momentSizeBiasPearsonChiSq_eq_momentRatios
    (s : ℕ → ℝ) (k : ℕ) :
    momentSizeBiasPearsonChiSq s k =
      (s (k + 2) / s k - (s (k + 1) / s k) ^ (2 : ℕ)) /
        (s (k + 1) / s k) ^ (2 : ℕ) := by
  rw [momentSizeBiasPearsonChiSq,
    momentNormalizedVariance_X_sizeBiased,
    momentNormalizedExpectation_X_sizeBiased]

/-- Denominator-free Pearson identity: its numerator is the adjacent Hankel determinant. -/
theorem sq_next_mul_momentSizeBiasPearsonChiSq
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    s (k + 1) ^ (2 : ℕ) * momentSizeBiasPearsonChiSq s k =
      s k * s (k + 2) - s (k + 1) ^ (2 : ℕ) := by
  rw [momentSizeBiasPearsonChiSq_eq_momentRatios]
  field_simp [hk, hk1]

/-- Pearson nonnegativity is exactly adjacent Hankel log-convexity when the two normalizing
moments are positive. -/
theorem momentSizeBiasPearsonChiSq_nonneg_iff_adjacentHankel
    (s : ℕ → ℝ) (k : ℕ) (hk : 0 < s k) (hk1 : 0 < s (k + 1)) :
    0 ≤ momentSizeBiasPearsonChiSq s k ↔
      s (k + 1) ^ (2 : ℕ) ≤ s k * s (k + 2) := by
  have hid := sq_next_mul_momentSizeBiasPearsonChiSq s k hk.ne' hk1.ne'
  have hsq : 0 < s (k + 1) ^ (2 : ℕ) := sq_pos_of_pos hk1
  constructor
  · intro h
    have hprod : 0 ≤
        s (k + 1) ^ (2 : ℕ) * momentSizeBiasPearsonChiSq s k :=
      mul_nonneg hsq.le h
    nlinarith
  · intro h
    nlinarith

/-- `1 + chi^(2 : ℕ)` is the multiplicative increment of adjacent moment ratios.  Thus Pearson
information is the discrete projective curvature of the moment sequence. -/
theorem momentSizeBiasPearsonChiSq_add_one_eq_adjacentRatioQuotient
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    momentSizeBiasPearsonChiSq s k + 1 =
      (s (k + 2) / s (k + 1)) / (s (k + 1) / s k) := by
  rw [momentSizeBiasPearsonChiSq_eq_momentRatios]
  field_simp [hk, hk1]
  ring

/-- **Size-bias fluctuation law.**  Variance in the current state is its mean times the increase
of the mean under one further size bias.  This is the exact value behind the waiting-time paradox
and length-biased sampling. -/
theorem momentNormalizedVariance_X_sizeBiased_eq_mean_mul_next_sub_mean
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    momentNormalizedVariance (momentSizeBiasedSequence s k) X =
      momentNormalizedExpectation (momentSizeBiasedSequence s k) X *
        (momentNormalizedExpectation (momentSizeBiasedSequence s (k + 1)) X -
          momentNormalizedExpectation (momentSizeBiasedSequence s k) X) := by
  rw [momentNormalizedVariance_X_sizeBiased s k,
    momentNormalizedExpectation_X_sizeBiased s k,
    momentNormalizedExpectation_X_sizeBiased s (k + 1)]
  rw [show k + 1 + 1 = k + 2 by omega]
  field_simp [hk, hk1]

/-! ### Price response under one further size bias -/

/-- Covariance of the selecting coordinate with `X^n` in the `k`-th size-biased state, written
as a shifted cross-Hankel value. -/
theorem momentNormalizedCovariance_X_X_pow_sizeBiased
    (s : ℕ → ℝ) (k n : ℕ) :
    momentNormalizedCovariance (momentSizeBiasedSequence s k) X (X ^ n) =
      s (k + n + 1) / s k -
        (s (k + 1) / s k) * (s (k + n) / s k) := by
  have hmul : (X : Polynomial ℝ) * X ^ n = X ^ (n + 1) := by
    rw [pow_succ']
  rw [momentNormalizedCovariance, hmul,
    momentNormalizedExpectation_X_pow_sizeBiased,
    momentNormalizedExpectation_X_sizeBiased,
    momentNormalizedExpectation_X_pow_sizeBiased]
  rw [show k + (n + 1) = k + n + 1 by omega]

/-- Denominator-free Price covariance identity.  Its numerator is the generalized `2 x 2`
cross-Hankel minor comparing the moment ratios at indices `k` and `k+n`. -/
theorem sq_mass_mul_momentNormalizedCovariance_X_X_pow_sizeBiased
    (s : ℕ → ℝ) (k n : ℕ) (hk : s k ≠ 0) :
    s k ^ (2 : ℕ) *
        momentNormalizedCovariance (momentSizeBiasedSequence s k) X (X ^ n) =
      s k * s (k + n + 1) - s (k + 1) * s (k + n) := by
  rw [momentNormalizedCovariance_X_X_pow_sizeBiased]
  field_simp [hk]

/-- With positive normalizing mass, nonnegative selection covariance is exactly nonnegativity of
the corresponding cross-Hankel minor. -/
theorem momentNormalizedCovariance_X_X_pow_sizeBiased_nonneg_iff_crossHankel
    (s : ℕ → ℝ) (k n : ℕ) (hk : 0 < s k) :
    0 ≤ momentNormalizedCovariance (momentSizeBiasedSequence s k) X (X ^ n) ↔
      s (k + 1) * s (k + n) ≤ s k * s (k + n + 1) := by
  have hid := sq_mass_mul_momentNormalizedCovariance_X_X_pow_sizeBiased
    s k n hk.ne'
  have hsq : 0 < s k ^ (2 : ℕ) := sq_pos_of_pos hk
  constructor
  · intro h
    have hprod : 0 ≤ s k ^ (2 : ℕ) *
        momentNormalizedCovariance (momentSizeBiasedSequence s k) X (X ^ n) :=
      mul_nonneg hsq.le h
    nlinarith
  · intro h
    nlinarith

/-- **Robertson--Price size-bias equation.**  Selection covariance is the current mean times the
one-step change of the `n`-th power expectation.  The observable itself does not change, so there
is no transmission term. -/
theorem momentNormalizedCovariance_X_X_pow_sizeBiased_eq_mean_mul_response
    (s : ℕ → ℝ) (k n : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    momentNormalizedCovariance (momentSizeBiasedSequence s k) X (X ^ n) =
      momentNormalizedExpectation (momentSizeBiasedSequence s k) X *
        (momentNormalizedExpectation (momentSizeBiasedSequence s (k + 1)) (X ^ n) -
          momentNormalizedExpectation (momentSizeBiasedSequence s k) (X ^ n)) := by
  rw [momentNormalizedCovariance_X_X_pow_sizeBiased,
    momentNormalizedExpectation_X_sizeBiased,
    momentNormalizedExpectation_X_pow_sizeBiased,
    momentNormalizedExpectation_X_pow_sizeBiased]
  rw [show k + 1 + n = k + n + 1 by omega]
  field_simp [hk, hk1]

/-- Quotient form of the Robertson--Price identity: the change of any power expectation under
one further size bias is its selection covariance divided by the current mean. -/
theorem momentSizeBiasPriceEquation_X_pow
    (s : ℕ → ℝ) (k n : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    momentNormalizedExpectation (momentSizeBiasedSequence s (k + 1)) (X ^ n) -
        momentNormalizedExpectation (momentSizeBiasedSequence s k) (X ^ n) =
      momentNormalizedCovariance (momentSizeBiasedSequence s k) X (X ^ n) /
        momentNormalizedExpectation (momentSizeBiasedSequence s k) X := by
  have hmean :
      momentNormalizedExpectation (momentSizeBiasedSequence s k) X ≠ 0 := by
    rw [momentNormalizedExpectation_X_sizeBiased]
    exact div_ne_zero hk1 hk
  rw [momentNormalizedCovariance_X_X_pow_sizeBiased_eq_mean_mul_response
    s k n hk hk1]
  field_simp [hmean]

/-- Pearson information is the relative increase of the mean under one further size bias. -/
theorem momentSizeBiasPearsonChiSq_eq_relativeMeanLift
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    momentSizeBiasPearsonChiSq s k =
      (momentNormalizedExpectation (momentSizeBiasedSequence s (k + 1)) X -
          momentNormalizedExpectation (momentSizeBiasedSequence s k) X) /
        momentNormalizedExpectation (momentSizeBiasedSequence s k) X := by
  rw [momentSizeBiasPearsonChiSq_eq_momentRatios,
    momentNormalizedExpectation_X_sizeBiased s k,
    momentNormalizedExpectation_X_sizeBiased s (k + 1)]
  rw [show k + 1 + 1 = k + 2 by omega]
  field_simp [hk, hk1]

/-- **Hammersley--Chapman--Robbins saturation.**  For a size-bias pair and the statistic `X`,
the chi-square change-of-measure bound is an equality.  Thus this generic information inequality
cannot improve the moment problem without an independent bound on the mean lift. -/
theorem momentSizeBiasPearsonChiSq_hcr_saturation
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    (momentNormalizedExpectation (momentSizeBiasedSequence s (k + 1)) X -
        momentNormalizedExpectation (momentSizeBiasedSequence s k) X) ^ (2 : ℕ) =
      momentNormalizedVariance (momentSizeBiasedSequence s k) X *
        momentSizeBiasPearsonChiSq s k := by
  have hmean :
      momentNormalizedExpectation (momentSizeBiasedSequence s k) X ≠ 0 := by
    rw [momentNormalizedExpectation_X_sizeBiased s k]
    exact div_ne_zero hk1 hk
  rw [momentNormalizedVariance_X_sizeBiased_eq_mean_mul_next_sub_mean
      s k hk hk1,
    momentSizeBiasPearsonChiSq_eq_relativeMeanLift s k hk hk1]
  field_simp [hmean]

/-- Pure-state QFI of the size-biased coordinate is four times the mean times its size-bias lift. -/
theorem pureStateQuantumFisherValue_sizeBiased_X_eq_meanLift
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) (hk1 : s (k + 1) ≠ 0) :
    pureStateQuantumFisherValue
        (momentSizeBiasedSequence s k 0)
        (momentFunctional (momentSizeBiasedSequence s k) X)
        (momentFunctional (momentSizeBiasedSequence s k) (X ^ (2 : ℕ))) =
      4 * momentNormalizedExpectation (momentSizeBiasedSequence s k) X *
        (momentNormalizedExpectation (momentSizeBiasedSequence s (k + 1)) X -
          momentNormalizedExpectation (momentSizeBiasedSequence s k) X) := by
  have hk' : momentSizeBiasedSequence s k 0 ≠ 0 := by
    simpa [momentSizeBiasedSequence] using hk
  rw [pureStateQuantumFisherValue_moment_eq_four_mul_normalizedVariance
    (momentSizeBiasedSequence s k) hk' X,
    momentNormalizedVariance_X_sizeBiased_eq_mean_mul_next_sub_mean
      s k hk hk1]
  ring

/-- The Pearson value is the pure-state quantum Fisher information divided by four times the
squared signal.  This is the exact information-theoretic normalization of the moment QFI. -/
theorem momentSizeBiasPearsonChiSq_eq_quantumFisher_signalRatio
    (s : ℕ → ℝ) (k : ℕ) (hk : s k ≠ 0) :
    momentSizeBiasPearsonChiSq s k =
      pureStateQuantumFisherValue
          (momentSizeBiasedSequence s k 0)
          (momentFunctional (momentSizeBiasedSequence s k) X)
          (momentFunctional (momentSizeBiasedSequence s k) (X ^ (2 : ℕ))) /
        (4 * momentNormalizedExpectation
          (momentSizeBiasedSequence s k) X ^ (2 : ℕ)) := by
  have hk' : momentSizeBiasedSequence s k 0 ≠ 0 := by
    simpa [momentSizeBiasedSequence] using hk
  rw [pureStateQuantumFisherValue_moment_eq_four_mul_normalizedVariance
    (momentSizeBiasedSequence s k) hk' X]
  unfold momentSizeBiasPearsonChiSq
  by_cases hmean :
      momentNormalizedExpectation (momentSizeBiasedSequence s k) X = 0
  · simp [hmean]
  · field_simp [hmean]

/-! ### Mixtures and the laws of total covariance and variance -/

/-- Pointwise sum of two moment sequences. -/
def momentSequenceSum (s t : ℕ → ℝ) : ℕ → ℝ :=
  fun n => s n + t n

/-- Moment evaluation is additive in the underlying sequence. -/
theorem momentFunctional_sequenceSum
    (s t : ℕ → ℝ) (p : Polynomial ℝ) :
    momentFunctional (momentSequenceSum s t) p =
      momentFunctional s p + momentFunctional t p := by
  rw [momentFunctional_eq_support_sum, momentFunctional_eq_support_sum,
    momentFunctional_eq_support_sum]
  simp only [momentSequenceSum, mul_add, Finset.sum_add_distrib]

/-- **Law of total covariance for moment states.**  The covariance of a two-component
positive-mass mixture is the weighted within-component covariance plus the product of the two
component expectation mismatches.  This is the polarized statistical-mechanics mixture law;
the total-variance identity below is its diagonal specialization. -/
theorem momentNormalizedCovariance_sequenceSum
    (s t : ℕ → ℝ) (hs : s 0 ≠ 0) (ht : t 0 ≠ 0)
    (hst : s 0 + t 0 ≠ 0) (p q : Polynomial ℝ) :
    momentNormalizedCovariance (momentSequenceSum s t) p q =
      s 0 / (s 0 + t 0) * momentNormalizedCovariance s p q +
        t 0 / (s 0 + t 0) * momentNormalizedCovariance t p q +
          (s 0 * t 0 / (s 0 + t 0) ^ (2 : ℕ)) *
            (momentNormalizedExpectation s p -
              momentNormalizedExpectation t p) *
            (momentNormalizedExpectation s q -
              momentNormalizedExpectation t q) := by
  unfold momentNormalizedCovariance momentNormalizedExpectation
  rw [momentFunctional_sequenceSum, momentFunctional_sequenceSum,
    momentFunctional_sequenceSum]
  simp only [momentSequenceSum]
  field_simp [hs, ht, hst]
  ring

/-- **Law of total variance for moment states.**  The variance of a two-component positive-mass
mixture is the weighted within-component variance plus the variance of the two component means.
The identity itself is algebraic; positivity of its three terms is supplied separately by the
component moment states. -/
theorem momentNormalizedVariance_sequenceSum
    (s t : ℕ → ℝ) (hs : s 0 ≠ 0) (ht : t 0 ≠ 0)
    (hst : s 0 + t 0 ≠ 0) (p : Polynomial ℝ) :
    momentNormalizedVariance (momentSequenceSum s t) p =
      s 0 / (s 0 + t 0) * momentNormalizedVariance s p +
        t 0 / (s 0 + t 0) * momentNormalizedVariance t p +
          (s 0 * t 0 / (s 0 + t 0) ^ (2 : ℕ)) *
            (momentNormalizedExpectation s p -
              momentNormalizedExpectation t p) ^ (2 : ℕ) := by
  unfold momentNormalizedVariance momentNormalizedExpectation
  rw [momentFunctional_sequenceSum, momentFunctional_sequenceSum]
  simp only [momentSequenceSum]
  field_simp [hs, ht, hst]
  ring

/-- With positive component masses and nonnegative second-component variance, a mixture variance
is at least its weighted first-component variance. -/
theorem weighted_left_variance_le_sequenceSum
    (s t : ℕ → ℝ) (hs : 0 < s 0) (ht : 0 < t 0) (p : Polynomial ℝ)
    (hvart : 0 ≤ momentNormalizedVariance t p) :
    s 0 / (s 0 + t 0) * momentNormalizedVariance s p ≤
      momentNormalizedVariance (momentSequenceSum s t) p := by
  rw [momentNormalizedVariance_sequenceSum s t hs.ne' ht.ne' (add_pos hs ht).ne' p]
  have hweight : 0 ≤ t 0 / (s 0 + t 0) :=
    (div_nonneg ht.le (add_pos hs ht).le)
  have hbetween : 0 ≤ s 0 * t 0 / (s 0 + t 0) ^ (2 : ℕ) := by positivity
  nlinarith [mul_nonneg hweight hvart,
    mul_nonneg hbetween
      (sq_nonneg (momentNormalizedExpectation s p -
        momentNormalizedExpectation t p))]

end

end HTGeometry
