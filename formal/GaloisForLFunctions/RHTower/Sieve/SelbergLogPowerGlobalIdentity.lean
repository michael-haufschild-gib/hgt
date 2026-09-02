import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerJetIdentity
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogPowerPrincipalCollapse

/-!
# Global all-order logarithmic Selberg identity

The local formal identity propagates through pair-coprime multiplicativity.  Its coefficients give
the exact higher Leibniz decomposition needed for the square and cube of `log gcd`.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

def coefficientExponentialJet (f : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (m n : ℕ) : PowerSeries ℝ :=
  PowerSeries.C (f m n) * exponentialJet (w m n)

private theorem bivariateMultiplicative_coefficientExponentialJet
    {f : ℕ → ℕ → ℝ} {w : ℕ → ℕ → ℝ}
    (hf : BivariateMultiplicative f)
    (hfpos : ∀ {m n : ℕ}, f m n ≠ 0 → 0 < m ∧ 0 < n)
    (hw : ∀ {a b c d : ℕ}, 0 < a → 0 < b → 0 < c → 0 < d →
      Nat.Coprime (a * b) (c * d) → w (a * c) (b * d) = w a b + w c d) :
    BivariateMultiplicative (coefficientExponentialJet f w) := by
  constructor
  · have hw1 := hw (a := 1) (b := 1) (c := 1) (d := 1)
        (by omega) (by omega) (by omega) (by omega) (by norm_num)
    have hw0 : w 1 1 = 0 := by linarith
    simp [coefficientExponentialJet, hf.one, hw0]
  · intro a b c d h
    rw [coefficientExponentialJet, coefficientExponentialJet,
      coefficientExponentialJet, hf.map_mul_of_pair_coprime h]
    by_cases hfab : f a b = 0
    · simp [hfab]
    by_cases hfcd : f c d = 0
    · simp [hfcd]
    obtain ⟨ha, hb⟩ := hfpos hfab
    obtain ⟨hc, hd⟩ := hfpos hfcd
    rw [hw ha hb hc hd h, exponentialJet_add, map_mul]
    ring

/-- Literal original coefficient with its complete exponential `log gcd` jet. -/
def selbergOriginalLogPowerJet : ℕ → ℕ → PowerSeries ℝ :=
  coefficientExponentialJet selbergOriginalCoeff
    (fun m n => Real.log ((Nat.gcd m n : ℕ) : ℝ))

/-- Reciprocal diagonal with its complete logarithmic jet. -/
def selbergDiagonalLogPowerJet : ℕ → ℕ → PowerSeries ℝ :=
  coefficientExponentialJet selbergDiagonalReciprocalCoeff
    (fun m _ => Real.log (m : ℝ))

/-- Constant jet of the reciprocal Möbius pair. -/
def selbergMoebiusReciprocalPairJet (m n : ℕ) : PowerSeries ℝ :=
  PowerSeries.C (selbergMoebiusReciprocalPair m n)

/-- Principal logarithmic jet: only the reciprocal diagonal is deformed. -/
def selbergPrincipalLogPowerJet : ℕ → ℕ → PowerSeries ℝ :=
  bivariateDirichletConvolution selbergDiagonalLogPowerJet
    selbergMoebiusReciprocalPairJet

theorem bivariateMultiplicative_selbergOriginalLogPowerJet :
    BivariateMultiplicative selbergOriginalLogPowerJet := by
  apply bivariateMultiplicative_coefficientExponentialJet
    bivariateMultiplicative_selbergOriginalCoeff
  · intro m n hmn
    constructor
    · by_contra hm
      have : m = 0 := by omega
      subst m
      exact hmn (by simp [selbergOriginalCoeff])
    · by_contra hn
      have : n = 0 := by omega
      subst n
      exact hmn (by simp [selbergOriginalCoeff])
  · intro a b c d ha hb hc hd h
    rw [gcd_pair_mul_of_pair_coprime h]
    push_cast
    exact Real.log_mul
      (by exact_mod_cast (Nat.gcd_pos_of_pos_left b ha).ne')
      (by exact_mod_cast (Nat.gcd_pos_of_pos_left d hc).ne')

theorem bivariateMultiplicative_selbergDiagonalLogPowerJet :
    BivariateMultiplicative selbergDiagonalLogPowerJet := by
  apply bivariateMultiplicative_coefficientExponentialJet
    bivariateMultiplicative_selbergDiagonalReciprocalCoeff
  · intro m n hmn
    rw [selbergDiagonalReciprocalCoeff] at hmn
    split_ifs at hmn with h
    · subst n
      have hm0 : m ≠ 0 := by
        intro hm
        subst m
        exact hmn (by simp [reciprocalNatArithmetic])
      exact ⟨Nat.pos_of_ne_zero hm0, Nat.pos_of_ne_zero hm0⟩
    · exact (hmn rfl).elim
  · intro a b c d ha hb hc hd h
    push_cast
    exact Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hc.ne')

theorem bivariateMultiplicative_selbergMoebiusReciprocalPairJet :
    BivariateMultiplicative selbergMoebiusReciprocalPairJet := by
  constructor
  · simp [selbergMoebiusReciprocalPairJet,
      bivariateMultiplicative_selbergMoebiusReciprocalPair.one]
  · intro a b c d h
    rw [selbergMoebiusReciprocalPairJet, selbergMoebiusReciprocalPairJet,
      selbergMoebiusReciprocalPairJet,
      bivariateMultiplicative_selbergMoebiusReciprocalPair.map_mul_of_pair_coprime h,
      map_mul]

theorem bivariateMultiplicative_selbergPrincipalLogPowerJet :
    BivariateMultiplicative selbergPrincipalLogPowerJet :=
  bivariateMultiplicative_selbergDiagonalLogPowerJet.convolution
    bivariateMultiplicative_selbergMoebiusReciprocalPairJet

private theorem selbergDiagonalLogPowerJet_prime_pow_eq
    {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergDiagonalLogPowerJet (p ^ i) (p ^ j) = selbergLocalDiagonalJet p i j := by
  rw [selbergDiagonalLogPowerJet, coefficientExponentialJet,
    selbergDiagonalReciprocalCoeff, selbergLocalDiagonalJet]
  have hpow : p ^ i = p ^ j ↔ i = j :=
    (Nat.pow_right_injective hp.two_le).eq_iff
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, if_pos rfl, reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero)]
    push_cast
    rw [Real.log_pow, selbergLocalJetParameter, mul_pow]
    have hq : 1 / (p : ℝ) ^ i = (1 / (p : ℝ)) ^ i := by
      rw [one_div, one_div, inv_pow]
    rw [hq, map_pow, ← exponentialJet_nat_mul]
  · rw [if_neg (by simpa [hpow] using hij), if_neg hij]
    simp

private theorem selbergMoebiusReciprocalPairJet_prime_pow_eq
    {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergMoebiusReciprocalPairJet (p ^ i) (p ^ j) = selbergLocalMoebiusJet p i j := by
  rw [selbergMoebiusReciprocalPairJet, selbergLocalMoebiusJet,
    show localMoebiusPairFactor p = selbergLocalMoebiusReciprocalPair p from
      localMoebiusPairFactor_eq hp]
  rfl

private theorem selbergPrincipalLogPowerJet_prime_pow_eq
    {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergPrincipalLogPowerJet (p ^ i) (p ^ j) = selbergLocalPrincipalJet p i j := by
  rw [selbergPrincipalLogPowerJet,
    bivariateDirichletConvolution_prime_pow_over _ _ hp,
    selbergLocalPrincipalJet]
  have hd : (fun a b => selbergDiagonalLogPowerJet (p ^ a) (p ^ b)) =
      selbergLocalDiagonalJet p := by
    funext a b
    exact selbergDiagonalLogPowerJet_prime_pow_eq hp a b
  have hm : (fun a b => selbergMoebiusReciprocalPairJet (p ^ a) (p ^ b)) =
      selbergLocalMoebiusJet p := by
    funext a b
    exact selbergMoebiusReciprocalPairJet_prime_pow_eq hp a b
  rw [hd, hm]

private theorem selbergOriginalLogPowerJet_prime_pow_eq
    {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergOriginalLogPowerJet (p ^ i) (p ^ j) = selbergLocalOriginalJet p i j := by
  rw [selbergOriginalLogPowerJet, coefficientExponentialJet,
    show selbergOriginalCoeff (p ^ i) (p ^ j) = selbergLocalOriginal p i j from rfl,
    selbergLocalOriginal_eq_polynomial hp]
  rw [gcd_prime_pow_eq_pow_min]
  rw [Nat.cast_pow, Real.log_pow]
  match i, j with
  | 0, 0 => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
      additiveBivariateMonomialOver]
  | 0, (j + 1) =>
      match j with
      | 0 => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
          additiveBivariateMonomialOver]
      | (j + 1) => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
          additiveBivariateMonomialOver]
  | (i + 1), 0 =>
      match i with
      | 0 => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
          additiveBivariateMonomialOver]
      | (i + 1) => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
          additiveBivariateMonomialOver]
  | 1, 1 => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
      additiveBivariateMonomialOver, selbergLocalJetParameter]
  | 1, (j + 2) => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
      additiveBivariateMonomialOver]
  | (i + 2), (j + 1) => simp [selbergLocalOriginalPolynomial, selbergLocalOriginalJet,
      additiveBivariateMonomialOver]

/-- Exact global identity of formal logarithmic jets. -/
theorem selbergOriginalLogPowerJet_eq_correction_convolution_principal :
    selbergOriginalLogPowerJet =
      bivariateDirichletConvolution selbergEulerCorrectionJet
        selbergPrincipalLogPowerJet := by
  funext m n
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [selbergOriginalLogPowerJet, coefficientExponentialJet,
      selbergOriginalCoeff, bivariateDirichletConvolution]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [selbergOriginalLogPowerJet, coefficientExponentialJet,
      selbergOriginalCoeff, bivariateDirichletConvolution]
  refine BivariateMultiplicative.eq_of_prime_pow_eq
    bivariateMultiplicative_selbergOriginalLogPowerJet
    (bivariateMultiplicative_selbergEulerCorrectionJet.convolution
      bivariateMultiplicative_selbergPrincipalLogPowerJet) ?_ hm hn
  intro p hp i j
  rw [bivariateDirichletConvolution_prime_pow_over _ _ hp,
    selbergOriginalLogPowerJet_prime_pow_eq hp]
  have hc : (fun a b => selbergEulerCorrectionJet (p ^ a) (p ^ b)) =
      selbergCorrectionJetLocal p := by
    funext a b
    exact selbergEulerCorrectionJet_prime_pow hp a b
  have hprin : (fun a b => selbergPrincipalLogPowerJet (p ^ a) (p ^ b)) =
      selbergLocalPrincipalJet p := by
    funext a b
    exact selbergPrincipalLogPowerJet_prime_pow_eq hp a b
  rw [hc, hprin]
  exact congrFun₂
    (additiveBivariateConvolutionOver_localCorrectionJet_principal hp) i j |>.symm

/-- Ordinary `k`-th logarithmic derivative of the global correction. -/
def selbergEulerCorrectionLogPowerCoeff (k m n : ℕ) : ℝ :=
  (k.factorial : ℝ) * PowerSeries.coeff k (selbergEulerCorrectionJet m n)

theorem selbergEulerCorrectionLogPowerCoeff_zero (m n : ℕ) :
    selbergEulerCorrectionLogPowerCoeff 0 m n = selbergEulerCorrectionCoeff m n := by
  simp [selbergEulerCorrectionLogPowerCoeff, coeff_zero_selbergEulerCorrectionJet]

theorem selbergEulerCorrectionLogPowerCoeff_prime_pow
    {p : ℕ} (hp : p.Prime) (k i j : ℕ) :
    selbergEulerCorrectionLogPowerCoeff k (p ^ i) (p ^ j) =
      if k = 0 then selbergLocalCorrection p i j
      else selbergCorrectionLogPowerLocal k p i j := by
  rw [selbergEulerCorrectionLogPowerCoeff, selbergEulerCorrectionJet_prime_pow hp]
  rcases k with _ | k
  · simp
  · rw [coeff_selbergCorrectionJetLocal_succ]
    have hfac : (((k + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    field_simp [hfac]

/-- Ordinary (rather than divided-power) coefficient of a power-series-valued arithmetic
function. -/
def ordinaryPowerSeriesCoeff (k : ℕ) (F : ℕ → ℕ → PowerSeries ℝ) (m n : ℕ) : ℝ :=
  (k.factorial : ℝ) * PowerSeries.coeff k (F m n)

theorem ordinaryPowerSeriesCoeff_mul (k : ℕ) (F G : PowerSeries ℝ) :
    (k.factorial : ℝ) * PowerSeries.coeff k (F * G) =
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
        ((l.factorial : ℝ) * PowerSeries.coeff l F) *
        (((k - l).factorial : ℝ) * PowerSeries.coeff (k - l) G) := by
  rw [PowerSeries.coeff_mul, sum_nat_antidiagonal_eq_range_real, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hlk : l ≤ k := by simpa using hl
  have hfac := Nat.choose_mul_factorial_mul_factorial hlk
  have hfacR : (k.choose l : ℝ) * (l.factorial : ℝ) *
      ((k - l).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast hfac
  rw [← hfacR]
  ring

/-- Ordinary coefficients turn convolution of power-series-valued arithmetic functions into the
binomial Leibniz convolution of their ordinary coefficients. -/
theorem ordinaryPowerSeriesCoeff_bivariateDirichletConvolution
    (k : ℕ) (F G : ℕ → ℕ → PowerSeries ℝ) :
    ordinaryPowerSeriesCoeff k (bivariateDirichletConvolution F G) =
      fun m n => ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
        bivariateDirichletConvolution
          (ordinaryPowerSeriesCoeff l F)
          (ordinaryPowerSeriesCoeff (k - l) G) m n := by
  funext m n
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [ordinaryPowerSeriesCoeff, bivariateDirichletConvolution]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [ordinaryPowerSeriesCoeff, bivariateDirichletConvolution]
  rw [ordinaryPowerSeriesCoeff, bivariateDirichletConvolution,
    if_neg (by omega), map_sum, Finset.mul_sum]
  simp_rw [ordinaryPowerSeriesCoeff_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [bivariateDirichletConvolution, if_neg (by omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  simp [ordinaryPowerSeriesCoeff]
  ring

/-- The ordinary coefficients of the original jet are the literal powers of `log gcd`. -/
theorem ordinaryPowerSeriesCoeff_selbergOriginalLogPowerJet (k m n : ℕ) :
    ordinaryPowerSeriesCoeff k selbergOriginalLogPowerJet m n =
      selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ) ^ k := by
  rw [ordinaryPowerSeriesCoeff, selbergOriginalLogPowerJet, coefficientExponentialJet,
    PowerSeries.coeff_mul, sum_nat_antidiagonal_eq_range_real]
  simp only [PowerSeries.coeff_C, coeff_exponentialJet]
  rw [Finset.sum_eq_single 0]
  · simp
    have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · intro l hl hl0
    simp [hl0]
  · simp

/-- The ordinary coefficients of the diagonal jet are exactly the logarithmic-power diagonal. -/
theorem ordinaryPowerSeriesCoeff_selbergDiagonalLogPowerJet (k m n : ℕ) :
    ordinaryPowerSeriesCoeff k selbergDiagonalLogPowerJet m n =
      selbergDiagonalLogPowerReciprocalCoeff k m n := by
  rw [ordinaryPowerSeriesCoeff, selbergDiagonalLogPowerJet, coefficientExponentialJet,
    PowerSeries.coeff_mul, sum_nat_antidiagonal_eq_range_real]
  simp only [PowerSeries.coeff_C, coeff_exponentialJet]
  rw [Finset.sum_eq_single 0]
  · simp [selbergDiagonalReciprocalCoeff, selbergDiagonalLogPowerReciprocalCoeff]
    split_ifs with hmn
    · subst n
      by_cases hm : m = 0
      · subst m
        simp [reciprocalNatArithmetic]
      · rw [reciprocalNatArithmetic_apply hm]
        have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp
    · rfl
  · intro l hl hl0
    simp [hl0]
  · simp

/-- The constant reciprocal Möbius jet has only its zeroth ordinary coefficient. -/
theorem ordinaryPowerSeriesCoeff_selbergMoebiusReciprocalPairJet (k m n : ℕ) :
    ordinaryPowerSeriesCoeff k selbergMoebiusReciprocalPairJet m n =
      if k = 0 then selbergMoebiusReciprocalPair m n else 0 := by
  rw [ordinaryPowerSeriesCoeff, selbergMoebiusReciprocalPairJet]
  rcases k with _ | k <;> simp

/-- The ordinary coefficients of the principal jet recover the principal gcd-log coefficients. -/
theorem ordinaryPowerSeriesCoeff_selbergPrincipalLogPowerJet (k m n : ℕ) :
    ordinaryPowerSeriesCoeff k selbergPrincipalLogPowerJet m n =
      selbergGcdLogPowerPrincipalCoeff k m n := by
  rw [selbergPrincipalLogPowerJet,
    ordinaryPowerSeriesCoeff_bivariateDirichletConvolution,
    selbergGcdLogPowerPrincipalCoeff]
  change (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
      bivariateDirichletConvolution
        (ordinaryPowerSeriesCoeff l selbergDiagonalLogPowerJet)
        (ordinaryPowerSeriesCoeff (k - l) selbergMoebiusReciprocalPairJet) m n) =
    bivariateDirichletConvolution
      (selbergDiagonalLogPowerReciprocalCoeff k)
      selbergMoebiusReciprocalPair m n
  have hd (l : ℕ) : ordinaryPowerSeriesCoeff l selbergDiagonalLogPowerJet =
      selbergDiagonalLogPowerReciprocalCoeff l := by
    funext a b
    exact ordinaryPowerSeriesCoeff_selbergDiagonalLogPowerJet l a b
  have hmj (l : ℕ) : ordinaryPowerSeriesCoeff l selbergMoebiusReciprocalPairJet =
      fun a b => if l = 0 then selbergMoebiusReciprocalPair a b else 0 := by
    funext a b
    exact ordinaryPowerSeriesCoeff_selbergMoebiusReciprocalPairJet l a b
  simp_rw [hd]
  simp_rw [hmj]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [bivariateDirichletConvolution]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [bivariateDirichletConvolution]
  rw [bivariateDirichletConvolution, if_neg (by omega)]
  rw [Finset.sum_eq_single k]
  · simp [bivariateDirichletConvolution, show ¬ (m = 0 ∨ n = 0) by omega]
  · intro l hl hlk
    have hle : l ≤ k := by simpa using hl
    have hkl : k - l ≠ 0 := by omega
    simp [hkl, bivariateDirichletConvolution]
  · simp

/-- Exact all-order decomposition of the literal gcd-log coefficient into global correction
derivatives and principal logarithmic coefficients. -/
theorem selbergOriginalCoeff_mul_log_gcd_pow_eq_correction_convolution_principal
    (k m n : ℕ) :
    selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ) ^ k =
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
        bivariateDirichletConvolution
          (selbergEulerCorrectionLogPowerCoeff l)
          (selbergGcdLogPowerPrincipalCoeff (k - l)) m n := by
  rw [← ordinaryPowerSeriesCoeff_selbergOriginalLogPowerJet,
    selbergOriginalLogPowerJet_eq_correction_convolution_principal,
    ordinaryPowerSeriesCoeff_bivariateDirichletConvolution]
  change (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
      bivariateDirichletConvolution
        (ordinaryPowerSeriesCoeff l selbergEulerCorrectionJet)
        (ordinaryPowerSeriesCoeff (k - l) selbergPrincipalLogPowerJet) m n) = _
  have hc (l : ℕ) : ordinaryPowerSeriesCoeff l selbergEulerCorrectionJet =
      selbergEulerCorrectionLogPowerCoeff l := rfl
  have hp (l : ℕ) : ordinaryPowerSeriesCoeff l selbergPrincipalLogPowerJet =
      selbergGcdLogPowerPrincipalCoeff l := by
    funext a b
    exact ordinaryPowerSeriesCoeff_selbergPrincipalLogPowerJet l a b
  simp_rw [hp]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hc l]

end

end RHTower.Sieve
