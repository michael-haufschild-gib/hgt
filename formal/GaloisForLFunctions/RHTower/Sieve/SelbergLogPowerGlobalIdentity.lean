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
  · simp [coefficientExponentialJet, hf.one]
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
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [selbergDiagonalLogPowerJet, coefficientExponentialJet,
    selbergDiagonalReciprocalCoeff, selbergLocalDiagonalJet]
  have hpow : p ^ i = p ^ j ↔ i = j :=
    (Nat.pow_right_injective hp.two_le).eq_iff
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, if_pos rfl, reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero)]
    push_cast
    rw [Real.log_pow, localJetParameter, mul_pow, map_pow,
      ← exponentialJet_nat_mul]
    congr 2
    · field_simp [hpR]
    · push_cast
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
    bivariateDirichletConvolution_prime_pow _ _ hp,
    selbergLocalPrincipalJet]
  apply congrFun₂
  · funext a b
    exact selbergDiagonalLogPowerJet_prime_pow_eq hp a b
  · funext a b
    exact selbergMoebiusReciprocalPairJet_prime_pow_eq hp a b

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
      additiveBivariateMonomialOver, localJetParameter]
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
  rw [bivariateDirichletConvolution_prime_pow _ _ hp,
    selbergEulerCorrectionJet_prime_pow hp,
    selbergPrincipalLogPowerJet_prime_pow_eq hp,
    selbergOriginalLogPowerJet_prime_pow_eq hp]
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
    simp only [if_false, Nat.add_eq_zero, one_ne_zero, and_false]
    field_simp [hfac]

end

end RHTower.Sieve
