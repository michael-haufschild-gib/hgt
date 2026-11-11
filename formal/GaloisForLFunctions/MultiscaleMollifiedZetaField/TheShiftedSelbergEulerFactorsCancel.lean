import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergCorrectionIsMultiplicative
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationInversionLawOfTheSource

/-!
# Exact Euler factorization with a shifted gcd exponent

The correction amplitude cancels the reciprocal Möbius factor by
Dirichlet inversion. The remaining numerator is a polynomial with four
terms. Its diagonal denominator cancels against the principal geometric
factor, giving the literal shifted Möbius–gcd coefficient.
-/

open ArithmeticFunction Finset
open RHTower.Sieve
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The diagonal reciprocal coefficient with its real power shift. -/
def shiftedSelbergDiagonal (s : ℝ) (m n : ℕ) : ℝ :=
  selbergDiagonalReciprocalCoeff m n * (m : ℝ) ^ s

/-- The shifted diagonal convolved with the two reciprocal Möbius rows. -/
def shiftedSelbergPrincipal (s : ℝ) : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution (shiftedSelbergDiagonal s) selbergMoebiusReciprocalPair

/-- The literal Möbius–gcd coefficient with gcd exponent `1+s`. -/
def shiftedSelbergOriginal (s : ℝ) (m n : ℕ) : ℝ :=
  selbergOriginalCoeff m n * (Nat.gcd m n : ℝ) ^ s

theorem bivariateMultiplicative_shiftedSelbergDiagonal (s : ℝ) :
    BivariateMultiplicative (shiftedSelbergDiagonal s) := by
  constructor
  · simp [shiftedSelbergDiagonal, selbergDiagonalReciprocalCoeff]
  · intro a b c d h
    rw [shiftedSelbergDiagonal, shiftedSelbergDiagonal, shiftedSelbergDiagonal,
      bivariateMultiplicative_selbergDiagonalReciprocalCoeff.map_mul_of_pair_coprime h,
      Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg c)]
    ring

theorem bivariateMultiplicative_shiftedSelbergPrincipal (s : ℝ) :
    BivariateMultiplicative (shiftedSelbergPrincipal s) :=
  (bivariateMultiplicative_shiftedSelbergDiagonal s).convolution
    bivariateMultiplicative_selbergMoebiusReciprocalPair

theorem bivariateMultiplicative_shiftedSelbergOriginal (s : ℝ) :
    BivariateMultiplicative (shiftedSelbergOriginal s) := by
  constructor
  · simp [shiftedSelbergOriginal]
  · intro a b c d h
    rw [shiftedSelbergOriginal, shiftedSelbergOriginal, shiftedSelbergOriginal,
      bivariateMultiplicative_selbergOriginalCoeff.map_mul_of_pair_coprime h,
      gcd_pair_mul_of_pair_coprime h, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

private theorem reciprocalNatArithmetic_eq_dampedTwist :
    reciprocalNatArithmetic = dampedTwist 1 (↑ζ : ArithmeticFunction ℝ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [reciprocalNatArithmetic_apply hn, dampedTwist_apply, hn, Real.rpow_neg_one]

private theorem powerShiftedMoebius_neg_one_eq_dampedTwist :
    powerShiftedMoebius (-1) = dampedTwist 1 (↑moebius : ArithmeticFunction ℝ) := by
  ext n
  simp only [powerShiftedMoebius_apply, dampedTwist_apply, ArithmeticFunction.intCoe_apply]

/-- The correction amplitude cancels the reciprocal Möbius factor exactly. -/
theorem powerShiftedReciprocalAmplitude_mul_reciprocalMoebius (s : ℝ) :
    powerShiftedReciprocalAmplitude s * powerShiftedMoebius (-1) = powerShiftedMoebius s := by
  rw [powerShiftedReciprocalAmplitude, mul_assoc, reciprocalNatArithmetic_eq_dampedTwist,
    powerShiftedMoebius_neg_one_eq_dampedTwist,
    mul_comm (dampedTwist 1 (↑ζ : ArithmeticFunction ℝ)),
    dampedTwist_moebius_mul_dampedTwist_zeta, mul_one]

private theorem powerShiftedMoebius_neg_one_apply (n : ℕ) :
    powerShiftedMoebius (-1) n = selbergMoebiusReciprocalCoeff n := by
  simp only [powerShiftedMoebius_apply, selbergMoebiusReciprocalCoeff,
    Real.rpow_neg_one, div_eq_mul_inv]

private theorem shiftedSelbergLocalAmplitude_convolution (s : ℝ)
    {p n : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (n + 1), powerShiftedReciprocalAmplitude s (p ^ k) *
      selbergMoebiusReciprocalCoeff (p ^ (n - k))) = powerShiftedMoebius s (p ^ n) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f (p ^ n))
    (powerShiftedReciprocalAmplitude_mul_reciprocalMoebius s)
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => powerShiftedReciprocalAmplitude s i *
      powerShiftedMoebius (-1) j), Nat.sum_divisors_prime_pow hp] at h
  refine (Finset.sum_congr rfl fun k hk => ?_).trans h
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hp.pos,
    powerShiftedMoebius_neg_one_apply]

def shiftedSelbergLocalAmplitudePair (s : ℝ) (p i j : ℕ) : ℝ :=
  powerShiftedReciprocalAmplitude s (p ^ i) * powerShiftedReciprocalAmplitude s (p ^ j)

def shiftedSelbergLocalMoebiusPair (s : ℝ) (p i j : ℕ) : ℝ :=
  powerShiftedMoebius s (p ^ i) * powerShiftedMoebius s (p ^ j)

def shiftedSelbergLocalDiagonal (s : ℝ) (p i j : ℕ) : ℝ :=
  shiftedSelbergDiagonal s (p ^ i) (p ^ j)

def shiftedSelbergLocalDenominator (s : ℝ) (p : ℕ) : ℕ → ℕ → ℝ :=
  fun i j => additiveBivariateOne i j -
    additiveBivariateDiagonalMonomial ((p : ℝ) ^ s / p) i j

def shiftedSelbergLocalCorrection (s : ℝ) (p i j : ℕ) : ℝ :=
  shiftedSelbergCorrectionCoeff s (p ^ i) (p ^ j)

def shiftedSelbergLocalPrincipal (s : ℝ) (p i j : ℕ) : ℝ :=
  shiftedSelbergPrincipal s (p ^ i) (p ^ j)

def shiftedSelbergLocalOriginal (s : ℝ) (p i j : ℕ) : ℝ :=
  shiftedSelbergOriginal s (p ^ i) (p ^ j)

private theorem additiveBivariateConvolution_pair
    (a b c d : ℕ → ℝ) (i j : ℕ) :
    additiveBivariateConvolution (fun x y => a x * b y) (fun x y => c x * d y) i j =
      (∑ x ∈ Finset.range (i + 1), a x * c (i - x)) *
        ∑ y ∈ Finset.range (j + 1), b y * d (j - y) := by
  rw [additiveBivariateConvolution, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem shiftedSelbergLocalAmplitude_pair_convolution (s : ℝ)
    {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (shiftedSelbergLocalAmplitudePair s p)
      (selbergLocalMoebiusReciprocalPair p) = shiftedSelbergLocalMoebiusPair s p := by
  funext i j
  change additiveBivariateConvolution
      (fun x y => powerShiftedReciprocalAmplitude s (p ^ x) * powerShiftedReciprocalAmplitude s (p ^ y))
      (fun x y => selbergMoebiusReciprocalCoeff (p ^ x) *
        selbergMoebiusReciprocalCoeff (p ^ y)) i j = _
  rw [additiveBivariateConvolution_pair,
    shiftedSelbergLocalAmplitude_convolution s hp,
    shiftedSelbergLocalAmplitude_convolution s hp]
  rfl

theorem shiftedSelbergLocalPrincipal_eq_convolution (s : ℝ) {p : ℕ} (hp : p.Prime) :
    shiftedSelbergLocalPrincipal s p =
      additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
        (selbergLocalMoebiusReciprocalPair p) := by
  funext i j
  rw [shiftedSelbergLocalPrincipal, shiftedSelbergPrincipal,
    bivariateDirichletConvolution_prime_pow _ _ hp]
  rfl

theorem shiftedSelbergLocalCorrection_eq_one_sub_shift (s : ℝ) {p : ℕ} (hp : p.Prime) :
    shiftedSelbergLocalCorrection s p = fun i j =>
      additiveBivariateOne i j -
        additiveBivariateConvolution
          (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
          (shiftedSelbergLocalAmplitudePair s p) i j := by
  rw [additiveBivariateConvolution_diagonalMonomial_left]
  funext i j
  rcases i with _ | i
  · rcases j with _ | j
    · simp [shiftedSelbergLocalCorrection, additiveBivariateOne,
        additiveBivariateDiagonalShift]
    · simp only [shiftedSelbergLocalCorrection, pow_zero]
      rw [
        shiftedSelbergCorrectionCoeff_one_prime_pow_succ s hp]
      simp [additiveBivariateOne, additiveBivariateDiagonalShift]
  · rcases j with _ | j
    · simp only [shiftedSelbergLocalCorrection, pow_zero]
      rw [
        shiftedSelbergCorrectionCoeff_prime_pow_succ_one s hp]
      simp [additiveBivariateOne, additiveBivariateDiagonalShift]
    · rw [shiftedSelbergLocalCorrection, shiftedSelbergCorrectionCoeff_prime_pow_succ s hp]
      simp only [additiveBivariateOne, Nat.succ_ne_zero, and_self, if_false,
        additiveBivariateDiagonalShift, false_or, if_false, Nat.add_sub_cancel,
        shiftedSelbergLocalAmplitudePair]
      ring

theorem shiftedSelbergLocalDiagonal_convolution_denominator (s : ℝ)
    {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
      (shiftedSelbergLocalDenominator s p) = additiveBivariateOne := by
  change additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
    (fun i j => additiveBivariateOne i j -
      additiveBivariateDiagonalMonomial ((p : ℝ) ^ s / p) i j) = _
  rw [additiveBivariateConvolution_sub_right, additiveBivariateConvolution_one_right,
    additiveBivariateConvolution_diagonalMonomial_right]
  funext i j
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hinj := Nat.pow_right_injective hp.two_le
  rcases i with _ | i
  · rcases j with _ | j
    · simp [shiftedSelbergLocalDiagonal, shiftedSelbergDiagonal, selbergDiagonalReciprocalCoeff,
        additiveBivariateDiagonalShift, additiveBivariateOne]
    · have he : (1 : ℕ) ≠ p ^ (j + 1) := ne_of_lt (Nat.one_lt_pow (by omega) hp.one_lt)
      simp [shiftedSelbergLocalDiagonal, shiftedSelbergDiagonal, selbergDiagonalReciprocalCoeff,
        additiveBivariateDiagonalShift, additiveBivariateOne, he]
  · rcases j with _ | j
    · have he : p ^ (i + 1) ≠ (1 : ℕ) := ne_of_gt (Nat.one_lt_pow (by omega) hp.one_lt)
      simp [shiftedSelbergLocalDiagonal, shiftedSelbergDiagonal, selbergDiagonalReciprocalCoeff,
        additiveBivariateDiagonalShift, additiveBivariateOne, he, hp.ne_one]
    · by_cases hij : i = j
      · subst j
        simp only [shiftedSelbergLocalDiagonal, shiftedSelbergDiagonal, selbergDiagonalReciprocalCoeff,
          additiveBivariateDiagonalShift, Nat.succ_ne_zero, false_or, if_false,
          Nat.add_sub_cancel, additiveBivariateOne, and_self, if_true]
        rw [reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero),
          reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero)]
        push_cast
        rw [pow_succ, Real.mul_rpow (pow_nonneg (Nat.cast_nonneg p) _) (Nat.cast_nonneg p)]
        field_simp [hp0] <;> ring
      · have he : p ^ (i + 1) ≠ p ^ (j + 1) := fun h => hij (Nat.add_right_cancel (hinj h))
        have he' : p ^ i ≠ p ^ j := fun h => hij (hinj h)
        simp [shiftedSelbergLocalDiagonal, shiftedSelbergDiagonal, selbergDiagonalReciprocalCoeff,
          additiveBivariateDiagonalShift, additiveBivariateOne, he, he']

def shiftedSelbergLocalOriginalPolynomial (s : ℝ) (p i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 1
  else if i = 1 ∧ j = 0 then -(1 / (p : ℝ))
  else if i = 0 ∧ j = 1 then -(1 / (p : ℝ))
  else if i = 1 ∧ j = 1 then (p : ℝ) ^ s / p
  else 0

theorem shiftedSelbergLocalOriginal_eq_polynomial (s : ℝ) {p : ℕ} (hp : p.Prime) :
    shiftedSelbergLocalOriginal s p = shiftedSelbergLocalOriginalPolynomial s p := by
  funext i j
  change selbergLocalOriginal p i j * (Nat.gcd (p ^ i) (p ^ j) : ℝ) ^ s = _
  rw [selbergLocalOriginal_eq_polynomial hp]
  rcases i with _ | i
  · rcases j with _ | j
    · simp [selbergLocalOriginalPolynomial, shiftedSelbergLocalOriginalPolynomial]
    · rcases j with _ | j <;>
        simp [selbergLocalOriginalPolynomial, shiftedSelbergLocalOriginalPolynomial]
  · rcases i with _ | i
    · rcases j with _ | j
      · simp [selbergLocalOriginalPolynomial, shiftedSelbergLocalOriginalPolynomial]
      · rcases j with _ | j
        · simp [selbergLocalOriginalPolynomial, shiftedSelbergLocalOriginalPolynomial]
          ring
        · simp [selbergLocalOriginalPolynomial, shiftedSelbergLocalOriginalPolynomial]
    · simp [selbergLocalOriginalPolynomial, shiftedSelbergLocalOriginalPolynomial]

theorem shiftedSelbergLocalNumerator_identity (s : ℝ) {p : ℕ} (hp : p.Prime) :
    (fun i j => selbergLocalMoebiusReciprocalPair p i j -
      additiveBivariateConvolution
        (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
        (shiftedSelbergLocalMoebiusPair s p) i j) =
      additiveBivariateConvolution (shiftedSelbergLocalDenominator s p)
        (shiftedSelbergLocalOriginal s p) := by
  rw [additiveBivariateConvolution_diagonalMonomial_left]
  change (fun i j => selbergLocalMoebiusReciprocalPair p i j -
      additiveBivariateDiagonalShift ((1 / (p : ℝ)) ^ 2)
        (shiftedSelbergLocalMoebiusPair s p) i j) =
    additiveBivariateConvolution
      (fun i j => additiveBivariateOne i j -
        additiveBivariateDiagonalMonomial ((p : ℝ) ^ s / p) i j)
      (shiftedSelbergLocalOriginal s p)
  rw [additiveBivariateConvolution_sub_left,
    additiveBivariateConvolution_one_left,
    additiveBivariateConvolution_diagonalMonomial_left,
    shiftedSelbergLocalOriginal_eq_polynomial s hp]
  funext i j
  have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rcases i with _ | i
  · rcases j with _ | j
    · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
        additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial]
    · rcases j with _ | j
      · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime hp, powerShiftedMoebius_apply, moebius_real_prime_pow hp]
      · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
          powerShiftedMoebius_apply, moebius_real_prime_pow hp]
  · rcases i with _ | i
    · rcases j with _ | j
      · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime hp, powerShiftedMoebius_apply, moebius_real_prime_pow hp]
      · rcases j with _ | j
        · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime hp, powerShiftedMoebius_apply, moebius_real_prime_pow hp]
          field_simp [hpR0] <;> ring
        · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime hp,
            selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
            powerShiftedMoebius_apply, moebius_real_prime_pow hp]
          by_cases hj : j = 0 <;> simp [hj] <;> ring
    · rcases j with _ | j
      · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
          powerShiftedMoebius_apply, moebius_real_prime_pow hp]
      · rcases j with _ | j
        · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime hp,
            selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
            powerShiftedMoebius_apply, moebius_real_prime_pow hp]
          by_cases hi : i = 0 <;> simp [hi] <;> ring
        · simp [selbergLocalMoebiusReciprocalPair, shiftedSelbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, shiftedSelbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
            powerShiftedMoebius_apply, moebius_real_prime_pow hp]
          by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]
          field_simp [hpR0] <;> ring

theorem shiftedSelbergLocalCorrection_convolution_principal (s : ℝ) {p : ℕ}
    (hp : p.Prime) :
    additiveBivariateConvolution (shiftedSelbergLocalCorrection s p)
        (shiftedSelbergLocalPrincipal s p) =
      shiftedSelbergLocalOriginal s p := by
  rw [shiftedSelbergLocalCorrection_eq_one_sub_shift s hp,
    shiftedSelbergLocalPrincipal_eq_convolution s hp,
    additiveBivariateConvolution_sub_left,
    additiveBivariateConvolution_one_left]
  calc
    additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
          (selbergLocalMoebiusReciprocalPair p) -
        additiveBivariateConvolution
          (additiveBivariateConvolution
            (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
            (shiftedSelbergLocalAmplitudePair s p))
          (additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
            (selbergLocalMoebiusReciprocalPair p)) =
        additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
          (selbergLocalMoebiusReciprocalPair p) -
        additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
          (additiveBivariateConvolution
            (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
            (additiveBivariateConvolution (shiftedSelbergLocalAmplitudePair s p)
              (selbergLocalMoebiusReciprocalPair p))) := by
      congr 1
      apply bivariateCoefficientSeries_injective
      simp only [bivariateCoefficientSeries_convolution]
      ring
    _ = additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
          (selbergLocalMoebiusReciprocalPair p) -
        additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
          (additiveBivariateConvolution
            (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
            (shiftedSelbergLocalMoebiusPair s p)) := by
      rw [shiftedSelbergLocalAmplitude_pair_convolution s hp]
    _ = additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
          (fun i j => selbergLocalMoebiusReciprocalPair p i j -
            additiveBivariateConvolution
              (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
              (shiftedSelbergLocalMoebiusPair s p) i j) := by
      rw [additiveBivariateConvolution_sub_right]
      funext i j
      rfl
    _ = additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
          (additiveBivariateConvolution (shiftedSelbergLocalDenominator s p)
            (shiftedSelbergLocalOriginal s p)) := by
      rw [shiftedSelbergLocalNumerator_identity s hp]
    _ = additiveBivariateConvolution
          (additiveBivariateConvolution (shiftedSelbergLocalDiagonal s p)
            (shiftedSelbergLocalDenominator s p))
          (shiftedSelbergLocalOriginal s p) := by
      rw [additiveBivariateConvolution_assoc]
    _ = additiveBivariateConvolution additiveBivariateOne
          (shiftedSelbergLocalOriginal s p) := by
      rw [shiftedSelbergLocalDiagonal_convolution_denominator s hp]
    _ = shiftedSelbergLocalOriginal s p := additiveBivariateConvolution_one_left _

/-- The shifted correction and principal factor recover the literal gcd kernel. -/
theorem shiftedSelbergCorrection_convolution_principal (s : ℝ) (m n : ℕ) :
    bivariateDirichletConvolution (shiftedSelbergCorrectionCoeff s)
      (shiftedSelbergPrincipal s) m n = shiftedSelbergOriginal s m n := by
  by_cases hm : m = 0
  · subst m
    simp [bivariateDirichletConvolution, shiftedSelbergOriginal, selbergOriginalCoeff]
  by_cases hn : n = 0
  · subst n
    simp [bivariateDirichletConvolution, shiftedSelbergOriginal, selbergOriginalCoeff]
  apply BivariateMultiplicative.eq_of_prime_pow_eq
    ((bivariateMultiplicative_shiftedSelbergCorrectionCoeff s).convolution
      (bivariateMultiplicative_shiftedSelbergPrincipal s))
    (bivariateMultiplicative_shiftedSelbergOriginal s) _
    (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
  intro p hp i j
  rw [bivariateDirichletConvolution_prime_pow _ _ hp]
  exact congrFun (congrFun (shiftedSelbergLocalCorrection_convolution_principal s hp) i) j

end GaloisForLFunctions.MultiscaleMollifiedZetaField
