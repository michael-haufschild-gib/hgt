import GaloisForLFunctions.RHTower.Sieve.BivariateDirichletPrimePower

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

def selbergLocalAmplitudePair (p i j : ℕ) : ℝ :=
  reciprocalMoebiusAmplitude (p ^ i) * reciprocalMoebiusAmplitude (p ^ j)

def selbergLocalMoebiusReciprocalPair (p i j : ℕ) : ℝ :=
  selbergMoebiusReciprocalCoeff (p ^ i) * selbergMoebiusReciprocalCoeff (p ^ j)

def selbergLocalMoebiusPair (p i j : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius (p ^ i) : ℤ) : ℝ)) *
    (((ArithmeticFunction.moebius (p ^ j) : ℤ) : ℝ))

def selbergLocalDiagonalReciprocal (p i j : ℕ) : ℝ :=
  selbergDiagonalReciprocalCoeff (p ^ i) (p ^ j)

def selbergLocalEulerDenominator (p : ℕ) : ℕ → ℕ → ℝ :=
  fun i j => additiveBivariateOne i j -
    additiveBivariateDiagonalMonomial (1 / (p : ℝ)) i j

def selbergLocalCorrection (p i j : ℕ) : ℝ :=
  selbergEulerCorrectionCoeff (p ^ i) (p ^ j)

def selbergLocalPrincipal (p i j : ℕ) : ℝ :=
  selbergPrincipalCoeff (p ^ i) (p ^ j)

def selbergLocalOriginal (p i j : ℕ) : ℝ :=
  selbergOriginalCoeff (p ^ i) (p ^ j)

private theorem selbergLocalAmplitude_convolution_moebiusReciprocal
    {p n : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (n + 1),
      reciprocalMoebiusAmplitude (p ^ k) *
        selbergMoebiusReciprocalCoeff (p ^ (n - k))) =
      (((ArithmeticFunction.moebius (p ^ n) : ℤ) : ℝ)) := by
  rcases n with _ | n
  · simp
  rcases n with _ | t
  · rw [show 1 + 1 = 2 by norm_num]
    norm_num [Finset.sum_range_succ]
    rw [show p = p ^ (0 + 1) by simp,
      reciprocalMoebiusAmplitude_prime_pow_succ hp]
    simp only [zero_add, pow_one, pow_zero]
    rw [
      selbergMoebiusReciprocalCoeff_prime hp,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp [hp0]
    ring
  · let n : ℕ := t + 2
    let f : ℕ → ℝ := fun k => reciprocalMoebiusAmplitude (p ^ k) *
      selbergMoebiusReciprocalCoeff (p ^ (n - k))
    change (∑ k ∈ Finset.range (n + 1), f k) = _
    have hnMem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hnmMem : n - 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hnmErase : n - 1 ∈ (Finset.range (n + 1)).erase n :=
      Finset.mem_erase.mpr ⟨by omega, hnmMem⟩
    calc
      (∑ k ∈ Finset.range (n + 1), f k) =
          (∑ k ∈ (Finset.range (n + 1)).erase n, f k) + f n :=
        (Finset.sum_erase_add _ f hnMem).symm
      _ = ((∑ k ∈ ((Finset.range (n + 1)).erase n).erase (n - 1), f k) +
            f (n - 1)) + f n := by
        rw [Finset.sum_erase_add _ f hnmErase]
      _ = f (n - 1) + f n := by
        rw [show (∑ k ∈ ((Finset.range (n + 1)).erase n).erase (n - 1), f k) = 0 by
          apply Finset.sum_eq_zero
          intro k hk
          have hkRange : k < n + 1 := Finset.mem_range.mp
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
          have hknm : k ≠ n - 1 := Finset.ne_of_mem_erase hk
          have hkn : k ≠ n := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
          have htwo : 2 ≤ n - k := by omega
          have hsub : n - k = (n - k - 2) + 2 := by omega
          dsimp [f]
          rw [hsub, selbergMoebiusReciprocalCoeff_prime_pow_two_add hp]
          ring]
        ring
      _ = (((ArithmeticFunction.moebius (p ^ n) : ℤ) : ℝ)) := by
        have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hnsub : n - (n - 1) = 1 := by dsimp [n]; omega
        have hnn : n - n = 0 := Nat.sub_self n
        have hnmEq : n - 1 = t + 1 := by omega
        dsimp [f]
        rw [hnsub, hnn, pow_one, pow_zero,
          selbergMoebiusReciprocalCoeff_prime hp,
          selbergMoebiusReciprocalCoeff_one,
          hnmEq,
          reciprocalMoebiusAmplitude_prime_pow_succ hp,
          show n = (t + 1) + 1 by rfl,
          reciprocalMoebiusAmplitude_prime_pow_succ hp,
          ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
          if_neg (by omega)]
        push_cast
        field_simp [hpR0]
        have hcancel : (p : ℝ) * (1 / (p : ℝ)) = 1 := by
          field_simp [hpR0]
        rw [pow_succ]
        have hpowCancel : (p : ℝ) * ((1 / (p : ℝ)) ^ t * (1 / (p : ℝ))) =
            (1 / (p : ℝ)) ^ t := by
          calc
            (p : ℝ) * ((1 / (p : ℝ)) ^ t * (1 / (p : ℝ))) =
                (1 / (p : ℝ)) ^ t * ((p : ℝ) * (1 / (p : ℝ))) := by ring
            _ = (1 / (p : ℝ)) ^ t := by rw [hcancel, mul_one]
        rw [hpowCancel]
        ring

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

theorem additiveBivariateConvolution_localAmplitude_moebiusReciprocal
    {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (selbergLocalAmplitudePair p)
      (selbergLocalMoebiusReciprocalPair p) = selbergLocalMoebiusPair p := by
  funext i j
  change additiveBivariateConvolution
      (fun x y => reciprocalMoebiusAmplitude (p ^ x) * reciprocalMoebiusAmplitude (p ^ y))
      (fun x y => selbergMoebiusReciprocalCoeff (p ^ x) *
        selbergMoebiusReciprocalCoeff (p ^ y)) i j = _
  rw [additiveBivariateConvolution_pair,
    selbergLocalAmplitude_convolution_moebiusReciprocal hp,
    selbergLocalAmplitude_convolution_moebiusReciprocal hp]
  rfl

theorem selbergLocalPrincipal_eq_convolution {p : ℕ} (hp : p.Prime) :
    selbergLocalPrincipal p =
      additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
        (selbergLocalMoebiusReciprocalPair p) := by
  funext i j
  rw [selbergLocalPrincipal, selbergPrincipalCoeff,
    bivariateDirichletConvolution_prime_pow _ _ hp]
  rfl

theorem selbergLocalCorrection_eq_one_sub_shift {p : ℕ} (hp : p.Prime) :
    selbergLocalCorrection p = fun i j =>
      additiveBivariateOne i j -
        additiveBivariateConvolution
          (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
          (selbergLocalAmplitudePair p) i j := by
  rw [additiveBivariateConvolution_diagonalMonomial_left]
  funext i j
  rcases i with _ | i
  · rcases j with _ | j
    · simp [selbergLocalCorrection, additiveBivariateOne,
        additiveBivariateDiagonalShift]
    · simp only [selbergLocalCorrection, pow_zero]
      rw [
        selbergEulerCorrectionCoeff_one_prime_pow_succ hp]
      simp [additiveBivariateOne, additiveBivariateDiagonalShift]
  · rcases j with _ | j
    · simp only [selbergLocalCorrection, pow_zero]
      rw [
        selbergEulerCorrectionCoeff_prime_pow_succ_one hp]
      simp [additiveBivariateOne, additiveBivariateDiagonalShift]
    · rw [selbergLocalCorrection, selbergEulerCorrectionCoeff_prime_pow_succ hp]
      simp only [additiveBivariateOne, Nat.succ_ne_zero, and_self, if_false,
        additiveBivariateDiagonalShift, false_or, if_false, Nat.add_sub_cancel,
        selbergLocalAmplitudePair]
      ring

theorem additiveBivariateConvolution_localDiagonal_eulerDenominator
    {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
      (selbergLocalEulerDenominator p) = additiveBivariateOne := by
  change additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
      (fun i j => additiveBivariateOne i j -
        additiveBivariateDiagonalMonomial (1 / (p : ℝ)) i j) = additiveBivariateOne
  rw [additiveBivariateConvolution_sub_right,
    additiveBivariateConvolution_one_right,
    additiveBivariateConvolution_diagonalMonomial_right]
  funext i j
  rcases i with _ | i
  · rcases j with _ | j
    · simp [selbergLocalDiagonalReciprocal, selbergDiagonalReciprocalCoeff,
        additiveBivariateDiagonalShift, additiveBivariateOne]
    · have hpow : (1 : ℕ) ≠ p ^ (j + 1) := by
        exact ne_of_lt (Nat.one_lt_pow (by omega) hp.one_lt)
      change selbergDiagonalReciprocalCoeff 1 (p ^ (j + 1)) - 0 = 0
      rw [selbergDiagonalReciprocalCoeff, if_neg hpow]
      ring
  · rcases j with _ | j
    · have hpow : p ^ (i + 1) ≠ (1 : ℕ) := by
        exact ne_of_gt (Nat.one_lt_pow (by omega) hp.one_lt)
      change selbergDiagonalReciprocalCoeff (p ^ (i + 1)) 1 - 0 = 0
      rw [selbergDiagonalReciprocalCoeff, if_neg hpow]
      ring
    · by_cases hij : i = j
      · subst j
        have hpi0 : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
        have hpis0 : p ^ (i + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
        simp only [selbergLocalDiagonalReciprocal, selbergDiagonalReciprocalCoeff,
          additiveBivariateDiagonalShift, Nat.succ_ne_zero, false_or, if_false,
          Nat.add_sub_cancel, additiveBivariateOne, and_self]
        simp only [if_true]
        rw [reciprocalNatArithmetic_apply hpi0,
          reciprocalNatArithmetic_apply hpis0]
        push_cast
        have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [pow_succ]
        field_simp [hpR0]
        ring
      · have hpow : p ^ (i + 1) ≠ p ^ (j + 1) := fun he =>
          hij (Nat.add_right_cancel
            ((Nat.pow_right_injective hp.two_le) he))
        have hpowPrev : p ^ i ≠ p ^ j := fun he =>
          hij ((Nat.pow_right_injective hp.two_le) he)
        simp [selbergLocalDiagonalReciprocal, selbergDiagonalReciprocalCoeff,
          additiveBivariateDiagonalShift, additiveBivariateOne, hpow, hpowPrev]

theorem moebius_real_prime_pow {p i : ℕ} (hp : p.Prime) :
    (((ArithmeticFunction.moebius (p ^ i) : ℤ) : ℝ)) =
      if i = 0 then 1 else if i = 1 then -1 else 0 := by
  rcases i with _ | i
  · simp
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    by_cases hi : i + 1 = 1
    · rw [if_pos hi, if_neg (by omega), if_pos hi]
      norm_num
    · rw [if_neg hi, if_neg (by omega), if_neg hi]
      norm_num

private theorem gcd_prime_pow_eq_pow_min' {p i j : ℕ} :
    Nat.gcd (p ^ i) (p ^ j) = p ^ min i j := by
  rcases le_total i j with hij | hji
  · rw [min_eq_left hij, Nat.gcd_eq_left_iff_dvd.mpr (pow_dvd_pow p hij)]
  · rw [min_eq_right hji, Nat.gcd_eq_right_iff_dvd.mpr (pow_dvd_pow p hji)]

def selbergLocalOriginalPolynomial (p i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 1
  else if i = 1 ∧ j = 0 then -(1 / (p : ℝ))
  else if i = 0 ∧ j = 1 then -(1 / (p : ℝ))
  else if i = 1 ∧ j = 1 then 1 / (p : ℝ)
  else 0

theorem selbergLocalOriginal_eq_polynomial {p : ℕ} (hp : p.Prime) :
    selbergLocalOriginal p = selbergLocalOriginalPolynomial p := by
  funext i j
  rw [selbergLocalOriginal, selbergOriginalCoeff, gcd_prime_pow_eq_pow_min',
    moebius_real_prime_pow hp, moebius_real_prime_pow hp]
  rcases i with _ | i
  · rcases j with _ | j
    · simp [selbergLocalOriginalPolynomial]
    · rcases j with _ | j
      · simp [selbergLocalOriginalPolynomial]
        ring
      · simp [selbergLocalOriginalPolynomial]
  · rcases i with _ | i
    · rcases j with _ | j
      · simp [selbergLocalOriginalPolynomial]
        ring
      · rcases j with _ | j
        · have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
          simp [selbergLocalOriginalPolynomial]
          field_simp [hpR0]
        · simp [selbergLocalOriginalPolynomial]
    · simp [selbergLocalOriginalPolynomial]

theorem selbergLocalNumerator_identity {p : ℕ} (hp : p.Prime) :
    (fun i j => selbergLocalMoebiusReciprocalPair p i j -
      additiveBivariateConvolution
        (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
        (selbergLocalMoebiusPair p) i j) =
      additiveBivariateConvolution (selbergLocalEulerDenominator p)
        (selbergLocalOriginal p) := by
  rw [additiveBivariateConvolution_diagonalMonomial_left]
  change (fun i j => selbergLocalMoebiusReciprocalPair p i j -
      additiveBivariateDiagonalShift ((1 / (p : ℝ)) ^ 2)
        (selbergLocalMoebiusPair p) i j) =
    additiveBivariateConvolution
      (fun i j => additiveBivariateOne i j -
        additiveBivariateDiagonalMonomial (1 / (p : ℝ)) i j)
      (selbergLocalOriginal p)
  rw [additiveBivariateConvolution_sub_left,
    additiveBivariateConvolution_one_left,
    additiveBivariateConvolution_diagonalMonomial_left,
    selbergLocalOriginal_eq_polynomial hp]
  funext i j
  have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rcases i with _ | i
  · rcases j with _ | j
    · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
        additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial]
    · rcases j with _ | j
      · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime hp, moebius_real_prime_pow hp]
      · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
          moebius_real_prime_pow hp]
  · rcases i with _ | i
    · rcases j with _ | j
      · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime hp, moebius_real_prime_pow hp]
      · rcases j with _ | j
        · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime hp, moebius_real_prime_pow hp]
          field_simp [hpR0]
          ring
        · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime hp,
            selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
            moebius_real_prime_pow hp]
          field_simp [hpR0]
    · rcases j with _ | j
      · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
          additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
          selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
          moebius_real_prime_pow hp]
      · rcases j with _ | j
        · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime hp,
            selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
            moebius_real_prime_pow hp]
          field_simp [hpR0]
        · simp [selbergLocalMoebiusReciprocalPair, selbergLocalMoebiusPair,
            additiveBivariateDiagonalShift, selbergLocalOriginalPolynomial,
            selbergMoebiusReciprocalCoeff_prime_pow_two_add hp,
            moebius_real_prime_pow hp]
          by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]
          field_simp [hpR0]

theorem additiveBivariateConvolution_localCorrection_principal {p : ℕ}
    (hp : p.Prime) :
    additiveBivariateConvolution (selbergLocalCorrection p)
        (selbergLocalPrincipal p) =
      selbergLocalOriginal p := by
  rw [selbergLocalCorrection_eq_one_sub_shift hp,
    selbergLocalPrincipal_eq_convolution hp,
    additiveBivariateConvolution_sub_left,
    additiveBivariateConvolution_one_left]
  calc
    additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (selbergLocalMoebiusReciprocalPair p) -
        additiveBivariateConvolution
          (additiveBivariateConvolution
            (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
            (selbergLocalAmplitudePair p))
          (additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
            (selbergLocalMoebiusReciprocalPair p)) =
        additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (selbergLocalMoebiusReciprocalPair p) -
        additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (additiveBivariateConvolution
            (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
            (additiveBivariateConvolution (selbergLocalAmplitudePair p)
              (selbergLocalMoebiusReciprocalPair p))) := by
      congr 1
      apply bivariateCoefficientSeries_injective
      simp only [bivariateCoefficientSeries_convolution]
      ring
    _ = additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (selbergLocalMoebiusReciprocalPair p) -
        additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (additiveBivariateConvolution
            (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
            (selbergLocalMoebiusPair p)) := by
      rw [additiveBivariateConvolution_localAmplitude_moebiusReciprocal hp]
    _ = additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (fun i j => selbergLocalMoebiusReciprocalPair p i j -
            additiveBivariateConvolution
              (additiveBivariateDiagonalMonomial ((1 / (p : ℝ)) ^ 2))
              (selbergLocalMoebiusPair p) i j) := by
      rw [additiveBivariateConvolution_sub_right]
      funext i j
      rfl
    _ = additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (additiveBivariateConvolution (selbergLocalEulerDenominator p)
            (selbergLocalOriginal p)) := by
      rw [selbergLocalNumerator_identity hp]
    _ = additiveBivariateConvolution
          (additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
            (selbergLocalEulerDenominator p))
          (selbergLocalOriginal p) := by
      rw [additiveBivariateConvolution_assoc]
    _ = additiveBivariateConvolution additiveBivariateOne
          (selbergLocalOriginal p) := by
      rw [additiveBivariateConvolution_localDiagonal_eulerDenominator hp]
    _ = selbergLocalOriginal p := additiveBivariateConvolution_one_left _

theorem selbergEulerCorrection_convolution_principal_prime_pow
    {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    bivariateDirichletConvolution selbergEulerCorrectionCoeff
        selbergPrincipalCoeff (p ^ i) (p ^ j) =
      selbergOriginalCoeff (p ^ i) (p ^ j) := by
  rw [bivariateDirichletConvolution_prime_pow _ _ hp]
  change additiveBivariateConvolution (selbergLocalCorrection p)
      (selbergLocalPrincipal p) i j = selbergLocalOriginal p i j
  exact congrFun (congrFun
    (additiveBivariateConvolution_localCorrection_principal hp) i) j

/-- Exact Euler-coefficient factorization of the Barban--Vehov quadratic form. -/
theorem selbergEulerCorrection_convolution_principal (m n : ℕ) :
    bivariateDirichletConvolution selbergEulerCorrectionCoeff
        selbergPrincipalCoeff m n =
      selbergOriginalCoeff m n := by
  by_cases hm : m = 0
  · subst m
    simp [bivariateDirichletConvolution, selbergOriginalCoeff]
  by_cases hn : n = 0
  · subst n
    simp [bivariateDirichletConvolution, selbergOriginalCoeff]
  exact BivariateMultiplicative.eq_of_prime_pow_eq
    (bivariateMultiplicative_selbergEulerCorrectionCoeff.convolution
      bivariateMultiplicative_selbergPrincipalCoeff)
    bivariateMultiplicative_selbergOriginalCoeff
    (fun hp i j => selbergEulerCorrection_convolution_principal_prime_pow hp i j)
    (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

end

end RHTower.Sieve
