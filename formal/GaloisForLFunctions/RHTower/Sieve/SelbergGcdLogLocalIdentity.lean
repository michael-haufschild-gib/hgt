import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionLogNumerator
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogPrincipalCollapse
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionLogCoefficient

/-!
# The local gcd-logarithmic identity

At every prime the four local Euler factors satisfy

`c^{log} = corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫`.

Clearing the denominator `D = 1 − XY/p` reduces this to two facts already available — the numerator
identity `corr^{log} ∗ N = (log p/p²)XY(X+Y−2XY)` and the diagonal identity
`diag^{log} ∗ D = (log p·XY/p) ∗ diag` — together with the finite polynomial identity
`c + (X+Y−2XY)/p = D`.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Local coefficients of the logarithmic diagonal weight. -/
def selbergLocalDiagonalLogReciprocal (p i j : ℕ) : ℝ :=
  selbergDiagonalLogReciprocalCoeff (p ^ i) (p ^ j)

/-- Local coefficients of the gcd-logarithmic principal factor. -/
def selbergLocalGcdLogPrincipal (p i j : ℕ) : ℝ :=
  selbergGcdLogPrincipalCoeff (p ^ i) (p ^ j)

/-- Local coefficients of the differentiated correction. -/
def selbergLocalCorrectionLog (p i j : ℕ) : ℝ :=
  selbergEulerCorrectionLogCoeff (p ^ i) (p ^ j)

/-- Local coefficients of the gcd-logarithmic original weight. -/
def selbergLocalOriginalGcdLog (p i j : ℕ) : ℝ :=
  selbergOriginalGcdLogCoeff (p ^ i) (p ^ j)

theorem selbergMoebiusReciprocalCoeff_prime_pow_eq {p : ℕ} (hp : p.Prime) (i : ℕ) :
    selbergMoebiusReciprocalCoeff (p ^ i) = localMoebiusFactor p i := by
  match i with
  | 0 => simp [localMoebiusFactor]
  | 1 =>
      rw [pow_one, localMoebiusFactor, if_neg (by omega), if_pos rfl,
        selbergMoebiusReciprocalCoeff,
        ArithmeticFunction.moebius_apply_prime hp]
      push_cast
      rw [neg_div, one_div]
  | (k + 2) =>
      rw [localMoebiusFactor, if_neg (by omega), if_neg (by omega),
        selbergMoebiusReciprocalCoeff_prime_pow_two_add hp]

theorem localMoebiusPairFactor_eq {p : ℕ} (hp : p.Prime) :
    localMoebiusPairFactor p = selbergLocalMoebiusReciprocalPair p := by
  funext i j
  rw [localMoebiusPairFactor, selbergLocalMoebiusReciprocalPair,
    selbergMoebiusReciprocalCoeff_prime_pow_eq hp,
    selbergMoebiusReciprocalCoeff_prime_pow_eq hp]

theorem selbergLocalGcdLogPrincipal_eq_convolution {p : ℕ} (hp : p.Prime) :
    selbergLocalGcdLogPrincipal p =
      additiveBivariateConvolution (selbergLocalDiagonalLogReciprocal p)
        (selbergLocalMoebiusReciprocalPair p) := by
  funext i j
  rw [selbergLocalGcdLogPrincipal, selbergGcdLogPrincipalCoeff,
    bivariateDirichletConvolution_prime_pow _ _ hp]
  rfl

theorem selbergLocalCorrectionLog_eq {p : ℕ} (hp : p.Prime) :
    selbergLocalCorrectionLog p = selbergCorrectionLogLocal p := by
  funext i j
  rw [selbergLocalCorrectionLog,
    selbergEulerCorrectionLogCoeff_prime_pow hp]

theorem selbergLocalDiagonalLogReciprocal_eq {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergLocalDiagonalLogReciprocal p i j =
      if i = j then (i : ℝ) * Real.log (p : ℝ) / (p : ℝ) ^ i else 0 := by
  have hpow : p ^ i = p ^ j ↔ i = j :=
    (Nat.pow_right_injective hp.two_le).eq_iff
  rw [selbergLocalDiagonalLogReciprocal, selbergDiagonalLogReciprocalCoeff]
  by_cases hij : i = j
  · rw [if_pos (by rw [hij]), if_pos hij, hij]
    push_cast
    rw [Real.log_pow]
  · rw [if_neg (by rw [hpow]; exact hij), if_neg hij]

theorem selbergLocalDiagonalReciprocal_eq {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    selbergLocalDiagonalReciprocal p i j =
      if i = j then 1 / (p : ℝ) ^ i else 0 := by
  have hpow : p ^ i = p ^ j ↔ i = j :=
    (Nat.pow_right_injective hp.two_le).eq_iff
  have hne : (p : ℕ) ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [selbergLocalDiagonalReciprocal, selbergDiagonalReciprocalCoeff]
  by_cases hij : i = j
  · rw [if_pos (by rw [hij]), if_pos hij, reciprocalNatArithmetic_apply hne, hij]
    push_cast
    ring
  · rw [if_neg (by rw [hpow]; exact hij), if_neg hij]

/-- **The diagonal identity `diag^{log} ∗ D = (log p·XY/p) ∗ diag`.** -/
theorem additiveBivariateConvolution_diagonalLog_eulerDenominator
    {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (selbergLocalDiagonalLogReciprocal p)
        (selbergLocalEulerDenominator p) =
      additiveBivariateConvolution
        (additiveBivariateDiagonalMonomial (Real.log (p : ℝ) / (p : ℝ)))
        (selbergLocalDiagonalReciprocal p) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  change additiveBivariateConvolution (selbergLocalDiagonalLogReciprocal p)
      (fun i j => additiveBivariateOne i j -
        additiveBivariateDiagonalMonomial (1 / (p : ℝ)) i j) = _
  rw [additiveBivariateConvolution_sub_right,
    additiveBivariateConvolution_one_right,
    additiveBivariateConvolution_diagonalMonomial_right,
    additiveBivariateConvolution_diagonalMonomial_left]
  funext i j
  show selbergLocalDiagonalLogReciprocal p i j -
      additiveBivariateDiagonalShift (1 / (p : ℝ))
        (selbergLocalDiagonalLogReciprocal p) i j =
    additiveBivariateDiagonalShift (Real.log (p : ℝ) / (p : ℝ))
      (selbergLocalDiagonalReciprocal p) i j
  rw [additiveBivariateDiagonalShift, additiveBivariateDiagonalShift]
  by_cases h0 : i = 0 ∨ j = 0
  · rw [if_pos h0, if_pos h0, sub_zero,
      selbergLocalDiagonalLogReciprocal_eq hp]
    rcases h0 with h | h
    · subst h
      by_cases hj : (0 : ℕ) = j
      · rw [if_pos hj]
        simp
      · rw [if_neg hj]
    · subst h
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl]
        norm_num
      · rw [if_neg (by omega)]
  · rw [not_or] at h0
    obtain ⟨hi0, hj0⟩ := h0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    rw [if_neg (by omega), if_neg (by omega)]
    rw [selbergLocalDiagonalLogReciprocal_eq hp,
      selbergLocalDiagonalLogReciprocal_eq hp,
      selbergLocalDiagonalReciprocal_eq hp]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      simp only [pow_succ]
      push_cast
      field_simp
      ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring

theorem gcd_prime_pow_eq_pow_min {p i j : ℕ} :
    Nat.gcd (p ^ i) (p ^ j) = p ^ min i j := by
  rcases le_total i j with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow p h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow p h)]

theorem selbergLocalOriginalGcdLog_eq {p : ℕ} (hp : p.Prime) :
    selbergLocalOriginalGcdLog p = fun i j =>
      if i = 1 ∧ j = 1 then Real.log (p : ℝ) / (p : ℝ) else 0 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  funext i j
  rw [selbergLocalOriginalGcdLog, selbergOriginalGcdLogCoeff,
    gcd_prime_pow_eq_pow_min]
  have hlog : Real.log (((p ^ min i j : ℕ) : ℝ)) =
      ((min i j : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlog, show selbergOriginalCoeff (p ^ i) (p ^ j) =
      selbergLocalOriginalPolynomial p i j from
    congrFun (congrFun (selbergLocalOriginal_eq_polynomial hp) i) j]
  match i, j with
  | 0, j => simp [selbergLocalOriginalPolynomial]
  | (i + 1), 0 => simp [selbergLocalOriginalPolynomial]
  | 1, 1 =>
      rw [selbergLocalOriginalPolynomial, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
      norm_num
      field_simp
  | 1, (l + 2) =>
      rw [selbergLocalOriginalPolynomial, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
  | (k + 2), (l + 1) =>
      rw [selbergLocalOriginalPolynomial, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring

/-- **The finite identity `(log p·XY/p) ∗ c + numerator = c^{log} ∗ D`.** -/
theorem selbergLocalGcdLog_denominator_identity {p : ℕ} (hp : p.Prime) :
    (fun i j => additiveBivariateConvolution
        (additiveBivariateDiagonalMonomial (Real.log (p : ℝ) / (p : ℝ)))
        (selbergLocalOriginal p) i j + selbergCorrectionLogNumerator p i j) =
      additiveBivariateConvolution (selbergLocalOriginalGcdLog p)
        (selbergLocalEulerDenominator p) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change (fun i j => additiveBivariateConvolution
      (additiveBivariateDiagonalMonomial (Real.log (p : ℝ) / (p : ℝ)))
      (selbergLocalOriginal p) i j + selbergCorrectionLogNumerator p i j) =
    additiveBivariateConvolution (selbergLocalOriginalGcdLog p)
      (fun i j => additiveBivariateOne i j -
        additiveBivariateDiagonalMonomial (1 / (p : ℝ)) i j)
  rw [additiveBivariateConvolution_sub_right,
    additiveBivariateConvolution_one_right,
    additiveBivariateConvolution_diagonalMonomial_right,
    additiveBivariateConvolution_diagonalMonomial_left]
  funext i j
  show additiveBivariateDiagonalShift (Real.log (p : ℝ) / (p : ℝ))
        (selbergLocalOriginal p) i j + selbergCorrectionLogNumerator p i j =
    selbergLocalOriginalGcdLog p i j -
      additiveBivariateDiagonalShift (1 / (p : ℝ))
        (selbergLocalOriginalGcdLog p) i j
  rw [selbergLocalOriginal_eq_polynomial hp, selbergLocalOriginalGcdLog_eq hp]
  match i, j with
  | 0, j =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator]
  | (i + 1), 0 =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator]
  | 1, 1 =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator,
        selbergLocalOriginalPolynomial]
  | 1, 2 =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator,
        selbergLocalOriginalPolynomial]
      field_simp
      ring
  | 1, (l + 3) =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator,
        selbergLocalOriginalPolynomial]
  | 2, 1 =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator,
        selbergLocalOriginalPolynomial]
      field_simp
      ring
  | 2, 2 =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator,
        selbergLocalOriginalPolynomial]
      field_simp
      ring
  | 2, (l + 3) =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator,
        selbergLocalOriginalPolynomial]
  | (k + 3), (l + 1) =>
      simp [additiveBivariateDiagonalShift, selbergCorrectionLogNumerator,
        selbergLocalOriginalPolynomial]

theorem additiveBivariateConvolution_add_left (f g h : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution (fun i j => f i j + g i j) h =
      fun i j => additiveBivariateConvolution f h i j +
        additiveBivariateConvolution g h i j := by
  funext i j
  rw [additiveBivariateConvolution, additiveBivariateConvolution,
    additiveBivariateConvolution, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- **The local gcd-logarithmic identity.** -/
theorem additiveBivariateConvolution_localGcdLog_identity {p : ℕ} (hp : p.Prime) :
    (fun i j => additiveBivariateConvolution (selbergLocalCorrection p)
        (selbergLocalGcdLogPrincipal p) i j +
      additiveBivariateConvolution (selbergCorrectionLogLocal p)
        (selbergLocalPrincipal p) i j) =
      selbergLocalOriginalGcdLog p := by
  set D := selbergLocalEulerDenominator p with hD
  set dg := selbergLocalDiagonalReciprocal p with hdg
  set mp := selbergLocalMoebiusReciprocalPair p with hmp
  set dl := selbergLocalDiagonalLogReciprocal p with hdl
  set M := additiveBivariateDiagonalMonomial (Real.log (p : ℝ) / (p : ℝ)) with hM
  have hdgD : additiveBivariateConvolution dg D = additiveBivariateOne :=
    additiveBivariateConvolution_localDiagonal_eulerDenominator hp
  have hDdg : additiveBivariateConvolution D dg = additiveBivariateOne := by
    rw [additiveBivariateConvolution_comm]
    exact hdgD
  have hPD : additiveBivariateConvolution (selbergLocalPrincipal p) D = mp := by
    rw [selbergLocalPrincipal_eq_convolution hp, additiveBivariateConvolution_assoc,
      additiveBivariateConvolution_comm mp D, ← additiveBivariateConvolution_assoc,
      hdgD, additiveBivariateConvolution_one_left]
  have hPlogD : additiveBivariateConvolution (selbergLocalGcdLogPrincipal p) D =
      additiveBivariateConvolution M (selbergLocalPrincipal p) := by
    rw [selbergLocalGcdLogPrincipal_eq_convolution hp,
      additiveBivariateConvolution_assoc,
      additiveBivariateConvolution_comm mp D, ← additiveBivariateConvolution_assoc,
      additiveBivariateConvolution_diagonalLog_eulerDenominator hp,
      additiveBivariateConvolution_assoc,
      selbergLocalPrincipal_eq_convolution hp]
  have hstep : additiveBivariateConvolution
      (fun i j => additiveBivariateConvolution (selbergLocalCorrection p)
          (selbergLocalGcdLogPrincipal p) i j +
        additiveBivariateConvolution (selbergCorrectionLogLocal p)
          (selbergLocalPrincipal p) i j) D =
      additiveBivariateConvolution (selbergLocalOriginalGcdLog p) D := by
    rw [additiveBivariateConvolution_add_left]
    have h1 : additiveBivariateConvolution
        (additiveBivariateConvolution (selbergLocalCorrection p)
          (selbergLocalGcdLogPrincipal p)) D =
        additiveBivariateConvolution M (selbergLocalOriginal p) := by
      rw [additiveBivariateConvolution_assoc, hPlogD,
        ← additiveBivariateConvolution_assoc,
        additiveBivariateConvolution_comm (selbergLocalCorrection p) M,
        additiveBivariateConvolution_assoc,
        additiveBivariateConvolution_localCorrection_principal hp]
    have h2 : additiveBivariateConvolution
        (additiveBivariateConvolution (selbergCorrectionLogLocal p)
          (selbergLocalPrincipal p)) D =
        selbergCorrectionLogNumerator p := by
      rw [additiveBivariateConvolution_assoc, hPD, hmp,
        ← localMoebiusPairFactor_eq hp]
      funext i j
      exact additiveBivariateConvolution_selbergCorrectionLogLocal_moebius hp.pos i j
    change additiveBivariateConvolution
        (additiveBivariateConvolution (selbergLocalCorrection p)
          (selbergLocalGcdLogPrincipal p)) D +
      additiveBivariateConvolution
        (additiveBivariateConvolution (selbergCorrectionLogLocal p)
          (selbergLocalPrincipal p)) D = _
    rw [h1, h2]
    exact selbergLocalGcdLog_denominator_identity hp
  calc
    (fun i j => additiveBivariateConvolution (selbergLocalCorrection p)
        (selbergLocalGcdLogPrincipal p) i j +
      additiveBivariateConvolution (selbergCorrectionLogLocal p)
        (selbergLocalPrincipal p) i j)
        = additiveBivariateConvolution
            (fun i j => additiveBivariateConvolution (selbergLocalCorrection p)
              (selbergLocalGcdLogPrincipal p) i j +
              additiveBivariateConvolution (selbergCorrectionLogLocal p)
                (selbergLocalPrincipal p) i j) additiveBivariateOne :=
          (additiveBivariateConvolution_one_right _).symm
    _ = additiveBivariateConvolution
          (fun i j => additiveBivariateConvolution (selbergLocalCorrection p)
            (selbergLocalGcdLogPrincipal p) i j +
            additiveBivariateConvolution (selbergCorrectionLogLocal p)
              (selbergLocalPrincipal p) i j)
          (additiveBivariateConvolution D dg) := by rw [hDdg]
    _ = additiveBivariateConvolution
          (additiveBivariateConvolution
            (fun i j => additiveBivariateConvolution (selbergLocalCorrection p)
              (selbergLocalGcdLogPrincipal p) i j +
              additiveBivariateConvolution (selbergCorrectionLogLocal p)
                (selbergLocalPrincipal p) i j) D) dg :=
          (additiveBivariateConvolution_assoc _ _ _).symm
    _ = additiveBivariateConvolution
          (additiveBivariateConvolution (selbergLocalOriginalGcdLog p) D) dg := by
          rw [hstep]
    _ = additiveBivariateConvolution (selbergLocalOriginalGcdLog p)
          (additiveBivariateConvolution D dg) :=
          additiveBivariateConvolution_assoc _ _ _
    _ = selbergLocalOriginalGcdLog p := by
          rw [hDdg, additiveBivariateConvolution_one_right]

end

end RHTower.Sieve
