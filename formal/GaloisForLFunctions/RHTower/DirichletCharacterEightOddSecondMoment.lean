/-
# Finite second moments for the conductor-eight/odd quadratic characters

Both explicit conductor-eight local quadratic characters are handled through
one finite tag.  Every result is a closed statement about the constructed CRT
characters; no conductor, primitivity, or density premise is used.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterEightOddCRT
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMomentDivisorBound

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The two explicit conductor-eight local quadratic characters. -/
inductive EightQuadraticKind where
  | first
  | second
deriving DecidableEq

/-- The selected explicit conductor-eight character. -/
def eightQuadraticLocal : EightQuadraticKind → ZMod 8 → ℂ
  | .first => quadraticCharacterEight
  | .second => quadraticCharacterEightPrime

/-- The selected conductor-eight/odd composite character. -/
def eightOddQuadraticCharacterOfKind (κ : EightQuadraticKind) (P : OddPrimeFamily I)
    (x : ZMod (eightOddModulus P)) : ℂ :=
  eightOddQuadraticCharacter (eightQuadraticLocal κ) P x

/-- Every selected explicit local character is real-valued. -/
theorem eightQuadraticLocal_star (κ : EightQuadraticKind) (x : ZMod 8) :
    star (eightQuadraticLocal κ x) = eightQuadraticLocal κ x := by
  cases κ
  · rw [eightQuadraticLocal, MulChar.star_apply', quadraticCharacterEight_isQuadratic.inv]
  · rw [eightQuadraticLocal, MulChar.star_apply', quadraticCharacterEightPrime_isQuadratic.inv]

/-- Every selected conductor-eight/odd composite character is real-valued. -/
theorem eightOddQuadraticCharacterOfKind_star [DecidableEq I] (κ : EightQuadraticKind)
    (P : OddPrimeFamily I) (x : ZMod (eightOddModulus P)) :
    star (eightOddQuadraticCharacterOfKind κ P x) = eightOddQuadraticCharacterOfKind κ P x := by
  simp only [eightOddQuadraticCharacterOfKind, eightOddQuadraticCharacter, star_mul,
    eightQuadraticLocal_star, quadraticCharacter_star]
  ring

/-- Exact complete correlation gcd bound, uniformly over the two explicit conductor-eight characters. -/
theorem eightOdd_quadraticCharacterOfKind_shiftCorrelation_norm_le_gcd [DecidableEq I]
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (k l : ℤ) :
    ‖∑ x : ZMod (eightOddModulus P),
      eightOddQuadraticCharacterOfKind κ P (x + (k : ZMod (eightOddModulus P))) *
        eightOddQuadraticCharacterOfKind κ P (x + (l : ZMod (eightOddModulus P)))‖ ≤
      (eightOddModulus P).gcd (l - k).natAbs := by
  cases κ
  · simpa only [eightOddQuadraticCharacterOfKind, eightQuadraticLocal,
      eightOddQuadraticCharacterEight] using
      eightOdd_quadraticCharacterEight_shiftCorrelation_norm_le_gcd_exact P k l
  · simpa only [eightOddQuadraticCharacterOfKind, eightQuadraticLocal,
      eightOddQuadraticCharacterEightPrime] using
      eightOdd_quadraticCharacterEightPrime_shiftCorrelation_norm_le_gcd_exact P k l

/-- Incomplete shift sum for the selected conductor-eight/odd composite character. -/
def eightOddQuadraticIntervalShiftSum [DecidableEq I] (κ : EightQuadraticKind)
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) (x : ZMod (eightOddModulus P)) : ℂ :=
  ∑ k ∈ Finset.Icc 1 M,
    b k * eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P)))

/-- Exact expansion of the finite second moment for either conductor-eight/odd composite. -/
theorem eightOdd_quadratic_intervalShiftSum_energy [DecidableEq I] (κ : EightQuadraticKind)
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    (∑ x : ZMod (eightOddModulus P),
      (Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) : ℂ)) =
      ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod (eightOddModulus P),
          eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
            eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P))) := by
  have hnorm : ∀ x : ZMod (eightOddModulus P),
      (Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) : ℂ) =
        eightOddQuadraticIntervalShiftSum κ P M b x *
          star (eightOddQuadraticIntervalShiftSum κ P M b x) := by
    intro x
    exact (Complex.mul_conj _).symm
  rw [Finset.sum_congr rfl fun x hx => hnorm x]
  simp only [eightOddQuadraticIntervalShiftSum]
  simp_rw [star_sum, Finset.sum_mul_sum, star_mul, eightOddQuadraticCharacterOfKind_star]
  have hreorder (x : ZMod (eightOddModulus P)) (k l : ℕ) :
      b k * eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
          (eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P))) *
            star (b l)) =
        (b k * star (b l)) *
          (eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
            eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P)))) := by
    ring
  simp_rw [hreorder]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-- The finite second moment for either conductor-eight composite is bounded by its literal
positive gcd kernel. -/
theorem eightOdd_quadratic_intervalShiftSum_normSq_le_gcdKernel [DecidableEq I]
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (eightOddModulus P),
      Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) ≤
      gcdKernelMoment (eightOddModulus P - 1) M b := by
  have henergy := eightOdd_quadratic_intervalShiftSum_energy κ P M b
  have hnonneg : 0 ≤ ∑ x : ZMod (eightOddModulus P),
      Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) :=
    Finset.sum_nonneg fun x hx => Complex.normSq_nonneg _
  have hmodpos : 0 < eightOddModulus P :=
    Nat.pos_of_ne_zero (eightOddModulus_neZero P).out
  have hmod : eightOddModulus P - 1 + 1 = eightOddModulus P :=
    Nat.sub_add_cancel hmodpos
  calc
    ∑ x : ZMod (eightOddModulus P),
        Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x)
        = ‖(↑(∑ x : ZMod (eightOddModulus P),
            Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod (eightOddModulus P),
          eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
            eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P)))‖ := by
      have hcast : (↑(∑ x : ZMod (eightOddModulus P),
          Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x)) : ℂ) =
          ∑ x : ZMod (eightOddModulus P),
            (Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) : ℂ) := by
        exact_mod_cast rfl
      rw [hcast, henergy]
    _ ≤ ∑ k ∈ Finset.Icc 1 M, ‖∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod (eightOddModulus P),
          eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
            eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P)))‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
        ‖b k * star (b l) * ∑ x : ZMod (eightOddModulus P),
          eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
            eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P)))‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
        ‖b k‖ * ‖b l‖ * ‖∑ x : ZMod (eightOddModulus P),
          eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
            eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P)))‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      simp only [norm_mul, norm_star]
    _ ≤ gcdKernelMoment (eightOddModulus P - 1) M b := by
      rw [gcdKernelMoment]
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      rw [hmod]
      have hcorr : ‖∑ x : ZMod (eightOddModulus P),
          eightOddQuadraticCharacterOfKind κ P (x + ((k : ℤ) : ZMod (eightOddModulus P))) *
            eightOddQuadraticCharacterOfKind κ P (x + ((l : ℤ) : ZMod (eightOddModulus P)))‖ ≤
          (eightOddModulus P).gcd (Nat.dist k l) := by
        simpa only [natAbs_intCast_sub_eq_natDist] using
          eightOdd_quadraticCharacterOfKind_shiftCorrelation_norm_le_gcd κ P (k : ℤ) (l : ℤ)
      nlinarith [mul_le_mul_of_nonneg_left hcorr
        (mul_nonneg (norm_nonneg (b k)) (norm_nonneg (b l)))]

/-- Divisor-power form of the finite second moment for either conductor-eight composite. -/
theorem eightOdd_quadratic_intervalShiftSum_normSq_le_divisorRpow [DecidableEq I]
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ x : ZMod (eightOddModulus P),
      Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) ≤
      ((M : ℝ) * (Sieve.divisorBoundConst ε * (eightOddModulus P : ℝ) ^ ε) +
        (eightOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
  have hmodpos : 0 < eightOddModulus P :=
    Nat.pos_of_ne_zero (eightOddModulus_neZero P).out
  have hmod : eightOddModulus P - 1 + 1 = eightOddModulus P :=
    Nat.sub_add_cancel hmodpos
  have hmodR : ((eightOddModulus P - 1 : ℕ) : ℝ) + 1 = (eightOddModulus P : ℝ) := by
    exact_mod_cast hmod
  have hdiv : ((eightOddModulus P).divisors.card : ℝ) ≤
      Sieve.divisorBoundConst ε * (eightOddModulus P : ℝ) ^ ε :=
    Sieve.card_divisors_le_rpow hε (eightOddModulus_neZero P).out
  have henergy_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ gcdKernelMoment (eightOddModulus P - 1) M b :=
      eightOdd_quadratic_intervalShiftSum_normSq_le_gcdKernel κ P M b
    _ ≤ (∑ e ∈ (eightOddModulus P - 1 + 1).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
      exact gcdKernelMoment_le (eightOddModulus P - 1) M b
    _ ≤ ((M : ℝ) * ((eightOddModulus P - 1 + 1).divisors.card : ℝ) +
        ((eightOddModulus P - 1 : ℕ) : ℝ) + 1) *
          ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (by
          simpa only [add_assoc] using
            divisor_totient_coefficient_le (eightOddModulus P - 1) M)
        henergy_nonneg
    _ = ((M : ℝ) * ((eightOddModulus P).divisors.card : ℝ) +
        (eightOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
      have hcoeff :
          (M : ℝ) * ((eightOddModulus P).divisors.card : ℝ) +
              ((eightOddModulus P - 1 : ℕ) : ℝ) + 1 =
            (M : ℝ) * ((eightOddModulus P).divisors.card : ℝ) +
              (eightOddModulus P : ℝ) := by
        linarith [hmodR]
      rw [hmod, hcoeff]
    _ ≤ ((M : ℝ) * (Sieve.divisorBoundConst ε * (eightOddModulus P : ℝ) ^ ε) +
        (eightOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · simpa [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg M))
            (eightOddModulus P : ℝ)
      · exact henergy_nonneg

end OddPrimeFamily
end RHTower
