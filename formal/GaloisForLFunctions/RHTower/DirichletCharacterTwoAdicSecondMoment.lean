/-
# Level-four/odd quadratic-character interval-energy expansion

This is the coefficient-energy bridge for the level-four/odd CRT character.
It exposes the exact complete correlations that the already-proved finite
gcd-kernel and divisor/Cauchy machinery must bound next.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicCRT
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMoment

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The level-four complex quadratic character is real-valued. -/
theorem quadraticCharacterFour_star (x : ZMod 4) :
    star (quadraticCharacterFour x) = quadraticCharacterFour x := by
  rw [MulChar.star_apply', quadraticCharacterFour_isQuadratic.inv]

/-- The level-four/odd CRT character is real-valued. -/
theorem fourOddQuadraticCharacter_star [DecidableEq I]
    (P : OddPrimeFamily I) (x : ZMod (fourOddModulus P)) :
    star (fourOddQuadraticCharacter P x) = fourOddQuadraticCharacter P x := by
  simp only [fourOddQuadraticCharacter, star_mul, quadraticCharacterFour_star,
    quadraticCharacter_star]
  ring

/-- Incomplete shift sum for the constructed level-four/odd CRT character. -/
def fourOddQuadraticIntervalShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (M : ℕ) (b : ℕ → ℂ) (x : ZMod (fourOddModulus P)) : ℂ :=
  ∑ k ∈ Finset.Icc 1 M,
    b k * fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P)))

/-- Exact expansion of the incomplete level-four/odd second moment into its complete
integer-shift correlations. -/
theorem fourOdd_quadratic_intervalShiftSum_energy [DecidableEq I] (P : OddPrimeFamily I)
    (M : ℕ) (b : ℕ → ℂ) :
    (∑ x : ZMod (fourOddModulus P),
      (Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) : ℂ)) =
      ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod (fourOddModulus P),
          fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
            fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P))) := by
  have hnorm : ∀ x : ZMod (fourOddModulus P),
      (Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) : ℂ) =
        fourOddQuadraticIntervalShiftSum P M b x *
          star (fourOddQuadraticIntervalShiftSum P M b x) := by
    intro x
    exact (Complex.mul_conj _).symm
  rw [Finset.sum_congr rfl fun x hx => hnorm x]
  simp only [fourOddQuadraticIntervalShiftSum]
  simp_rw [star_sum, Finset.sum_mul_sum, star_mul, fourOddQuadraticCharacter_star]
  have hreorder (x : ZMod (fourOddModulus P)) (k l : ℕ) :
      b k * fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
          (fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P))) * star (b l)) =
        (b k * star (b l)) *
          (fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
            fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P)))) := by
    ring
  simp_rw [hreorder]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-- The incomplete level-four/odd second moment is bounded by four times the literal positive
gcd kernel.  This combines the closed CRT correlation bound with the finite coefficient-energy
expansion, with no analytic hypothesis. -/
theorem fourOdd_quadratic_intervalShiftSum_normSq_le_gcdKernel [DecidableEq I]
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (fourOddModulus P),
      Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) ≤
      4 * gcdKernelMoment (fourOddModulus P - 1) M b := by
  have henergy := fourOdd_quadratic_intervalShiftSum_energy P M b
  have hnonneg : 0 ≤ ∑ x : ZMod (fourOddModulus P),
      Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) :=
    Finset.sum_nonneg fun x hx => Complex.normSq_nonneg _
  have hmodpos : 0 < fourOddModulus P :=
    Nat.pos_of_ne_zero (fourOddModulus_neZero P).out
  have hmod : fourOddModulus P - 1 + 1 = fourOddModulus P :=
    Nat.sub_add_cancel hmodpos
  calc
    ∑ x : ZMod (fourOddModulus P),
        Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x)
        = ‖(↑(∑ x : ZMod (fourOddModulus P),
            Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod (fourOddModulus P),
          fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
            fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P)))‖ := by
      have hcast : (↑(∑ x : ZMod (fourOddModulus P),
          Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x)) : ℂ) =
          ∑ x : ZMod (fourOddModulus P),
            (Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) : ℂ) := by
        exact_mod_cast rfl
      rw [hcast, henergy]
    _ ≤ ∑ k ∈ Finset.Icc 1 M, ‖∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod (fourOddModulus P),
          fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
            fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P)))‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
        ‖b k * star (b l) * ∑ x : ZMod (fourOddModulus P),
          fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
            fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P)))‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
        ‖b k‖ * ‖b l‖ * ‖∑ x : ZMod (fourOddModulus P),
          fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
            fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P)))‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      simp only [norm_mul, norm_star]
    _ ≤ 4 * gcdKernelMoment (fourOddModulus P - 1) M b := by
      rw [gcdKernelMoment, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l hl
      rw [hmod]
      have hcorr : ‖∑ x : ZMod (fourOddModulus P),
          fourOddQuadraticCharacter P (x + ((k : ℤ) : ZMod (fourOddModulus P))) *
            fourOddQuadraticCharacter P (x + ((l : ℤ) : ZMod (fourOddModulus P)))‖ ≤
          4 * (fourOddModulus P).gcd (Nat.dist k l) := by
        simpa only [natAbs_intCast_sub_eq_natDist] using
          fourOdd_quadratic_shiftCorrelation_norm_le_gcd P (k : ℤ) (l : ℤ)
      nlinarith [mul_le_mul_of_nonneg_left hcorr
        (mul_nonneg (norm_nonneg (b k)) (norm_nonneg (b l)))]

/-- Exact divisor/totient form of the level-four/odd second moment.  The factor four is the
closed contribution of the conductor-four local character; the coefficient estimate itself is
the same finite divisor/Cauchy argument used for the odd CRT family. -/
theorem fourOdd_quadratic_intervalShiftSum_normSq_le_divisor [DecidableEq I]
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (fourOddModulus P),
      Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) ≤
      4 * ((∑ e ∈ (fourOddModulus P).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) := by
  have hmodpos : 0 < fourOddModulus P :=
    Nat.pos_of_ne_zero (fourOddModulus_neZero P).out
  have hmod : fourOddModulus P - 1 + 1 = fourOddModulus P :=
    Nat.sub_add_cancel hmodpos
  calc
    _ ≤ 4 * gcdKernelMoment (fourOddModulus P - 1) M b :=
      fourOdd_quadratic_intervalShiftSum_normSq_le_gcdKernel P M b
    _ ≤ 4 * ((∑ e ∈ (fourOddModulus P - 1 + 1).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (gcdKernelMoment_le (fourOddModulus P - 1) M b)
        (by norm_num)
    _ = _ := by rw [hmod]

/-- Literal-divisor-count form of the closed level-four/odd second moment. -/
theorem fourOdd_quadratic_intervalShiftSum_normSq_le_divisorCount [DecidableEq I]
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (fourOddModulus P),
      Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) ≤
      4 * (((M : ℝ) * ((fourOddModulus P).divisors.card : ℝ) +
        (fourOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) := by
  have hmodpos : 0 < fourOddModulus P :=
    Nat.pos_of_ne_zero (fourOddModulus_neZero P).out
  have hmod : fourOddModulus P - 1 + 1 = fourOddModulus P :=
    Nat.sub_add_cancel hmodpos
  have hmodR : ((fourOddModulus P - 1 : ℕ) : ℝ) + 1 = (fourOddModulus P : ℝ) := by
    exact_mod_cast hmod
  have henergy_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ 4 * ((∑ e ∈ (fourOddModulus P).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) :=
      fourOdd_quadratic_intervalShiftSum_normSq_le_divisor P M b
    _ ≤ 4 * (((M : ℝ) * ((fourOddModulus P).divisors.card : ℝ) +
        (fourOddModulus P : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right
          (by
            simpa only [hmod, hmodR] using
              divisor_totient_coefficient_le (fourOddModulus P - 1) M)
          henergy_nonneg
      · norm_num

end OddPrimeFamily
end RHTower
