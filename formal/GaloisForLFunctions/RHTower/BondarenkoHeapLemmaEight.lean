/-
# Bondarenko--Heap Lemma 8: closed quadratic-character second moments

This is the exact finite-window form of Lemma 8 in Bondarenko--Heap,
`Siegel zeros and small gaps between zeros of the Riemann zeta function`
(arXiv:2608.07399).  The source conductor decomposition is
`q = 2^ν Q` for `ν ∈ {0, 2, 3}`.  This module covers its odd square-free
case and identifies both even branches with their fundamental-discriminant
Kronecker symbols before applying the closed finite second-moment estimates.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterFundamentalDiscriminantKronecker
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMomentWindow
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicSecondMomentWindow
import GaloisForLFunctions.RHTower.DirichletCharacterEightOddSecondMomentWindow

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The Lemma-8 window for the level-four fundamental-discriminant family. -/
def fourOddFundamentalKroneckerWindowShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (fourOddModulus P)) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    b n * (evenKroneckerSymbol (fourOddFundamentalDiscriminant P)
      (x + ((A + n : ℕ) : ZMod (fourOddModulus P))).val : ℂ)

/-- The Lemma-8 window for the first level-eight fundamental-discriminant family. -/
def eightOddFundamentalKroneckerWindowShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (eightOddModulus P)) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    b n * (evenKroneckerSymbol (eightOddFundamentalDiscriminant P)
      (x + ((A + n : ℕ) : ZMod (eightOddModulus P))).val : ℂ)

/-- The Lemma-8 window for the second level-eight fundamental-discriminant family. -/
def eightOddPrimeFundamentalKroneckerWindowShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (eightOddModulus P)) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    b n * (evenKroneckerSymbol (eightOddPrimeFundamentalDiscriminant P)
      (x + ((A + n : ℕ) : ZMod (eightOddModulus P))).val : ℂ)

/-- The level-four Kronecker window is exactly its established CRT-character window. -/
theorem fourOddFundamentalKroneckerWindowShiftSum_eq [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (fourOddModulus P)) :
    fourOddFundamentalKroneckerWindowShiftSum P A M b x =
      fourOddQuadraticWindowShiftSum P A M b x := by
  unfold fourOddFundamentalKroneckerWindowShiftSum fourOddQuadraticWindowShiftSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [fourOddQuadraticDirichletCharacter_eq_fundamentalKronecker,
    fourOddQuadraticDirichletCharacter_apply]

/-- The first level-eight Kronecker window is its established first CRT-character window. -/
theorem eightOddFundamentalKroneckerWindowShiftSum_eq [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (eightOddModulus P)) :
    eightOddFundamentalKroneckerWindowShiftSum P A M b x =
      eightOddQuadraticWindowShiftSum .first P A M b x := by
  unfold eightOddFundamentalKroneckerWindowShiftSum eightOddQuadraticWindowShiftSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [eightOddQuadraticDirichletCharacterEight_eq_fundamentalKronecker,
    eightOddQuadraticDirichletCharacterEight_apply]
  rfl

/-- The second level-eight Kronecker window is its established second CRT-character window. -/
theorem eightOddPrimeFundamentalKroneckerWindowShiftSum_eq [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (x : ZMod (eightOddModulus P)) :
    eightOddPrimeFundamentalKroneckerWindowShiftSum P A M b x =
      eightOddQuadraticWindowShiftSum .second P A M b x := by
  unfold eightOddPrimeFundamentalKroneckerWindowShiftSum eightOddQuadraticWindowShiftSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [eightOddQuadraticDirichletCharacterEightPrime_eq_fundamentalKronecker,
    eightOddQuadraticDirichletCharacterEightPrime_apply]
  rfl

/-- Premise-free source-scale form of Lemma 8 for the odd square-free CRT
family, the `ν = 0` conductor branch in the source decomposition. -/
theorem odd_quadratic_windowShiftSum_sourceScale [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (ε : ℝ) :
    ε ≤ 0 ∨ ∃ C : ℝ, 0 < C ∧
      ∑ x : ZMod P.modulus,
        Complex.normSq (quadraticWindowShiftSum P A M b x) ≤
          C * (P.modulus : ℝ) ^ ε * ((P.modulus : ℝ) + M) *
            ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
  by_cases hεnonpos : ε ≤ 0
  · exact Or.inl hεnonpos
  · right
    have hε : 0 < ε := lt_of_not_ge hεnonpos
    have hCpos : 0 < Sieve.divisorBoundConst ε := Sieve.divisorBoundConst_pos hε
    refine ⟨1 + Sieve.divisorBoundConst ε, by linarith, ?_⟩
    have hbase := quadratic_windowShiftSum_normSq_le_divisorRpow P A M b hε
    have hqnat : 1 ≤ P.modulus := Nat.one_le_iff_ne_zero.mpr P.modulus_neZero.out
    have hq : 1 ≤ (P.modulus : ℝ) := by
      exact_mod_cast hqnat
    have hm : 0 ≤ (M : ℝ) := by positivity
    have hC : 0 ≤ Sieve.divisorBoundConst ε := hCpos.le
    have henergy : 0 ≤ ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by positivity
    calc
      _ ≤ ((M : ℝ) * (Sieve.divisorBoundConst ε * (P.modulus : ℝ) ^ ε) +
          (P.modulus : ℝ)) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := hbase
      _ ≤ (1 + Sieve.divisorBoundConst ε) * (P.modulus : ℝ) ^ ε *
          ((P.modulus : ℝ) + M) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
        have hp : 1 ≤ (P.modulus : ℝ) ^ ε := Real.one_le_rpow hq hε.le
        have hp0 : 0 ≤ (P.modulus : ℝ) ^ ε := le_trans (by norm_num) hp
        have hq0 : 0 ≤ (P.modulus : ℝ) := le_trans (by norm_num) hq
        have hqterm : (P.modulus : ℝ) ≤ (P.modulus : ℝ) ^ ε * (P.modulus : ℝ) := by
          nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hp)]
        have hmterm : (M : ℝ) * (Sieve.divisorBoundConst ε * (P.modulus : ℝ) ^ ε) ≤
            (1 + Sieve.divisorBoundConst ε) * (P.modulus : ℝ) ^ ε * (M : ℝ) := by
          nlinarith [mul_nonneg hm hC, mul_nonneg hm (sub_nonneg.mpr hp)]
        have hcoef : (M : ℝ) * (Sieve.divisorBoundConst ε * (P.modulus : ℝ) ^ ε) +
            (P.modulus : ℝ) ≤
            (1 + Sieve.divisorBoundConst ε) * (P.modulus : ℝ) ^ ε *
              ((P.modulus : ℝ) + M) := by
          nlinarith [mul_nonneg (show 0 ≤ 1 + Sieve.divisorBoundConst ε by linarith)
            (mul_nonneg hp0 hq0)]
        exact mul_le_mul_of_nonneg_right hcoef henergy

/-- Premise-free source-scale form of Lemma 8 for every level-four fundamental
discriminant window.  The left alternative records nonpositive exponents; the
right alternative is precisely the usual positive-exponent estimate with its
constant produced internally. -/
theorem fourOdd_fundamentalKronecker_windowShiftSum_sourceScale [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (ε : ℝ) :
    ε ≤ 0 ∨ ∃ C : ℝ, 0 < C ∧
      ∑ x : ZMod (fourOddModulus P),
        Complex.normSq (fourOddFundamentalKroneckerWindowShiftSum P A M b x) ≤
          C * (fourOddModulus P : ℝ) ^ ε * ((fourOddModulus P : ℝ) + M) *
            ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
  by_cases hεnonpos : ε ≤ 0
  · exact Or.inl hεnonpos
  · right
    have hε : 0 < ε := lt_of_not_ge hεnonpos
    have hCpos : 0 < Sieve.divisorBoundConst ε := Sieve.divisorBoundConst_pos hε
    refine ⟨1 + Sieve.divisorBoundConst ε, by linarith, ?_⟩
    simp_rw [fourOddFundamentalKroneckerWindowShiftSum_eq]
    have hbase := fourOdd_quadratic_windowShiftSum_normSq_le_divisorRpow P A M b hε
    have hqnat : 1 ≤ fourOddModulus P :=
      Nat.one_le_iff_ne_zero.mpr (fourOddModulus_neZero P).out
    have hq : 1 ≤ (fourOddModulus P : ℝ) := by
      exact_mod_cast hqnat
    have hm : 0 ≤ (M : ℝ) := by positivity
    have hC : 0 ≤ Sieve.divisorBoundConst ε := hCpos.le
    have henergy : 0 ≤ ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by positivity
    calc
      _ ≤ ((M : ℝ) * (Sieve.divisorBoundConst ε * (fourOddModulus P : ℝ) ^ ε) +
          (fourOddModulus P : ℝ)) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := hbase
      _ ≤ (1 + Sieve.divisorBoundConst ε) * (fourOddModulus P : ℝ) ^ ε *
          ((fourOddModulus P : ℝ) + M) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
        have hp : 1 ≤ (fourOddModulus P : ℝ) ^ ε := Real.one_le_rpow hq hε.le
        have hp0 : 0 ≤ (fourOddModulus P : ℝ) ^ ε := le_trans (by norm_num) hp
        have hq0 : 0 ≤ (fourOddModulus P : ℝ) := le_trans (by norm_num) hq
        have hqterm : (fourOddModulus P : ℝ) ≤
            (fourOddModulus P : ℝ) ^ ε * (fourOddModulus P : ℝ) := by
          nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hp)]
        have hmterm : (M : ℝ) *
            (Sieve.divisorBoundConst ε * (fourOddModulus P : ℝ) ^ ε) ≤
            (1 + Sieve.divisorBoundConst ε) * (fourOddModulus P : ℝ) ^ ε * (M : ℝ) := by
          nlinarith [mul_nonneg hm hC, mul_nonneg hm (sub_nonneg.mpr hp)]
        have hcoef : (M : ℝ) *
            (Sieve.divisorBoundConst ε * (fourOddModulus P : ℝ) ^ ε) +
            (fourOddModulus P : ℝ) ≤
            (1 + Sieve.divisorBoundConst ε) * (fourOddModulus P : ℝ) ^ ε *
              ((fourOddModulus P : ℝ) + M) := by
          nlinarith [mul_nonneg (show 0 ≤ 1 + Sieve.divisorBoundConst ε by linarith)
            (mul_nonneg hp0 hq0)]
        exact mul_le_mul_of_nonneg_right hcoef henergy

/-- Premise-free source-scale estimate for either certified conductor-eight CRT
window.  Fundamental-discriminant wrappers below identify both choices with
their Kronecker symbols. -/
theorem eightOdd_quadratic_windowShiftSum_sourceScale [DecidableEq I]
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (ε : ℝ) :
    ε ≤ 0 ∨ ∃ C : ℝ, 0 < C ∧
      ∑ x : ZMod (eightOddModulus P),
        Complex.normSq (eightOddQuadraticWindowShiftSum κ P A M b x) ≤
          C * (eightOddModulus P : ℝ) ^ ε * ((eightOddModulus P : ℝ) + M) *
            ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
  by_cases hεnonpos : ε ≤ 0
  · exact Or.inl hεnonpos
  · right
    have hε : 0 < ε := lt_of_not_ge hεnonpos
    have hCpos : 0 < Sieve.divisorBoundConst ε := Sieve.divisorBoundConst_pos hε
    refine ⟨1 + Sieve.divisorBoundConst ε, by linarith, ?_⟩
    have hbase := eightOdd_quadratic_windowShiftSum_normSq_le_divisorRpow κ P A M b hε
    have hqnat : 1 ≤ eightOddModulus P :=
      Nat.one_le_iff_ne_zero.mpr (eightOddModulus_neZero P).out
    have hq : 1 ≤ (eightOddModulus P : ℝ) := by
      exact_mod_cast hqnat
    have hm : 0 ≤ (M : ℝ) := by positivity
    have hC : 0 ≤ Sieve.divisorBoundConst ε := hCpos.le
    have henergy : 0 ≤ ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by positivity
    calc
      _ ≤ ((M : ℝ) * (Sieve.divisorBoundConst ε * (eightOddModulus P : ℝ) ^ ε) +
          (eightOddModulus P : ℝ)) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := hbase
      _ ≤ (1 + Sieve.divisorBoundConst ε) * (eightOddModulus P : ℝ) ^ ε *
          ((eightOddModulus P : ℝ) + M) * ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
        have hp : 1 ≤ (eightOddModulus P : ℝ) ^ ε := Real.one_le_rpow hq hε.le
        have hp0 : 0 ≤ (eightOddModulus P : ℝ) ^ ε := le_trans (by norm_num) hp
        have hq0 : 0 ≤ (eightOddModulus P : ℝ) := le_trans (by norm_num) hq
        have hqterm : (eightOddModulus P : ℝ) ≤
            (eightOddModulus P : ℝ) ^ ε * (eightOddModulus P : ℝ) := by
          nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hp)]
        have hmterm : (M : ℝ) *
            (Sieve.divisorBoundConst ε * (eightOddModulus P : ℝ) ^ ε) ≤
            (1 + Sieve.divisorBoundConst ε) * (eightOddModulus P : ℝ) ^ ε * (M : ℝ) := by
          nlinarith [mul_nonneg hm hC, mul_nonneg hm (sub_nonneg.mpr hp)]
        have hcoef : (M : ℝ) *
            (Sieve.divisorBoundConst ε * (eightOddModulus P : ℝ) ^ ε) +
            (eightOddModulus P : ℝ) ≤
            (1 + Sieve.divisorBoundConst ε) * (eightOddModulus P : ℝ) ^ ε *
              ((eightOddModulus P : ℝ) + M) := by
          nlinarith [mul_nonneg (show 0 ≤ 1 + Sieve.divisorBoundConst ε by linarith)
            (mul_nonneg hp0 hq0)]
        exact mul_le_mul_of_nonneg_right hcoef henergy

/-- Premise-free source-scale form of Lemma 8 for the first level-eight
fundamental-discriminant Kronecker family. -/
theorem eightOdd_fundamentalKronecker_windowShiftSum_sourceScale [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (ε : ℝ) :
    ε ≤ 0 ∨ ∃ C : ℝ, 0 < C ∧
      ∑ x : ZMod (eightOddModulus P),
        Complex.normSq (eightOddFundamentalKroneckerWindowShiftSum P A M b x) ≤
          C * (eightOddModulus P : ℝ) ^ ε * ((eightOddModulus P : ℝ) + M) *
            ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
  simpa only [eightOddFundamentalKroneckerWindowShiftSum_eq] using
    (eightOdd_quadratic_windowShiftSum_sourceScale .first P A M b ε)

/-- Premise-free source-scale form of Lemma 8 for the second level-eight
fundamental-discriminant Kronecker family. -/
theorem eightOddPrime_fundamentalKronecker_windowShiftSum_sourceScale [DecidableEq I]
    (P : OddPrimeFamily I) (A M : ℕ) (b : ℕ → ℂ) (ε : ℝ) :
    ε ≤ 0 ∨ ∃ C : ℝ, 0 < C ∧
      ∑ x : ZMod (eightOddModulus P),
        Complex.normSq (eightOddPrimeFundamentalKroneckerWindowShiftSum P A M b x) ≤
          C * (eightOddModulus P : ℝ) ^ ε * ((eightOddModulus P : ℝ) + M) *
            ∑ n ∈ Finset.Icc 1 M, ‖b n‖ ^ 2 := by
  simpa only [eightOddPrimeFundamentalKroneckerWindowShiftSum_eq] using
    (eightOdd_quadratic_windowShiftSum_sourceScale .second P A M b ε)

end OddPrimeFamily
end RHTower
