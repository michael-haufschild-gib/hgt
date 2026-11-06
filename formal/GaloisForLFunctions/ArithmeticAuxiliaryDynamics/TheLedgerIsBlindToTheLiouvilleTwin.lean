import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCoefficientMassOfAProducer
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheLiouvilleTwinIsARatioOfHorizonTorsions

/-!
# The ledger is blind to the Liouville twin

The ledger of a stencil reads the primes through `Σ_d Λ(d) g(⌊n/d⌋)`. The weight `Λ + λΛ` is supported
on even prime powers, and its partial sum is `2 ψ(√n)`. So replacing `Λ` by the twin `−λΛ` changes every
ledger by at most `2 w ψ(√n)`: a producer cannot separate the primes from their Liouville twin below
`w √n`.

This is the parity barrier in the language of construction. The ledger uses `g(⌊n/d⌋)`, and the
parity of `d` never enters it. Breaking parity needs an input that the multiplicity does not contain.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The ledger of a stencil against a weight on the integers. -/
def ledger (c : ℕ →₀ ℤ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, a d * (stepWeight c (n / d) : ℝ)

/-- **The twin bound.** A producer's ledgers against `Λ` and against `−λΛ` differ by at most
`2 w ψ(√n)`. -/
theorem IsProducer.abs_ledger_twin_le {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (n : ℕ) :
    |ledger c ArithmeticOfSquareRootPrecision.vonMangoldtWeight n -
        ledger c (fun d => -ArithmeticOfSquareRootPrecision.liouvilleWeight d) n| ≤
      2 * (peak c : ℝ) * Chebyshev.psi (Nat.sqrt n) := by
  set W : ℕ → ℝ := fun d => ArithmeticOfSquareRootPrecision.vonMangoldtWeight d +
    ArithmeticOfSquareRootPrecision.liouvilleWeight d with hW
  have hW0 : ∀ d, 0 ≤ W d := by
    intro d
    simp only [hW, ArithmeticOfSquareRootPrecision.vonMangoldtWeight,
      ArithmeticOfSquareRootPrecision.liouvilleWeight]
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    have hlam : |(ArithmeticFunction.liouville d : ℝ)| ≤ 1 := by
      rcases eq_or_ne d 0 with rfl | hd
      · simp
      · rw [ArithmeticFunction.liouville_apply hd]
        rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors d) with h | h <;> rw [h] <;> simp
    have := (abs_le.mp hlam).1
    nlinarith
  have hsum : ∑ d ∈ Ioc 0 n, W d = 2 * Chebyshev.psi (Nat.sqrt n) := by
    have h := ArithmeticOfSquareRootPrecision.partialSum_liouvilleWeight_eq n
    have hψ : ∑ d ∈ Ioc 0 n, ArithmeticOfSquareRootPrecision.vonMangoldtWeight d =
        Chebyshev.psi n := by
      rw [Chebyshev.psi, Nat.floor_natCast]
      rfl
    simp only [ArithmeticOfSquareRootPrecision.partialSum, Nat.floor_natCast] at h
    simp only [hW, sum_add_distrib]
    linarith
  have hdiff : ledger c ArithmeticOfSquareRootPrecision.vonMangoldtWeight n -
      ledger c (fun d => -ArithmeticOfSquareRootPrecision.liouvilleWeight d) n =
      ∑ d ∈ Ioc 0 n, W d * (stepWeight c (n / d) : ℝ) := by
    rw [ledger, ledger, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    simp only [hW]
    ring
  rw [hdiff]
  have hw := hP.le_peak
  have hterm : ∀ d ∈ Ioc 0 n, |W d * (stepWeight c (n / d) : ℝ)| ≤ W d * (peak c : ℝ) := by
    intro d _
    rw [abs_mul, abs_of_nonneg (hW0 d)]
    refine mul_le_mul_of_nonneg_left ?_ (hW0 d)
    have h1 : (0 : ℝ) ≤ stepWeight c (n / d) := by exact_mod_cast hP.nonneg _
    have h2 : (stepWeight c (n / d) : ℝ) ≤ peak c := by exact_mod_cast hP.stepWeight_le_peak _
    rw [abs_of_nonneg h1]
    exact h2
  calc _ ≤ ∑ d ∈ Ioc 0 n, |W d * (stepWeight c (n / d) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 n, W d * (peak c : ℝ) := sum_le_sum hterm
    _ = (∑ d ∈ Ioc 0 n, W d) * (peak c : ℝ) := by rw [sum_mul]
    _ = _ := by rw [hsum]; ring

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
