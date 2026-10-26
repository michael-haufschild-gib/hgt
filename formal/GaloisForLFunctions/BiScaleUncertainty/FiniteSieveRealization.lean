import GaloisForLFunctions.BezoutValuationIncidence.PronicBezoutSplitAndPrimePowerIndecomposability
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Exact divisor-sieve realization of finite integer signals

Möbius inversion constructs finite coefficients realizing every prescribed
window vector. This transfers graph witnesses to the actual arithmetic model.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- Explicit inverse divisor transform of an arbitrary real integer signal. -/
def integerSignalMobiusCoefficient (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ d.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * f x.2

/-- Divisor summation exactly reconstructs every positive-index signal value. -/
theorem sum_divisors_integerSignalMobiusCoefficient (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, integerSignalMobiusCoefficient f d) = f n := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := integerSignalMobiusCoefficient f) (g := f)).mpr (fun _ _ => rfl)
  exact h n hn

/-- Finite window coefficients vanish beyond the specified horizon. -/
def finiteIntegerSignalCoefficient (N : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d ≤ N then integerSignalMobiusCoefficient f d else 0

theorem finiteIntegerSignalCoefficient_eq_zero (N : ℕ) (f : ℕ → ℝ) {d : ℕ} (hd : N < d) :
    finiteIntegerSignalCoefficient N f d = 0 := by
  rw [finiteIntegerSignalCoefficient, if_neg (not_le.mpr hd)]

/-- The actual finite divisor sieve realizes each prescribed window value. -/
theorem sieveSeq_finiteIntegerSignalCoefficient (N : ℕ) (f : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    BezoutValuationIncidence.sieveSeq N (finiteIntegerSignalCoefficient N f) n = f n := by
  have hn0 : 0 < n := hn
  have hset : (Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    constructor
    · intro hd
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hn0.ne'⟩
    · intro hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      exact mem_filter.mpr ⟨mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hn0 hdvd).trans hnN⟩, hdvd⟩
  rw [BezoutValuationIncidence.sieveSeq, hset]
  calc
    _ = ∑ d ∈ n.divisors, integerSignalMobiusCoefficient f d := by
      apply sum_congr rfl
      intro d hd
      rw [finiteIntegerSignalCoefficient,
        if_pos ((Nat.le_of_dvd hn0 (Nat.dvd_of_mem_divisors hd)).trans hnN)]
    _ = f n := sum_divisors_integerSignalMobiusCoefficient f n hn0

/-- Every finite real window vector has explicitly supported arithmetic sieve coefficients. -/
theorem exists_finite_sieveSeq_realization (N : ℕ) (f : ℕ → ℝ) :
    ∃ c : ℕ → ℝ, (∀ d, N < d → c d = 0) ∧
      ∀ n ∈ Icc 1 N, BezoutValuationIncidence.sieveSeq N c n = f n := by
  refine ⟨finiteIntegerSignalCoefficient N f,
    fun _ hd => finiteIntegerSignalCoefficient_eq_zero N f hd, ?_⟩
  intro n hn
  exact sieveSeq_finiteIntegerSignalCoefficient N f (mem_Icc.mp hn).1 (mem_Icc.mp hn).2

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
