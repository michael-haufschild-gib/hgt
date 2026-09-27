import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite signed reconstruction on logarithmic delays

These operators retain the exact exponential cutoff. Composition is
Dirichlet convolution of the coefficients, so the zeta and Möbius delay
operators invert one another on nonnegative time, for arbitrary profiles.
-/

noncomputable section
open scoped BigOperators
open ArithmeticFunction

namespace RHTower

def logarithmicWeightedDilation (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, a n * f (T - Real.log n)

def logarithmicDilationSum (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation (fun _ => 1) f T

def logarithmicMobiusInverse (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation (fun n => (moebius n : ℝ)) f T

/-- Exact finite composition, without a convergence or regularity premise. -/
theorem logarithmicWeightedDilation_comp (a b : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (logarithmicWeightedDilation b f) T =
      logarithmicWeightedDilation
        (fun k => ∑ x ∈ k.divisorsAntidiagonal, a x.1 * b x.2) f T := by
  unfold logarithmicWeightedDilation
  have hrow (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) :
      a n * (∑ m ∈ Finset.Icc 1 ⌊Real.exp (T - Real.log n)⌋₊,
        b m * f (T - Real.log n - Real.log m)) =
      ∑ m ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ / n),
        (a n * b m) * f (T - Real.log ((n * m : ℕ) : ℝ)) := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hnpos),
      Nat.floor_div_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hnpos.ne')
      (by exact_mod_cast hmpos.ne')]
    rw [sub_sub]
    ring
  rw [Finset.sum_congr rfl hrow, ← Sieve.sum_Icc_divisorsAntidiagonal_swap]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]

theorem logarithmicDilationSum_mobiusInverse (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    logarithmicDilationSum (logarithmicMobiusInverse f) T = f T := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  change logarithmicWeightedDilation (fun _ => 1)
    (logarithmicWeightedDilation (fun n => (moebius n : ℝ)) f) T = f T
  rw [logarithmicWeightedDilation_comp]
  have hc (k : ℕ) :
      (∑ x ∈ k.divisorsAntidiagonal, (1 : ℝ) * (moebius x.2 : ℝ)) =
        if k = 1 then 1 else 0 := by
    simp only [one_mul]
    rw [Nat.sum_divisorsAntidiagonal' (fun _ d => (moebius d : ℝ)),
      ← Int.cast_sum, sum_moebius_divisors]
    split_ifs <;> simp
  simp only [logarithmicWeightedDilation]
  simp_rw [hc]
  simp only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_Icc, le_refl, true_and, hN, if_true,
    Nat.cast_one, Real.log_one, sub_zero]

theorem logarithmicMobiusInverse_dilationSum (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    logarithmicMobiusInverse (logarithmicDilationSum f) T = f T := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  change logarithmicWeightedDilation (fun n => (moebius n : ℝ))
    (logarithmicWeightedDilation (fun _ => 1) f) T = f T
  rw [logarithmicWeightedDilation_comp]
  have hc (k : ℕ) :
      (∑ x ∈ k.divisorsAntidiagonal, (moebius x.1 : ℝ) * (1 : ℝ)) =
        if k = 1 then 1 else 0 := by
    simp only [mul_one]
    rw [Nat.sum_divisorsAntidiagonal (fun d _ => (moebius d : ℝ)),
      ← Int.cast_sum, sum_moebius_divisors]
    split_ifs <;> simp
  simp only [logarithmicWeightedDilation]
  simp_rw [hc]
  simp only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_Icc, le_refl, true_and, hN, if_true,
    Nat.cast_one, Real.log_one, sub_zero]

end RHTower
