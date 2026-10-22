import GaloisForLFunctions.RHTower.MobiusSquareResidueShortBilinear
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelSummation
import GaloisForLFunctions.RHTower.DirichletDivisorAsymptotic
import GaloisForLFunctions.RHTower.LogarithmicDivisorDilation

/-!
# Exact divisor decomposition of the square bilinear kernel

Complementary divisors turn the logarithmic floor kernel into a divisor-count
sum at each exact quotient `s²/q`. Discrete Abel summation then separates the
classical divisor main term and its remainder without changing a cutoff or
discarding an endpoint. The final identity preserves the two Möbius signs and
the original counterterm. No bound on their signed remainder is asserted.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

theorem sum_log_mul_divisors (q n : ℕ) (hq : 1 ≤ q) :
    (∑ d ∈ n.divisors, Real.log (q * d : ℕ)) =
      (n.divisors.card : ℝ) * (Real.log q + Real.log n / 2) := by
  have he : (∑ d ∈ n.divisors, Real.log (q * d : ℕ)) =
      ∑ d ∈ n.divisors, (Real.log q + Real.log d) := by
    apply sum_congr rfl
    intro d hd
    have hd₀ : d ≠ 0 := by
      intro hz
      have h := Nat.mem_divisors.mp hd
      simp [hz] at h
    have hq₀ : q ≠ 0 := by omega
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hq₀) (by exact_mod_cast hd₀)]
  rw [he, sum_add_distrib]
  simp only [sum_const, nsmul_eq_mul]
  rw [sum_log_divisors_eq_half_card_mul_log]
  ring

theorem sum_log_mul_floor_eq_divisor_sum (X q : ℕ) (hq : 1 ≤ q) :
    (∑ k ∈ Icc 1 X, Real.log (q * k : ℕ) * ((X / k : ℕ) : ℝ)) =
      ∑ n ∈ Icc 1 X,
        (n.divisors.card : ℝ) * (Real.log q + Real.log n / 2) := by
  calc
    _ = ∑ k ∈ Icc 1 X, ∑ j ∈ Icc 1 (X / k), Real.log (q * k : ℕ) := by
      apply sum_congr rfl
      intro k hk
      simp [mul_comm]
    _ = ∑ n ∈ Icc 1 X, ∑ x ∈ n.divisorsAntidiagonal,
        Real.log (q * x.1 : ℕ) :=
      (Sieve.sum_Icc_divisorsAntidiagonal_swap
        (fun k _ => Real.log (q * k : ℕ)) X).symm
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.sum_divisorsAntidiagonal (fun k _ => Real.log (q * k : ℕ))]
      exact sum_log_mul_divisors q n hq

theorem mobiusSquareShortBilinearKernel_eq_divisor_sum (N q : ℕ) :
    mobiusSquareShortBilinearKernel N q =
      ∑ s ∈ range N, ∑ n ∈ Icc 1 (s ^ 2 / q),
        (n.divisors.card : ℝ) * (Real.log q + Real.log n / 2) := by
  by_cases hq₀ : q = 0
  · subst q
    simp [mobiusSquareShortBilinearKernel]
  have hq : 1 ≤ q := by omega
  unfold mobiusSquareShortBilinearKernel mobiusSquareFloorPrefix
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  rw [← sum_log_mul_floor_eq_divisor_sum (s ^ 2 / q) q hq]
  simp_rw [← Nat.div_div_eq_div_mul]
  have hsN : s ≤ N := by have := mem_range.mp hs; omega
  have hsq : s ^ 2 ≤ N ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hsN hsN
  have hdiv : s ^ 2 / q ≤ N ^ 2 / q := Nat.div_le_div_right hsq
  symm
  apply sum_subset (fun k hk =>
    mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hdiv⟩)
  intro k hk hk'
  have hlt : s ^ 2 / q < k := by
    have := (mem_Icc.mp hk).1
    simp only [mem_Icc] at hk'
    omega
  simp [Nat.div_eq_of_lt hlt]

private theorem divisor_sum_Icc_eq_range (f : ℕ → ℝ) (X : ℕ) (hf : f 0 = 0) :
    (∑ n ∈ Icc 1 X, f n) = ∑ n ∈ range (X + 1), f n := by
  have hset : (range (X + 1)).erase 0 = Icc 1 X := by
    ext n
    simp only [mem_erase, mem_range, mem_Icc]
    omega
  have h := sum_erase_add (s := range (X + 1)) (f := f)
    (show 0 ∈ range (X + 1) by simp)
  simpa only [hset, hf, add_zero] using h

noncomputable def mobiusSquareDivisorSummatory (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, (n.divisors.card : ℝ)

noncomputable def mobiusSquareDivisorMainTerm (X : ℕ) : ℝ :=
  (X : ℝ) * Real.log X + (2 * Real.eulerMascheroniConstant - 1) * X

noncomputable def mobiusSquareDivisorRemainder (X : ℕ) : ℝ :=
  mobiusSquareDivisorSummatory X - mobiusSquareDivisorMainTerm X

private theorem divisor_count_eq_floor (X : ℕ) :
    mobiusSquareDivisorSummatory X = ∑ k ∈ Icc 1 X, ((X / k : ℕ) : ℝ) := by
  have hset : Ioc 0 X = Icc 1 X := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  have h := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div X
  rw [hset] at h
  simp_rw [ArithmeticFunction.sigma_zero_apply] at h
  unfold mobiusSquareDivisorSummatory
  exact_mod_cast h

theorem abs_mobiusSquareDivisorRemainder_le (X : ℕ) :
    |mobiusSquareDivisorRemainder X| ≤ 20 * Real.sqrt X := by
  by_cases hX : X = 0
  · subst X
    simp [mobiusSquareDivisorRemainder, mobiusSquareDivisorSummatory,
      mobiusSquareDivisorMainTerm]
  have h := abs_sum_div_sub_dirichlet_le X (by omega)
  simpa [mobiusSquareDivisorRemainder, mobiusSquareDivisorMainTerm,
    divisor_count_eq_floor, sub_add_eq_sub_sub] using h

/-- Exact discrete Abel action; its boundary term is retained even at the first cell. -/
noncomputable def mobiusSquareDivisorLogAbel (q X : ℕ) (F : ℕ → ℝ) : ℝ :=
  (Real.log q + Real.log X / 2) * F X +
    (1 / 2 : ℝ) * ∑ n ∈ range X,
      F n * (Real.log n - Real.log (n + 1 : ℕ))

theorem sum_divisor_log_eq_discrete_abel (q X : ℕ) :
    (∑ n ∈ Icc 1 X,
      (n.divisors.card : ℝ) * (Real.log q + Real.log n / 2)) =
      mobiusSquareDivisorLogAbel q X mobiusSquareDivisorSummatory := by
  have hD (Y : ℕ) :
      deningerPartialSum (fun n => (n.divisors.card : ℝ)) Y =
        mobiusSquareDivisorSummatory Y := by
    exact (divisor_sum_Icc_eq_range (fun n => (n.divisors.card : ℝ)) Y (by simp)).symm
  rw [divisor_sum_Icc_eq_range
    (fun n => (n.divisors.card : ℝ) * (Real.log q + Real.log n / 2)) X (by simp),
    deningerAbelSummation]
  simp_rw [hD]
  unfold mobiusSquareDivisorLogAbel
  rw [mul_sum]
  congr 1
  · ring
  · apply sum_congr rfl
    intro n hn
    ring

private theorem divisor_log_abel_add (q X : ℕ) (F G : ℕ → ℝ) :
    mobiusSquareDivisorLogAbel q X (fun n => F n + G n) =
      mobiusSquareDivisorLogAbel q X F + mobiusSquareDivisorLogAbel q X G := by
  unfold mobiusSquareDivisorLogAbel
  simp_rw [add_mul, mul_add, sum_add_distrib]
  ring

noncomputable def mobiusSquareDivisorPrincipalKernel (N q : ℕ) : ℝ :=
  ∑ s ∈ range N,
    mobiusSquareDivisorLogAbel q (s ^ 2 / q) mobiusSquareDivisorMainTerm

noncomputable def mobiusSquareDivisorRemainderKernel (N q : ℕ) : ℝ :=
  ∑ s ∈ range N,
    mobiusSquareDivisorLogAbel q (s ^ 2 / q) mobiusSquareDivisorRemainder

/-- No floor replacement, continuous approximation, or remainder estimate is used here. -/
theorem mobiusSquareShortBilinearKernel_eq_principal_add_remainder (N q : ℕ) :
    mobiusSquareShortBilinearKernel N q =
      mobiusSquareDivisorPrincipalKernel N q + mobiusSquareDivisorRemainderKernel N q := by
  rw [mobiusSquareShortBilinearKernel_eq_divisor_sum]
  simp_rw [sum_divisor_log_eq_discrete_abel]
  have hD : mobiusSquareDivisorSummatory =
      fun n => mobiusSquareDivisorMainTerm n + mobiusSquareDivisorRemainder n := by
    funext n
    unfold mobiusSquareDivisorRemainder
    ring
  rw [hD]
  simp_rw [divisor_log_abel_add, sum_add_distrib]
  rfl

/-- The counterterm and both actual Möbius factors remain attached to their signed source. -/
theorem mobiusShortBilinearSquareSource_eq_divisor_principal_add_remainder (N : ℕ) :
    mobiusShortBilinearSquareSource N =
      ((∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          mobiusSquareDivisorPrincipalKernel N (a * b)) -
        (1 + 2 * ∑ d ∈ Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * Real.log d / d) *
          ∑ s ∈ range N, (s : ℝ) ^ 2) +
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          mobiusSquareDivisorRemainderKernel N (a * b) := by
  unfold mobiusShortBilinearSquareSource logMobiusShortBilinearSquareAction
  simp_rw [mobiusSquareShortBilinearKernel_eq_principal_add_remainder,
    mul_add, sum_add_distrib]
  ring

/-- In the first nonzero divisor cell, the remainder is a fixed part of the full kernel. -/
theorem mobiusSquareDivisorRemainderKernel_eq_top_cell {N q : ℕ}
    (hq : (N - 1) ^ 2 < 2 * q) :
    mobiusSquareDivisorRemainderKernel N q =
      (2 - 2 * Real.eulerMascheroniConstant) * mobiusSquareShortBilinearKernel N q := by
  have hqpos : 0 < q := by nlinarith [Nat.zero_le ((N - 1) ^ 2)]
  rw [mobiusSquareShortBilinearKernel_eq_divisor_sum]
  unfold mobiusSquareDivisorRemainderKernel
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  have hs' : s ≤ N - 1 := by have := mem_range.mp hs; omega
  have hsq : s ^ 2 ≤ (N - 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hs' hs'
  have hx : s ^ 2 / q ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ s ^ 2 / q := by omega
    have := (Nat.le_div_iff_mul_le hqpos).mp htwo
    omega
  have split_small (k : ℕ) (hk : k ≤ 1) : k = 0 ∨ k = 1 := by omega
  rcases split_small (s ^ 2 / q) hx with hzero | hone
  · simp [hzero, mobiusSquareDivisorLogAbel, mobiusSquareDivisorRemainder,
      mobiusSquareDivisorSummatory, mobiusSquareDivisorMainTerm]
  · simp [hone, mobiusSquareDivisorLogAbel, mobiusSquareDivisorRemainder,
      mobiusSquareDivisorSummatory, mobiusSquareDivisorMainTerm]
    ring

theorem mobiusSquareDivisorPrincipalKernel_eq_top_cell {N q : ℕ}
    (hq : (N - 1) ^ 2 < 2 * q) :
    mobiusSquareDivisorPrincipalKernel N q =
      (2 * Real.eulerMascheroniConstant - 1) * mobiusSquareShortBilinearKernel N q := by
  have h := mobiusSquareShortBilinearKernel_eq_principal_add_remainder N q
  rw [mobiusSquareDivisorRemainderKernel_eq_top_cell hq] at h
  linarith

end RHTower
