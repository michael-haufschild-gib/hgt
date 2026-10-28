import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonSplitsIntoSmoothRoughFibres
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRoughPrimeDefectControlsVariance

/-!
# Smooth-part conditioning approximates bounded-defect vectors

Conditioning harmonic measure on the small-prime part leaves a rough interval
in each fibre. Its variance is paid by the prime defect divided by the logarithm
of the roughness threshold. Unique factorization partitions the bottom edges
exactly, so the same estimate holds on the entire integer horizon.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Harmonic mean of the pole-gauged vector on one smooth-part fibre. -/
def smoothRoughMean (Q N : ℕ) (x : ℕ → ℝ) (d : ℕ) : ℝ :=
  wMean (roughInterval Q (N / d)) (fun k => 1 / (k : ℝ))
    (fun k => poleGauge x (d * k))

/-- The harmonic conditional mean transported back to physical coordinates. -/
def smoothRoughPoleProjection (Q N : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  smoothRoughMean Q N x (RHTower.Sieve.smoothPart (Q - 1) n) / Real.sqrt n

/-- Exact sum of the unnormalized conditional variances. -/
def smoothRoughFibreError (Q N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Nat.smoothNumbersUpTo N Q, 1 / (d : ℝ) *
    harmonicVar Q (N / d) (fun k => poleGauge x (d * k))

theorem smoothRoughFibreError_eq_sum_sq (Q N : ℕ) (x : ℕ → ℝ) :
    smoothRoughFibreError Q N x =
      ∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection Q N x n) ^ 2 := by
  classical
  rw [sum_Icc_eq_smoothRough_fibres Q N]
  unfold smoothRoughFibreError
  refine sum_congr rfl fun d hd => ?_
  rw [harmonicVar, wVar, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hd0 : 0 < d := Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp hd).2)
  have hk0 : 0 < k := (mem_roughInterval.mp hk).1
  have hn0 : (0 : ℝ) < (d * k : ℕ) := by exact_mod_cast Nat.mul_pos hd0 hk0
  have hs0 : Real.sqrt (d * k : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  rw [smoothRoughPoleProjection, smoothPart_mul_of_mem_rough_fibre hd hk]
  change 1 / (d : ℝ) * (1 / (k : ℝ) *
      (Real.sqrt (d * k : ℕ) * x (d * k) - smoothRoughMean Q N x d) ^ 2) = _
  have heq : x (d * k) - smoothRoughMean Q N x d / Real.sqrt (d * k : ℕ) =
      (Real.sqrt (d * k : ℕ) * x (d * k) - smoothRoughMean Q N x d) /
        Real.sqrt (d * k : ℕ) := by field_simp
  rw [heq, div_pow, Real.sq_sqrt hn0.le, Nat.cast_mul]
  ring

/-- Rescaling a fibre by its smooth factor preserves the literal pole gauge. -/
theorem poleGauge_smooth_fibre (d : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    poleGauge (fun j => Real.sqrt d * x (d * j)) k = poleGauge x (d * k) := by
  simp only [poleGauge, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg d)]
  ring

/-- The scaled rough defects partition the full defect by their bottom vertex. -/
theorem sum_smoothRough_roughPoleDefect (Q N : ℕ) (x : ℕ → ℝ) :
    (∑ d ∈ Nat.smoothNumbersUpTo N Q, 1 / (d : ℝ) *
      roughPoleDefect Q (N / d) (fun k => Real.sqrt d * x (d * k))) = poleDefect N x := by
  classical
  rw [poleDefect, sum_Icc_eq_smoothRough_fibres Q N]
  refine sum_congr rfl fun d hd => ?_
  rw [roughPoleDefect, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [mul_sum, Nat.div_div_eq_div_mul]
  refine sum_congr rfl fun t ht => ?_
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp hd).2
  have heq : Real.sqrt d * x (d * (k * t)) -
      Real.sqrt d * x (d * k) / Real.sqrt t =
      Real.sqrt d * (x ((d * k) * t) - x (d * k) / Real.sqrt t) := by
    rw [Nat.mul_assoc]
    ring
  rw [heq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  field_simp

/-- Bounded defect gives uniform approximation by functions of the smooth part. -/
theorem exists_smoothRoughPoleProjection_error_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ N : ℕ, ∀ x : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection Q N x n) ^ 2) ≤
        C / Real.log Q * poleDefect N x := by
  obtain ⟨C, hC, hrough⟩ := exists_rough_harmonicVar_le_primeDefect
  refine ⟨C, hC, fun Q hQ N x => ?_⟩
  rw [← smoothRoughFibreError_eq_sum_sq]
  unfold smoothRoughFibreError
  calc
    _ ≤ ∑ d ∈ Nat.smoothNumbersUpTo N Q, 1 / (d : ℝ) *
        (C / Real.log Q * roughPoleDefect Q (N / d)
          (fun k => Real.sqrt d * x (d * k))) := by
      refine sum_le_sum fun d _ => ?_
      have h := hrough Q hQ (N / d) (fun k => Real.sqrt d * x (d * k))
      have heq : poleGauge (fun k => Real.sqrt d * x (d * k)) =
          fun k => poleGauge x (d * k) := funext (poleGauge_smooth_fibre d x)
      rw [heq] at h
      exact mul_le_mul_of_nonneg_left h (div_nonneg zero_le_one (Nat.cast_nonneg d))
    _ = C / Real.log Q * (∑ d ∈ Nat.smoothNumbersUpTo N Q, 1 / (d : ℝ) *
        roughPoleDefect Q (N / d) (fun k => Real.sqrt d * x (d * k))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [sum_smoothRough_roughPoleDefect]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

