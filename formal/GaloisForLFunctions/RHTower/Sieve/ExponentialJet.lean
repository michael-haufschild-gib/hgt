import Mathlib

/-!
# Exponential power-series jets

`exponentialJet x` has coefficient `x^n/n!`; multiplication therefore encodes the ordinary
Leibniz rule with binomial coefficients after coefficients are multiplied by `n!`.
-/

open Finset
open PowerSeries

namespace RHTower.Sieve

noncomputable section

def exponentialJet (x : ℝ) : PowerSeries ℝ :=
  PowerSeries.rescale x (PowerSeries.exp ℝ)

@[simp] theorem coeff_exponentialJet (x : ℝ) (n : ℕ) :
    PowerSeries.coeff n (exponentialJet x) = x ^ n / (n.factorial : ℝ) := by
  rw [exponentialJet, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  norm_num
  ring

theorem sum_nat_antidiagonal_eq_range_real (F : ℕ × ℕ → ℝ) (k : ℕ) :
    (∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, F x) =
      ∑ j ∈ Finset.range (k + 1), F (j, k - j) := by
  let e : ℕ ↪ ℕ × ℕ :=
    ⟨fun j => (j, k - j), fun a b h => by simpa using congrArg Prod.fst h⟩
  have heq : Finset.HasAntidiagonal.antidiagonal k = (Finset.range (k + 1)).map e := by
    ext x
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp only [Finset.mem_map, Finset.mem_range]
    constructor
    · intro hx
      refine ⟨x.1, by omega, ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [e]
        omega
    · rintro ⟨j, hj, rfl⟩
      dsimp [e]
      omega
  rw [heq, Finset.sum_map]
  rfl

@[simp] theorem exponentialJet_add (x y : ℝ) :
    exponentialJet (x + y) = exponentialJet x * exponentialJet y := by
  ext n
  rw [PowerSeries.coeff_mul, coeff_exponentialJet, sum_nat_antidiagonal_eq_range_real]
  simp_rw [coeff_exponentialJet]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      x ^ j / (j.factorial : ℝ) * (y ^ (n - j) / ((n - j).factorial : ℝ)) =
        (x ^ j * y ^ (n - j) * (n.choose j : ℝ)) / (n.factorial : ℝ) := by
    intro j hj
    have hjn : j ≤ n := by simp only [Finset.mem_range] at hj; omega
    have hfac := Nat.choose_mul_factorial_mul_factorial hjn
    have hfacR : (n.choose j : ℝ) * (j.factorial : ℝ) * ((n-j).factorial : ℝ) =
        (n.factorial : ℝ) := by exact_mod_cast hfac
    have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
    have hnjf : ((n-j).factorial : ℝ) ≠ 0 := by positivity
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hc : (n.choose j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hjn).ne'
    calc
      x ^ j / (j.factorial : ℝ) * (y ^ (n - j) / ((n - j).factorial : ℝ)) =
          (x ^ j * y ^ (n - j)) /
            ((j.factorial : ℝ) * ((n - j).factorial : ℝ)) := by field_simp
      _ = (x ^ j * y ^ (n - j) * (n.choose j : ℝ)) /
            (n.factorial : ℝ) := by
              rw [← hfacR]
              field_simp [hc]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  rw [← add_pow]

@[simp] theorem exponentialJet_zero : exponentialJet 0 = 1 := by
  ext n
  rcases n with _ | n
  · simp
  · simp [coeff_exponentialJet]

theorem exponentialJet_nat_mul (n : ℕ) (x : ℝ) :
    exponentialJet ((n : ℝ) * x) = exponentialJet x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, exponentialJet_add, ih, pow_succ, one_mul]

end

end RHTower.Sieve
