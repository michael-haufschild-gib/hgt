import GaloisForLFunctions.RHTower.Sieve.JutilaCoefficientRemoval

namespace RHTower.Sieve

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

def jutilaCriticalRowEntry (t : ℝ) (n : ℕ) : ℂ :=
  ((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
    Complex.exp (((t * Real.log (n + 1) : ℝ) : ℂ) * Complex.I)

def jutilaCriticalDifferenceKernel (L : ℕ) (a : Fin L → ℂ) (t u : ℝ) : ℂ :=
  ∑ n : Fin L, a n *
    (((((n : ℕ) + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp ((((t - u) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

theorem jutilaCriticalRowEntry_mul_conj (t u : ℝ) (n : ℕ) :
    jutilaCriticalRowEntry t n * conj (jutilaCriticalRowEntry u n) =
      ((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp ((((t - u) * Real.log (n + 1) : ℝ) : ℂ) * Complex.I) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hweight :
      (((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) *
          (((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) =
        ((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hexp :
      Complex.exp (((t * Real.log (n + 1) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (conj (((u * Real.log (n + 1) : ℝ) : ℂ) * Complex.I)) =
        Complex.exp ((((t - u) * Real.log (n + 1) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  unfold jutilaCriticalRowEntry
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  calc
    ((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
          Complex.exp (((t * Real.log (n + 1) : ℝ) : ℂ) * Complex.I) *
        (((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
          Complex.exp (conj (((u * Real.log (n + 1) : ℝ) : ℂ) * Complex.I))) =
      (((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) *
          (((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) : ℝ) : ℂ) *
        (Complex.exp (((t * Real.log (n + 1) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (conj (((u * Real.log (n + 1) : ℝ) : ℂ) * Complex.I))) := by
            push_cast
            ring
    _ = _ := by rw [hweight, hexp]

theorem jutilaWeightedGramKernel_critical_eq {ρ : Type*} [Fintype ρ]
    (L : ℕ) (tau : ρ → ℝ) (a : Fin L → ℂ) (r s : ρ) :
    jutilaWeightedGramKernel
        (fun q : ρ => fun n : Fin L => jutilaCriticalRowEntry (tau q) n)
        r s a = jutilaCriticalDifferenceKernel L a (tau r) (tau s) := by
  rw [jutilaWeightedGramKernel, jutilaCriticalDifferenceKernel]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_assoc, jutilaCriticalRowEntry_mul_conj, ← mul_assoc]

theorem jutila_dirichlet_coefficient_removal {ρ : Type*} [Fintype ρ]
    (L : ℕ) (tau : ρ → ℝ) (a : Fin L → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, ‖a n‖ ≤ A) :
    ∑ r, ∑ s, ‖jutilaCriticalDifferenceKernel L a (tau r) (tau s)‖ ^ 2 ≤
      A ^ 2 * ∑ r, ∑ s,
        ‖jutilaCriticalDifferenceKernel L (fun _ => 1) (tau r) (tau s)‖ ^ 2 := by
  let x : ρ → Fin L → ℂ := fun r n => jutilaCriticalRowEntry (tau r) n
  have hbase := jutila_coefficient_removal x a hA ha
  simpa only [x, jutilaWeightedGramKernel_critical_eq] using hbase

end

end RHTower.Sieve
