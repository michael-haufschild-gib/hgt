import GaloisForLFunctions.RHTower.Sieve.JutilaCoefficientRemoval

/-!
# Jutila coefficient removal for critical Dirichlet kernels

This specializes `JutilaCoefficientRemoval` to the critical Dirichlet kernel.  Factoring

```text
n^(-1/2 + i(t-u))
  = n^(-1/4 + it) * conjugate(n^(-1/4 + iu))
```

realizes the kernel as a row Gram matrix.  Jutila's abstract coefficient-removal inequality then
gives the exact finite form of his 1975 Dirichlet-polynomial lemma: divisor-convolution
coefficients may be replaced by ones at the square of their uniform bound.
-/

namespace RHTower.Sieve

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Half-critical Dirichlet row entry `n^(-1/4+it)`, with the natural number argument representing
the positive integer `n+1`. -/
def jutilaCriticalRowEntry (t : ℝ) (n : ℕ) : ℂ :=
  ((((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
    Complex.exp (((t * Real.log (n + 1) : ℝ) : ℂ) * Complex.I)

/-- Critical difference kernel with coefficients `a_n`:
`sum_n a_n n^(-1/2+i(t-u))`. -/
def jutilaCriticalDifferenceKernel (L : ℕ) (a : Fin L → ℂ) (t u : ℝ) : ℂ :=
  ∑ n : Fin L, a n *
    (((((n : ℕ) + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp ((((t - u) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

/-- The half-critical row factorization of the critical Dirichlet difference kernel. -/
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

/-- The abstract Jutila Gram kernel is exactly the critical Dirichlet difference kernel. -/
theorem jutilaWeightedGramKernel_critical_eq {ρ : Type*} [Fintype ρ]
    (L : ℕ) (tau : ρ → ℝ) (a : Fin L → ℂ) (r s : ρ) :
    jutilaWeightedGramKernel
        (fun q : ρ => fun n : Fin L => jutilaCriticalRowEntry (tau q) n)
        r s a = jutilaCriticalDifferenceKernel L a (tau r) (tau s) := by
  rw [jutilaWeightedGramKernel, jutilaCriticalDifferenceKernel]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_assoc, jutilaCriticalRowEntry_mul_conj, ← mul_assoc]

/-- **Jutila's critical Dirichlet coefficient-removal inequality (1975, Lemma 5.3).** -/
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
