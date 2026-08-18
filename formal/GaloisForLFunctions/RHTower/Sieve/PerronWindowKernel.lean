import GaloisForLFunctions.RHTower.Sieve.PerronShortInterval
import GaloisForLFunctions.RHTower.Sieve.PerronKernelBound

/-!
# The short-interval Perron formula against a single kernel

`Sieve/PerronShortInterval` gives the two-cutoff formula as a *difference* of two prefix integrals.
Step 2 of Matomäki–Teräväinen §7 uses it as a single integral against the kernel

```text
K(s) = ((B+1/2)^s − (A+1/2)^s)/s ,
```

whose two branches `Sieve/PerronKernelBound` bounds by `min(B − A, 2(B+1/2)/|t|)`.  Merging the two
prefix integrals is legitimate because on `Re s = σ ≥ 1` both integrands are continuous in `t`, hence
interval-integrable on the compact truncation range.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

/-- The Dirichlet polynomial appearing in the Perron integrand. -/
def perronPoly (c : ℕ → ℂ) (M : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I)))

theorem continuous_perronPoly (c : ℕ → ℂ) (M : ℕ) (σ : ℝ) :
    Continuous (fun t : ℝ => perronPoly c M σ t) := by
  refine continuous_finsetSum _ fun n hn => ?_
  refine continuous_const.mul ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  refine Continuous.cpow continuous_const ?_ ?_
  · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg
  · intro a
    exact Or.inl (by simpa using hn0)

/-- The prefix kernel `(N+1/2)^s / s`. -/
def perronPrefixKernel (N : ℕ) (σ t : ℝ) : ℂ :=
  ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)

theorem continuous_perronPrefixKernel (N : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun t : ℝ => perronPrefixKernel N σ t) := by
  have hbase : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hs : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℝ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hne : ∀ t : ℝ, ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  refine Continuous.div ?_ hs hne
  refine Continuous.cpow continuous_const hs ?_
  intro a
  exact Or.inl (by simpa using hbase)

/-- **The two prefix integrals merge into one kernel integral.** -/
theorem perronPrefixIntegral_sub (c : ℕ → ℂ) (M A B : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    perronPrefixIntegral c M B σ T - perronPrefixIntegral c M A σ T
      = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
          perronPoly c M σ t * (perronPrefixKernel B σ t - perronPrefixKernel A σ t) := by
  have hcB : Continuous (fun t : ℝ => perronPoly c M σ t * perronPrefixKernel B σ t) :=
    (continuous_perronPoly c M σ).mul (continuous_perronPrefixKernel B hσ)
  have hcA : Continuous (fun t : ℝ => perronPoly c M σ t * perronPrefixKernel A σ t) :=
    (continuous_perronPoly c M σ).mul (continuous_perronPrefixKernel A hσ)
  rw [perronPrefixIntegral, perronPrefixIntegral, ← mul_sub]
  congr 1
  show (∫ t in (-T)..T, perronPoly c M σ t * perronPrefixKernel B σ t)
      - (∫ t in (-T)..T, perronPoly c M σ t * perronPrefixKernel A σ t)
      = ∫ t in (-T)..T, perronPoly c M σ t * (perronPrefixKernel B σ t - perronPrefixKernel A σ t)
  rw [← intervalIntegral.integral_sub (hcB.intervalIntegrable _ _)
    (hcA.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr ?_
  intro t _
  ring

end

end RHTower.Sieve
