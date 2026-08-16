import GaloisForLFunctions.RHTower.DirichletLSeriesBridge

/-!
# Bridge to the general Dirichlet series `∑ aₙ e^{−λₙ s}`

The ordinary series used here is the general one with exponents `λₙ = log(n+1)`:

```text
aₙ (n+1)^{−s}  =  aₙ e^{−log(n+1)·s} .
```

Making that identification explicit lets the corpus's almost-periodic theory for general Dirichlet
series — strip almost periodicity, the Bohr spectrum, Bohr uniqueness — apply verbatim to the
partial sums studied here.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The ordinary exponents. -/
def ordinaryExponent (n : ℕ) : ℝ := Real.log ((n : ℝ) + 1)

theorem ordinaryExponent_zero : ordinaryExponent 0 = 0 := by
  rw [ordinaryExponent]
  norm_num

/-- Each ordinary kernel is the general exponential kernel at `λₙ = log(n+1)`. -/
theorem cpow_neg_eq_exp_neg_log (n : ℕ) (s : ℂ) :
    (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
      = Complex.exp (-((ordinaryExponent n : ℝ) : ℂ) * s) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le, ordinaryExponent]
  congr 1
  ring

/-- **The partial sums are general Dirichlet partial sums with exponents `log(n+1)`.** -/
theorem dirichletPartialSum_eq_expSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    dirichletPartialSum a N s
      = ∑ k ∈ Finset.range N,
          a k * Complex.exp (-((ordinaryExponent k : ℝ) : ℂ) * s) := by
  rw [dirichletPartialSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cpow_neg_eq_exp_neg_log]

/-- The exponents are strictly increasing, hence injective — the hypothesis the Bohr spectrum
argument needs to separate frequencies. -/
theorem ordinaryExponent_strictMono : StrictMono ordinaryExponent := by
  intro m n hmn
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlt : ((m : ℝ) + 1) < ((n : ℝ) + 1) := by
    have : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith
  exact Real.log_lt_log hm hlt

theorem ordinaryExponent_injective : Function.Injective ordinaryExponent :=
  ordinaryExponent_strictMono.injective

end GaloisForLFunctions.RHTower

end
