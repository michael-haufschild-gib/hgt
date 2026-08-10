import GaloisForLFunctions.RHTower.Sieve.DiscreteWindowGallagher
import GaloisForLFunctions.RHTower.Sieve.DyadicTranslates

/-!
# The dyadic mean square, bounded through Gallagher's lemma

`sum_blockSq_eq_translates` reduces every level of the Rademacher–Menshov decomposition to the
single object

```text
dyadicMeanSquare f ℓ A B = ∑_{z ∈ [A,B]} ( ∑_{z < n ≤ z+ℓ} f(n) )² ,
```

and `sum_normSq_window_le_gallagher` bounds exactly that, once the window is written as a difference
of partial sums and the range of starting points as `A, A+1, …`.  Hence

```text
dyadicMeanSquare f ℓ A B  ≤  A(1+ε)^{K'} · K' · blockCost(ℓ, A, ε, M₁, M₂, W) ,
```

with `M₁` a bound for `|∑_n f(n) n^{2πiw}|²` on `|w| ≤ W` and `M₂` one valid everywhere.

Every link from `AveragedMeanSquare` down to a bound on `‖logPoly f (Icc 1 M) w‖²` is now a proved
unconditional theorem of this corpus; what is left is the arithmetic that supplies `M₁`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The fixed-length window square, as the square of a window sum. -/
theorem fixedWindowSq_eq_sq_sum (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (z : ℕ) :
    fixedWindowSq f ℓ z = (∑ n ∈ Finset.Ioc z (z + ℓ), f n) ^ 2 := by
  have hwin := window_eq_partialSum f (y := z + 1) (by omega) (ℓ - 1)
  have hidx : z + 1 + (ℓ - 1) = z + ℓ := by omega
  have hpred : z + 1 - 1 = z := by omega
  rw [hidx, hpred] at hwin
  rw [fixedWindowSq, ← hwin, Finset.Icc_add_one_left_eq_Ioc]

/-- The window square, in the complex form the Gallagher layer uses. -/
theorem fixedWindowSq_eq_normSq (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (z : ℕ) :
    fixedWindowSq f ℓ z = ‖∑ n ∈ Finset.Ioc z (z + ℓ), ((f n : ℝ) : ℂ)‖ ^ 2 := by
  rw [fixedWindowSq_eq_sq_sum f hℓ z]
  have hcast : ∑ n ∈ Finset.Ioc z (z + ℓ), ((f n : ℝ) : ℂ)
      = (((∑ n ∈ Finset.Ioc z (z + ℓ), f n : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The dyadic mean square, bounded through Gallagher's lemma.** -/
theorem dyadicMeanSquare_le_gallagher (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {ℓ A B M K' : ℕ} {ε M₁ M₂ W : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1)
    (hε : 0 ≤ ε) (hW : 0 < W) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (h₁ : ∀ w ∈ Set.Icc (-W) W,
      ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 ≤ M₂) :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K') * ((K' : ℝ) * blockCost (ℓ : ℝ) (A : ℝ) ε M₁ M₂ W) := by
  classical
  set c : ℕ → ℂ := fun n => ((f n : ℝ) : ℂ) with hc
  have hcnorm : ∀ n : ℕ, ‖c n‖ ≤ 1 := by
    intro n
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  -- rewrite the mean square in complex window form over `range K`
  have hreindex : dyadicMeanSquare f ℓ A B
      = ∑ k ∈ Finset.range (B + 1 - A), ‖∑ n ∈ Finset.Ioc (A + k) (A + k + ℓ), c n‖ ^ 2 := by
    rw [dyadicMeanSquare, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fixedWindowSq_eq_normSq f hℓ (A + k)]
  rw [hreindex]
  have hMle : A + (B + 1 - A) + ℓ < M + 1 := by omega
  exact sum_normSq_window_le_gallagher c hcnorm hℓ hA hε hW hM₁ hM₂ hMle hcover h₁ h₂

end RHTower.Sieve

end
