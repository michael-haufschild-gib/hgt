import GaloisForLFunctions.RHTower.Sieve.FibreTailAverage
import GaloisForLFunctions.RHTower.Sieve.SquarefreeTailTruncate
import GaloisForLFunctions.RHTower.Sieve.SquarefreeExceptional
import GaloisForLFunctions.RHTower.Sieve.GoodStartFibreWindow

/-!
# The fibre squarefree mass: the exceptional set and the good fibres
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The aggregate bound for the fibre tails. -/
noncomputable def fibreTailBudget (x h : ℝ) (R M' : ℕ) : ℝ :=
  4 * ((⌈h⌉₊ + 1 : ℕ) : ℝ)
    * (((⌈Real.sqrt x⌉₊ : ℝ) + ((⌈h⌉₊ + 1 : ℕ) : ℝ)
        - ((⌈Real.sqrt x / 2⌉₊ - 1 : ℕ) : ℝ)) / (R : ℝ) + (M' : ℝ))

/-- **The fibre tails are bounded in aggregate.** -/
theorem sum_fibre_windowTail_le_budget {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {R M' : ℕ}
    (hR : 1 ≤ R) (hA : 1 ≤ ⌈Real.sqrt x / 2⌉₊)
    (hAB : ⌈Real.sqrt x / 2⌉₊ - 1 ≤ ⌈Real.sqrt x⌉₊ + (⌈h⌉₊ + 1)) :
    ∑ a ∈ outerBlock x h, windowTail (fibreStartIdx x a) (fibreLen x h a) R M'
      ≤ fibreTailBudget x h R M' := by
  have h1 := sum_fibre_windowTail_le hx hh R M'
  have h2 := sum_shift_windowTail_le (A := ⌈Real.sqrt x / 2⌉₊) (B := ⌈Real.sqrt x⌉₊)
    (⌈h⌉₊ + 1) R M' hA hR hAB
  have h3 : 4 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      windowTail (y - 1) (⌈h⌉₊ + 1) R M' ≤ fibreTailBudget x h R M' := by
    rw [fibreTailBudget]
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 4)
    linarith
  linarith

/-- **The exceptional fibres are few.**  Markov against the aggregate tail budget. -/
theorem card_fibre_bad_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {R M' : ℕ}
    (hR : 1 ≤ R) (hA : 1 ≤ ⌈Real.sqrt x / 2⌉₊)
    (hAB : ⌈Real.sqrt x / 2⌉₊ - 1 ≤ ⌈Real.sqrt x⌉₊ + (⌈h⌉₊ + 1))
    {θ : ℝ} (hθ : 0 < θ) :
    ((((outerBlock x h).filter (fun a =>
        θ ≤ windowTail (fibreStartIdx x a) (fibreLen x h a) R M')).card : ℕ) : ℝ)
      ≤ fibreTailBudget x h R M' / θ := by
  classical
  exact card_large_le_of_sum_le hθ
    (fun a _ => windowTail_nonneg _ _ _ _)
    (sum_fibre_windowTail_le_budget hx hh hR hA hAB)

/-- **The good fibres carry the squarefree mass.**  Outside the exceptional set the fibre holds at
least `(1/2)·(6/π²)·(fibre length)` squarefree integers. -/
theorem fibre_squarefree_mass {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {R M M' : ℕ} (hR : 1 ≤ R)
    {θ : ℝ}
    (hbig : ∀ a ∈ outerBlock x h, fibreStartIdx x a + fibreLen x h a ≤ M)
    (hMM : M' ≤ M)
    (hsq : ∀ a ∈ outerBlock x h,
      fibreStartIdx x a + fibreLen x h a < (M' + 1) ^ 2)
    (hgap : ∀ a ∈ outerBlock x h,
      (R : ℝ) + (fibreLen x h a : ℝ) / (R : ℝ) + θ
        ≤ (1 / 2) * squarefreeDensity * (fibreLen x h a : ℝ)) :
    ∀ a ∈ outerBlock x h,
      windowTail (fibreStartIdx x a) (fibreLen x h a) R M' ≤ θ →
      (1 / 2) * squarefreeDensity * (fibreLen x h a : ℝ)
        ≤ ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ) ^ 2 := by
  intro a ha htail
  have hbase := squarefree_count_ge_trunc (fibreStartIdx x a) (fibreLen x h a) R M M' hR
    (hbig a ha) hMM (hsq a ha)
  have hfib : innerFibre x h a
      = Finset.Ioc (fibreStartIdx x a) (fibreStartIdx x a + fibreLen x h a) :=
    innerFibre_eq_Ioc hx hh ha
  rw [hfib]
  have htw : ∑ d ∈ Finset.Icc (R + 1) M',
      ((#{n ∈ Finset.Ioc (fibreStartIdx x a)
          (fibreStartIdx x a + fibreLen x h a) | d ^ 2 ∣ n} : ℕ) : ℝ)
      = windowTail (fibreStartIdx x a) (fibreLen x h a) R M' := rfl
  rw [htw] at hbase
  have hg := hgap a ha
  linarith

end RHTower.Sieve
