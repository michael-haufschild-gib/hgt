import GaloisForLFunctions.RHTower.Sieve.WindowRealStep
import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare

/-!
# The fibres have a fixed multiplicative width

Settling the design question raised by `WindowRealStep`.  The fibre above `a` is the integer
interval `[⌈x/a⌉, ⌊(x + h√x)/a⌋]`, whose absolute length `h√x/a` depends on `a`; but its endpoints
are `x/a` and `(x/a)·(1 + h/√x)`, so its **relative** length does not:

```text
b ∈ innerFibre x h a  →  log(x/a) ≤ log b ≤ log(x/a) + log(1 + h/√x) ,
```

with the width `log(1 + h/√x)` independent of `a`.  Every fibre is a logarithmic window of one
common width, translated to a different starting point.

That is the parametrisation `gallagher_identity` wants — it is stated at a single `δ` — and it
removes the factor-two width variation that a decomposition dyadic in absolute length incurs.  The
`√x` starting points `log(x/a)`, `a` in the dyadic block, are what the mean square runs over.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The common multiplicative width of the fibres. -/
def fibreWidth (x h : ℝ) : ℝ := Real.log (1 + h / Real.sqrt x)

/-- **Every fibre is a logarithmic window of the same width.** -/
theorem innerFibre_log_bounds {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x (h)) {b : ℕ} (hb : 1 ≤ b) (hmem : b ∈ innerFibre x h a) :
    Real.log (x / a) ≤ Real.log b
      ∧ Real.log b ≤ Real.log (x / a) + fibreWidth x h := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have ha1 : 1 ≤ a := by
    rw [mem_outerBlock] at ha
    exact ha.1.1
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [innerFibre_eq hx hh ha, Finset.mem_Icc] at hmem
  obtain ⟨h1, h2⟩ := hmem
  -- the two endpoints, as reals
  have hlow : x / (a : ℝ) ≤ (b : ℝ) := by
    have := Nat.ceil_le.1 h1
    exact this
  have hhigh : (b : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) := by
    have hle : ((b : ℕ) : ℝ) ≤ ((⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h2
    have hfl : ((⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ : ℕ) : ℝ)
        ≤ (x + h * Real.sqrt x) / (a : ℝ) := by
      refine Nat.floor_le ?_
      have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
      positivity
    linarith
  have hxa0 : (0 : ℝ) < x / (a : ℝ) := by positivity
  refine ⟨Real.log_le_log hxa0 hlow, ?_⟩
  -- the upper endpoint is the lower one times `1 + h/√x`
  have hfac : (x + h * Real.sqrt x) / (a : ℝ) = (x / (a : ℝ)) * (1 + h / Real.sqrt x) := by
    field_simp
    nlinarith [hsq, hs0]
  have hstep : Real.log (b : ℝ) ≤ Real.log ((x / (a : ℝ)) * (1 + h / Real.sqrt x)) := by
    rw [← hfac]
    exact Real.log_le_log hb0 hhigh
  have hone : (0 : ℝ) < 1 + h / Real.sqrt x := by positivity
  rw [Real.log_mul (ne_of_gt hxa0) (ne_of_gt hone)] at hstep
  rw [fibreWidth]
  exact hstep

/-- The width is positive when the window is. -/
theorem fibreWidth_pos {x h : ℝ} (hx : 0 < x) (hh : 0 < h) : 0 < fibreWidth x h := by
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  rw [fibreWidth]
  refine Real.log_pos ?_
  have : (0 : ℝ) < h / Real.sqrt x := by positivity
  linarith

end RHTower.Sieve

end
