/-
Elementary algebra of finite Dirichlet polynomials `dpoly a s t = ∑_{n∈s} aₙ n^{-it}`.

These are the coefficient-level operations that do not depend on the multiplicative convolution
structure (that lives in `BohrMoments`: `dpolyConv`, `prodSupport`, `dpoly_mul`):

* `cterm_mul_cterm` — character multiplicativity `m^{-it}·n^{-it} = (mn)^{-it}` (`m, n ≥ 1`).
* `dpoly_sub` — `dpoly` is subtractive in the coefficient sequence.
* `dpoly_onehot` — the unit coefficient `[k = 1]` gives the constant polynomial `1` (when `1 ∈ s`).
-/
import GaloisForLFunctions.RHTower.SecondMoment

open Complex

namespace RHTower

/-- **Character multiplicativity.**  `m^{-it}·n^{-it} = (mn)^{-it}` for `m, n ≥ 1`:
`cterm a t m` combines with `cterm b t n` into the single character at `mn` with coefficient `aₘbₙ`. -/
theorem cterm_mul_cterm (a b : ℕ → ℝ) (t : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    cterm a t m * cterm b t n
      = (a m * b n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log (m * n) : ℂ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [cterm, cterm, Real.log_mul hm0 hn0]
  push_cast
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  ring

/-- `dpoly` is additive-subtractive in the coefficients. -/
theorem dpoly_sub (a b : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    dpoly (fun k => a k - b k) s t = dpoly a s t - dpoly b s t := by
  simp only [dpoly, cterm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro n _
  push_cast; ring

/-- The unit-at-`1` coefficient gives the constant Dirichlet polynomial `1`, provided `1 ∈ s`. -/
theorem dpoly_onehot (s : Finset ℕ) (t : ℝ) (hs : 1 ∈ s) :
    dpoly (fun k => if k = 1 then (1 : ℝ) else 0) s t = 1 := by
  rw [dpoly, Finset.sum_eq_single 1]
  · rw [cterm]; simp
  · intro k _ hne; rw [cterm]; simp [hne]
  · intro h; exact absurd hs h

end RHTower
