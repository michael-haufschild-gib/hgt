/-
The product of two Dirichlet polynomials is a Dirichlet polynomial: the Dirichlet convolution.

`(∑_{m∈s} aₘ m^{-it})(∑_{n∈s'} bₙ n^{-it}) = ∑_{m,n} aₘ bₙ (mn)^{-it}`, since the characters multiply,
`m^{-it}·n^{-it} = (mn)^{-it}` (from `log m + log n = log(mn)`).  This is the analytic face of the
Dirichlet convolution, and the first step in expressing the mollified product `ζ·M` — hence the
detection polynomial `1 − ζM` — as a single Dirichlet polynomial whose second moment
(`SecondMoment`) the Möbius cancellation (`Mollifier.sum_moebius_divisors`) makes small.
-/
import GaloisForLFunctions.RHTower.SecondMoment

open Complex Finset

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

/-- **The product of two Dirichlet polynomials** is the double sum over `s × s'` of the products of
characters — the pair form of the Dirichlet convolution. -/
theorem dpoly_mul (a b : ℕ → ℝ) (s s' : Finset ℕ) (t : ℝ)
    (hs : ∀ m ∈ s, 1 ≤ m) (hs' : ∀ n ∈ s', 1 ≤ n) :
    dpoly a s t * dpoly b s' t
      = ∑ m ∈ s, ∑ n ∈ s', (a m * b n : ℂ)
          * Complex.exp (-(t : ℂ) * I * (Real.log (m * n) : ℂ)) := by
  rw [dpoly, dpoly, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro m hm
  apply Finset.sum_congr rfl; intro n hn
  exact cterm_mul_cterm a b t (hs m hm) (hs' n hn)

end RHTower
