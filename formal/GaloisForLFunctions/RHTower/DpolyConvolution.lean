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

/-- The Dirichlet-convolution coefficient `cₖ = ∑_{mn=k, m∈s, n∈s'} aₘ bₙ`. -/
noncomputable def convCoeff (a b : ℕ → ℝ) (s s' : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ (s ×ˢ s').filter (fun p => p.1 * p.2 = k), a p.1 * b p.2

/-- The support of the convolution: the set of products `mn`. -/
noncomputable def convSupp (s s' : Finset ℕ) : Finset ℕ :=
  (s ×ˢ s').image (fun p => p.1 * p.2)

/-- **The product of two Dirichlet polynomials is a Dirichlet polynomial.**  With convolution
coefficients `cₖ = ∑_{mn=k} aₘbₙ` on the product support, `dpoly a s · dpoly b s' = dpoly c (convSupp)`.
This makes the mollified product `ζ·M` a single Dirichlet polynomial whose second moment
(`SecondMoment`) is governed by `∑ₖ cₖ²`. -/
theorem dpoly_mul_eq_dpoly (a b : ℕ → ℝ) (s s' : Finset ℕ) (t : ℝ)
    (hs : ∀ m ∈ s, 1 ≤ m) (hs' : ∀ n ∈ s', 1 ≤ n) :
    dpoly a s t * dpoly b s' t = dpoly (convCoeff a b s s') (convSupp s s') t := by
  classical
  rw [dpoly_mul a b s s' t hs hs', ← Finset.sum_product']
  rw [dpoly, convSupp]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image_of_mem (fun p : ℕ × ℕ => p.1 * p.2) hp)]
  apply Finset.sum_congr rfl
  intro k _
  rw [cterm, convCoeff, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
  have hpk' : (p.1 : ℝ) * (p.2 : ℝ) = (k : ℝ) := by exact_mod_cast hpk
  rw [hpk']
  push_cast
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

