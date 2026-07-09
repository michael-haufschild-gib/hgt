/-
Two kinds of zero for a factored carrier: columnar and interferential.

Write a carrier as a product `F = (column factor)·(rest)`, where the column factor of base `b`
depends on `s` only through the single exponential `b^{−s}`, say `ψ(b^{−s})`. A zero of `F` is:

* **columnar** when the column factor vanishes there — `ψ(b^{−s}) = 0`. Because `b^{−s}` has
  vertical period `2π/log b`, a vanishing column rides the whole imaginary-direction progression
  `{s₀ + k·(2π/log b)·i : k ∈ ℤ}`: the zero is clockwork, a divisor propagated by the column's
  own period. This is the flow-visible part of the divisor.

* **interferential** when *every* factor is nonvanishing at the point, yet the product itself is
  zero. Such a zero cannot be attributed to any single column; it is a cancellation among the
  factors. The location theorem below shows it is impossible wherever the product representation
  is an absolutely convergent infinite product: in the region of absolute convergence an infinite
  product with all factors nonvanishing is itself nonvanishing. Hence an interferential zero can
  only live where the product representation has broken down — inside the analytic continuation,
  never inside the convergence region. It is a creature of the continuation alone.

For an Euler product `∏_p (1 − a_p p^{−s})^{−1}` (equivalently `∏(1 + ·)` after expansion) this
splits the strip divisor into two disjoint charges: columnar zeros, which are the clockwork
divisor of a single prime column and vertically periodic; and interferential zeros, which carry
no column period and are confined to the continuation past the abscissa of absolute convergence.

The two results are independent of any analyticity input. Columnar periodicity needs only that
the factorization holds along the vertical progression and that `2 ≤ b` (real base exceeding one,
nonzero logarithm). Product nonvanishing needs only absolute convergence with each summand of
half-ball size, via `∏(1 + a_n) = exp(∑ log(1 + a_n))` and `exp ≠ 0`.
-/
import GaloisForLFunctions.RHTower.DAColumnDivisor
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace RHTower

/-- Columnar zeros are vertically periodic. Split one column of base `b` off the carrier,
`F s = ψ(b^{−s})·R s`, holding on a set `Ω` closed under vertical shifts `w ↦ w + t·i`. If the
column factor vanishes at `s₀ ∈ Ω`, then `F` vanishes on the entire vertical arithmetic
progression `{s₀ + k·(2π/log b)·i : k ∈ ℤ}`. No analyticity is used: the shifted point lies in
`Ω` by `hΩshift`, the factorization applies there, the column argument `b^{−s}` is unchanged by
the period shift (`exp_shift_invariant`), and the still-vanishing column kills the product. -/
theorem columnar_zero_periodic {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F R : ℂ → ℂ} {ψ : ℂ → ℂ} {b : ℕ} (hb : 2 ≤ b)
    (hfac : ∀ s ∈ Ω, F s = ψ ((b : ℂ) ^ (-s)) * R s)
    {s₀ : ℂ} (hs₀ : s₀ ∈ Ω) (h0 : ψ ((b : ℂ) ^ (-s₀)) = 0) :
    ∀ k : ℤ, F (s₀ + (k * (2 * Real.pi / Real.log b)) * Complex.I) = 0 := by
  intro k
  have hmem : s₀ + (↑k * (2 * Real.pi / Real.log b)) * Complex.I ∈ Ω := by
    have h := hΩshift s₀ hs₀ ((k : ℝ) * (2 * Real.pi / Real.log b))
    have hpt : s₀ + (((k : ℝ) * (2 * Real.pi / Real.log b) : ℝ) : ℂ) * Complex.I
             = s₀ + (↑k * (2 * Real.pi / Real.log b)) * Complex.I := by push_cast; ring
    rwa [hpt] at h
  rw [hfac _ hmem, exp_shift_invariant hb s₀ k, h0, zero_mul]

/-- Nonvanishing of an absolutely convergent complex product. If `∑ ‖a_n‖` converges and each
`‖a_n‖ ≤ 1/2`, then `∏(1 + a_n) ≠ 0`. Each factor is nonzero (`1 + a_n = 0` forces `‖a_n‖ = 1`),
so the logarithms `log(1 + a_n)` are summable, and `∏(1 + a_n) = exp(∑ log(1 + a_n))` is a value
of the exponential, hence nonzero. This is the classical statement that an absolutely convergent
infinite product cannot vanish, packaged for reuse under a clean half-ball hypothesis. -/
theorem tprod_one_add_ne_zero {a : ℕ → ℂ}
    (hsum : Summable fun n => ‖a n‖) (hhalf : ∀ n, ‖a n‖ ≤ 1 / 2) :
    ∏' n, (1 + a n) ≠ 0 := by
  have hne : ∀ n, (1 : ℂ) + a n ≠ 0 := by
    intro n h
    have han : a n = -1 := by linear_combination h
    have hnorm : ‖a n‖ = 1 := by rw [han]; simp
    have hle := hhalf n
    rw [hnorm] at hle
    norm_num at hle
  have hlog : Summable (fun n => Complex.log (1 + a n)) :=
    Complex.summable_log_one_add_of_summable hsum.of_norm
  rw [← Complex.cexp_tsum_eq_tprod hne hlog]
  exact Complex.exp_ne_zero _

/-- Interferential zeros live only in the continuation. If the carrier `F` at `s` equals an
absolutely convergent product `∏(1 + f_n s)` with each `‖f_n s‖ ≤ 1/2`, then `F s ≠ 0`. So a zero
of `F` at a point where such a product representation holds — where every factor `1 + f_n s` is
finite and the product converges absolutely — is impossible; interferential zeros (all factors
nonvanishing) can only occur where the product representation fails, i.e. in the analytic
continuation past the region of absolute convergence. Direct instantiation of the nonvanishing of
absolutely convergent products through the representation hypothesis. -/
theorem no_interferential_zero_in_product_region {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {s : ℂ}
    (hsum : Summable fun n => ‖f n s‖) (hhalf : ∀ n, ‖f n s‖ ≤ 1 / 2)
    (hrep : (∏' n, (1 + f n s)) = F s) :
    F s ≠ 0 := by
  rw [← hrep]
  exact tprod_one_add_ne_zero hsum hhalf

end RHTower
