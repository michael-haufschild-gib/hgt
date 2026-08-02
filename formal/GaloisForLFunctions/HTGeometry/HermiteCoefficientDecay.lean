import GaloisForLFunctions.HTGeometry.HermiteNumberOperator

/-!
# The Hermite coefficients of a Schwartz function decay rapidly

The Hermite functions are real valued, so pairing a Schwartz function against one is the `L²`
inner product against it, and Cauchy–Schwarz bounds that pairing by the product of the two `L²`
norms.

Moving powers of the number operator across the pairing multiplies the coefficient by `(4πn)ᵏ`.
Together: the `n`-th Hermite coefficient of a Schwartz function is bounded by `(4πn)^{-k}` times
the `L²` norm of the `k`-th power of the number operator applied to the function — rapid decay,
with an explicit constant at every order.

* `schwartzPair_eq_inner_toLp` : the pairing with a Hermite function is an `L²` inner product.
* `norm_schwartzPair_hermiteSchwartz_le` : Cauchy–Schwarz for that pairing.
* `schwartzPair_hermiteSchwartz_decay` : **`(4πn)ᵏ‖⟨f, hₙ⟩‖ ≤ ‖hₙ‖₂ ‖Nᵏf‖₂`.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- **Pairing a Schwartz function against a Hermite function is an `L²` inner product**, because
the Hermite functions are real valued. -/
theorem schwartzPair_eq_inner_toLp (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    schwartzPair f (hermiteSchwartz n)
      = inner ℂ ((hermiteSchwartz n).toLp 2 volume) (f.toLp 2 volume) := by
  rw [MeasureTheory.L2.inner_def, schwartzPair_comm, schwartzPair_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (hermiteSchwartz n) 2 volume,
    SchwartzMap.coeFn_toLp f 2 volume] with x hx hy
  rw [hx, hy, RCLike.inner_apply, conj_hermiteSchwartz, mul_comm]

/-- **Cauchy–Schwarz for the Hermite pairing.** -/
theorem norm_schwartzPair_hermiteSchwartz_le (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ‖schwartzPair f (hermiteSchwartz n)‖
      ≤ ‖(hermiteSchwartz n).toLp 2 volume‖ * ‖f.toLp 2 volume‖ := by
  rw [schwartzPair_eq_inner_toLp]
  exact norm_inner_le_norm _ _

/-- **The Hermite coefficients of a Schwartz function decay rapidly**: at every order `k` the
`n`-th coefficient is bounded by `(4πn)^{-k}` times an `L²` norm of the `k`-th power of the number
operator applied to the function. -/
theorem schwartzPair_hermiteSchwartz_decay (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (4 * π * n) ^ k * ‖schwartzPair f (hermiteSchwartz n)‖
      ≤ ‖(hermiteSchwartz n).toLp 2 volume‖ * ‖((numberCLM^[k]) f).toLp 2 volume‖ := by
  have hpair := schwartzPair_hermiteSchwartz_numberCLM_iterate k n f
  have hnorm : ‖schwartzPair ((numberCLM^[k]) f) (hermiteSchwartz n)‖
      = (4 * π * n) ^ k * ‖schwartzPair f (hermiteSchwartz n)‖ := by
    rw [hpair, norm_mul, norm_pow]
    congr 2
    have hval : (4 * (π : ℂ) * n) = ((4 * π * n : ℝ) : ℂ) := by push_cast; ring
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [← hnorm]
  exact norm_schwartzPair_hermiteSchwartz_le _ n

end GaloisForLFunctions

end
