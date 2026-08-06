# The main term's bracket, quantitatively (κ=1 Chebyshev)

`RHTower/Sieve/ChebyshevBracketBound.lean`:

    abs_bracket_sub_two_pi_le : c < 1 → 1 < d → 0 < T →
      |2 arctan(T/(d-1)) - 2 arctan(T/(c-1)) - 2π| ≤ 2·((d-c)/T)

The corpus's `tendsto_bracket_at_choice` is only qualitative, and only for a **symmetric**
rectangle (`c-1 = -(d-1)`).  The κ=1 rectangle is asymmetric, so this had to be built.

## The mathlib gap

**Mathlib has no `arctan z ≤ z`.**  Verified against this toolchain: `Real.arctan_le_self` and
`Real.arctan_le_arctan` do not exist.  The way in is

    Real.lt_tan : 0 < x → x < π/2 → x < tan x
    Real.tan_arctan : tan (arctan x) = x
    Real.arctan_pos : 0 < arctan x ↔ 0 < x
    Real.arctan_inv_of_pos : 0 < x → arctan x⁻¹ = π/2 - arctan x

giving `arctan_le_self` and then `pi_div_two_sub_arctan_le : 0 < u → π/2 - arctan u ≤ 1/u`.
No mean value theorem, no derivative argument.

## Sizes at the balanced κ=1 choice

`x ≈ N+H`, `t = √(log x)`, `T = exp(2t)`, `N/H = exp(t/240000)`.  The dominant term is
`(1-c)⁻¹(2(N+H)^c/c + 2Cc) ≈ t·x·exp(-t/240000)`; the balance is
`-1/80000 + 1/120000 = -1/240000`.  Total `O(x·t²·exp(-t/240000))`, and `sq_le_exp_div_gen`
absorbs `t²` into `exp(-t/480000)`.  Expected capstone
`|ψ(N) - N| ≪ N·exp(-√(log N)/480000)`.

Also in `ChebyshevKappaOneData.lean`: `one_sub_chebLeftTwo_inv` (`(1-c)⁻¹ = 40000 log T`) and
`half_le_chebLeftTwo`.

Remaining inputs are already in the corpus: `tsum_vonMangoldt_rpow_neg_le` (`8/(d-1)² = 8log²T`),
`mellin_smoothWeight_one_eq_ofReal`, `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le`.

See `mem:route_e/chebyshev_kappa_one_contour_proved_2026_08_06`,
`mem:route_e/chebyshev_kappa_one_height_and_width_2026_08_06`.
