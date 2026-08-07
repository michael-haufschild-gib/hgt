# The full-series Euler bound is built (2026-08-07)

`RHTower/Sieve/MultiplicativeEulerBound.lean`, green (3379 jobs), axiom-clean, in the umbrella.

`norm_tsum_twistedSummand_le_exp` : for `f` multiplicative on coprimes, `|f| ≤ 1`, `f 1 = 1`,
`f 0 = 0`, `Re s > 1`:

`‖∑' n, f n * n^(-s)‖ ≤ exp((∑' p : Nat.Primes, (f p * p^(-s)).re) + 5/2)`.

## Why it mattered

Every damping statement in the corpus's Halász layer (`EulerDamping`, `EulerExpansion`,
`HalaszDichotomy`, `HalaszUniqueClose`, `HalaszWindow`, `MoebiusEulerDamping`) bounds the
**squarefree smooth proxy** `∏_{p∈P}(1 + f(p)p^{-s})`, never the Dirichlet series. Perron consumes the
series. This was the actual missing Euler-product brick on the MR path — `mr-path-gap-status` was
right that the Halász analytic half is the one real gap, and this is its first half.

## Pieces (reusable)

- `twistedSummand f s n = f n * n^(-s)` + `_zero/_one/_mul`, `norm_twistedSummand_le`,
  `summable_norm_twistedSummand`, `summable_nat_rpow_neg` (any exponent > 1).
- `norm_tsum_localFactor_le` : `‖∑' e, f(p^e)p^(-es)‖ ≤ exp(Re(f(p)p^(-s)) + 5 p^(-2σ))`. Mechanism:
  `1 + z + R` with `‖R‖ ≤ 2p^{-2σ}`; corpus `norm_one_add_le_exp` for `1+z`; fold the remainder with
  `exp A + B ≤ exp(A + B e^{-A})` and `e^{-A} ≤ e^{1/2} ≤ 2` (`exp_half_le_two`, from
  `Real.exp_one_lt_d9`).
- `tsum_primes_inv_sq_le` : `∑' p, 1/p² ≤ 49/100`, transported from
  `SquarefreeDensityLowerBound.sum_primesBelow_one_div_sq_le` to the prime subtype via
  `tsum_le_of_sum_le` + `Finset.sum_image` + `primesBelow (sup+1)`.
- `tsum_primes_rpow_two_le`, `summable_primes_rpow_two` for `σ ≥ 1`.

## Lean notes

- mathlib's `EulerProduct.eulerProduct hf₁ hmul hsum hf₀` gives the ℕ-indexed
  `Tendsto (fun n => ∏ p ∈ primesBelow n, ∑' e, f (p^e)) atTop (𝓝 (∑' n, f n))` — much easier to use
  than the `HasProd` form: take `.norm`, `simp only [norm_prod]`, compare termwise with
  `∏ exp = exp ∑` (`Real.exp_sum`), and finish with `le_of_tendsto_of_tendsto'`. No infinite-product
  order lemmas needed.
- `Nat.primesBelow n = (range n).filter Nat.Prime`, so `Finset.sum_filter` converts an
  if-then-else sum over `range n` into a sum over `primesBelow n`.
- `Function.Injective.tsum_eq` (support inside the range) transports `∑' n` over ℕ to
  `∑' p : Nat.Primes`.
- Renames on this toolchain: `tsum_add` → `Summable.tsum_add`; `pow_le_pow_left` gone (use nlinarith);
  `Complex.mul_cpow_ofReal_nonneg` needs the product of TWO ofReals, not ofReal of a product.

## Next on the path

Integration over `t` against the Perron kernel: with `∑_p Re(f(p)p^{-σ-it}) = ∑_p p^{-σ} − D²`, the
bound is `|F| ≪ exp(∑_p p^{-σ}) e^{-D²}`, and `∑_p p^{-σ} ≍ log log x` at `σ = 1 + 1/log x`. The
window/uniqueness lemmas (`HalaszWindow`, `HalaszUniqueClose`) then control the measure of the set
where `D²` is small. NOT decay by itself — see `mem:halasz-mean-value-layer`.

Card: `docs/drafts/pipeline/3-formalized/multiplicative-euler-bound-halasz-input.md`.
