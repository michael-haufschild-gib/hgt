# The Euler-bound layer is closed end-to-end (2026-08-07)

`RHTower/Sieve/DistanceAbscissaBridge.lean` — green (9026 jobs), axiom-clean, in the umbrella.

`norm_tsum_twistedSummand_le_of_mulDistSqPair` :
`‖∑' n, f n · n^(-s)‖ ≤ (1 + 1/(σ-1)) · exp(7/2 + 2(σ-1)(log z + log 4)
   - mulDistSqPair f (charFn s.im) (Nat.primesLE z))`

for `|f| ≤ 1` multiplicative on coprimes, `σ = s.re > 1`, `1 ≤ z`. The RHS distance is EXACTLY the
corpus's own harmonic distance, so `MoebiusUniformFrequency.exists_mulDistSqPair_ge_uniform`
(`≥ log log z - 7 log log T - C`, uniform over `|t| ≤ T`) substitutes directly.

Chain: `natCast_cpow_neg_eq_mul` (polar split `p^{-s} = p^{-σ}·conj(charFn t p)`) →
`rpow_sub_re_twistedSummand` (abscissa term = `p^{-σ}` × harmonic defect) →
`sum_primesLE_le_mulDistSqTsum` → `mulDistSqPair_le_mulDistSqTsum_add` (shift cost from the corpus's
`PrimeSigmaShift.abs_sum_weight_shift_le`, weights = defect/2 so modulus ≤ 1).

## Lean traps

- **`Finset.subtype Nat.Prime s` poisons `Summable.sum_le_tsum`**: instance search then wants
  `(SummationFilter.unconditional Nat.Primes).NeBot` and fails (it succeeds for an abstract
  `T : Finset Nat.Primes`). Fix: do the whole comparison over `ℕ` with the indicator
  `G n = if n.Prime then g n else 0`, then transport with `Function.Injective.summable_iff` and
  `Function.Injective.tsum_eq`. Same idiom as `RouteRCofinalSieveIsUnitProfile`.
- `Complex.ofReal_log (hx : 0 ≤ x) : ((Real.log x : ℝ) : ℂ) = Complex.log x` (there is no
  `log_ofReal_of_pos`). Use `← Complex.ofReal_natCast` first to expose the real cast.
- `-s = -(s.re) + -(s.im)·I` is proved by `apply Complex.ext <;> simp`, NOT by rewriting with
  `Complex.re_add_im` (that substitutes inside `s.re` and loops).

Remaining on the Halász path: only the `t`-integration against the Perron kernel
(`HTGeometry.SmoothWeightPerron`), with the window/uniqueness lemmas controlling the measure of the
set where the distance is small. The Euler-product side is complete.

See `mem:route_e/multiplicative_euler_bound_built_2026_08_07`,
`mem:route_e/prime_abscissa_sum_bound_2026_08_07`.
