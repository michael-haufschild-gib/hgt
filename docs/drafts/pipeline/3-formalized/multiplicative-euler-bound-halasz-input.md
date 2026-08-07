# The Euler bound for a bounded multiplicative Dirichlet series

- **ID:** multiplicative-euler-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus audit of the Matomäki–Radziwiłł path — the Halász analytic half
- **Statement:** For `f` multiplicative on coprime arguments with `|f| ≤ 1`, `f 1 = 1`, `f 0 = 0` and
  `Re s > 1`: `‖∑_n f(n) n^{-s}‖ ≤ exp((∑_p Re(f(p) p^{-s})) + 5/2)`.

## Why this was the gap

`mr-path-gap-status` records that of the four gaps stated in the `Sieve/` headers, three are stale
and one is real: **the Halász analytic half** (`HalaszDichotomy`, `HalaszWindow`). Inspecting that
layer shows what is actually missing. The corpus owns

- `EulerDamping.norm_one_add_le_exp` — `‖1 + z‖ ≤ exp(Re z + ‖z‖²)`, no smallness hypothesis;
- `EulerExpansion.norm_sum_powerset_le_exp` — the damped bound for the **finite Euler product over
  squarefree smooth integers**;
- `HalaszDichotomy`, `HalaszUniqueClose`, `HalaszWindow` — uniqueness of a close frequency, the
  `O(δ/log N)` window, and the separated-set sums;
- `MoebiusUniformFrequency` — the distance lower bound, uniform over `|t| ≤ T`;
- `DirichletMeasureLargeValues`, `DirichletIntegralMeanValue`, the sharp large sieve, Gallagher.

Every damping statement in that list is about the *squarefree smooth proxy* `∏_{p ∈ P}(1 + f(p)p^{-s})`,
never about the Dirichlet series itself. Perron inversion consumes the series, not the proxy, so the
proxy cannot be fed to the contour step: prime powers and the tail of the prime range are missing.
That is the brick this card supplies.

## What is proved

`formal/GaloisForLFunctions/RHTower/Sieve/MultiplicativeEulerBound.lean` (3379 jobs, exit 0, axioms
`[propext, Classical.choice, Quot.sound]`).

- `twistedSummand f s n = f n * n^{-s}`, with `_zero`, `_one`, `_mul` (multiplicativity on coprime
  arguments, via `Complex.mul_cpow_ofReal_nonneg`) and `norm_twistedSummand_le`,
  `summable_norm_twistedSummand` for `Re s > 1`.
- `norm_tsum_localFactor_le` — **the local factor**:
  `‖∑_e f(p^e) p^{-es}‖ ≤ exp(Re(f(p)p^{-s}) + 5 p^{-2Re s})`.
  Mechanism: the factor is `1 + f(p)p^{-s} + R` with `‖R‖ ≤ 2p^{-2Re s}` (geometric tail, using
  `p^{-Re s} ≤ 1/2`); the corpus's `norm_one_add_le_exp` handles the first two terms, and the additive
  remainder is folded into the exponent by `exp A + B ≤ exp(A + B e^{-A})` with `e^{-A} ≤ e^{1/2} ≤ 2`.
- `tsum_primes_inv_sq_le`, `tsum_primes_rpow_two_le` — the prime-power excess is an absolute
  constant: `∑_p p^{-2σ} ≤ 49/100` for `σ ≥ 1`, transported from the corpus's
  `SquarefreeDensityLowerBound.sum_primesBelow_one_div_sq_le` over the prime subtype.
- `norm_tsum_twistedSummand_le_exp` — **the headline bound**. Assembly: mathlib's
  `EulerProduct.eulerProduct` gives convergence of the partial products over `primesBelow n`; the norm
  of the product is the product of the norms; the local bound is compared termwise against
  `∏ exp(g p) = exp(∑ g p)`; and `le_of_tendsto_of_tendsto'` passes to the limit. The exponent's
  prime-power part is then bounded by `5/2`.

## What it unlocks, and what it does not

With `∑_p Re(f(p)p^{-σ-it}) = ∑_p p^{-σ} − D_σ(f, n^{it})²`, the bound reads
`|F(σ+it)| ≪ exp(∑_p p^{-σ}) · e^{-D²}` — the exact shape Halász's method needs at
`σ = 1 + 1/log x`, where `∑_p p^{-σ} ≍ log log x`. Combined with the corpus's distance lower bound
(uniform over `|t| ≤ T`) and its window/uniqueness lemmas, the remaining step to Halász's mean-value
theorem is the *integration over `t`* against the Perron kernel — no longer an Euler-product matter.

It does **not** by itself give decay: as `halasz-mean-value-layer` records, the pointwise bound for
`f = μ` is `(log T)^7`-sized, and only averaging in `t` can win. This card removes the Euler-product
obstruction from that programme; it does not close it, and it is not an RH advance.

## Gates
- [x] 1 → 2 fully-proven on paper (classical, dependency-closed)
- [x] 2 → 3 formalized: `lake build` green, axiom-clean, wired into the RHTower umbrella
- [ ] 3 → 4 publication-ready

## Log
- 2026-08-07 — created directly in 3-formalized. Reuses `norm_one_add_le_exp` and
  `sum_primesBelow_one_div_sq_le` rather than reproving them; mathlib's `EulerProduct` supplies the
  product identity.

## The bound in distance form

Same module, appended:

- `primeAbscissaSum σ = ∑'_p p^{-σ}` — the trivial size of the prime sum at the abscissa.
- `mulDistSqTsum f s = ∑'_p (p^{-Re s} − Re(f(p) p^{-s}))` — the distance of `f` from the character at
  `s`, weighted at the abscissa. Termwise this is `p^{-Re s}(1 − Re(f(p)p^{-i Im s}))`, but written as a
  difference it needs no polar decomposition, and each term is nonnegative for `|f| ≤ 1` directly from
  `Re z ≤ ‖z‖`. With `mulDistSqTsum_term_nonneg`, `summable_mulDistSqTsum`, `mulDistSqTsum_nonneg`.
- `tsum_re_twistedSummand_eq_sub` — `∑'_p Re(f(p)p^{-s}) = primeAbscissaSum (Re s) − mulDistSqTsum f s`.
- `norm_tsum_twistedSummand_le_exp_sub_dist` — **the Halász shape**:

  `‖∑_n f(n) n^{-s}‖ ≤ exp(primeAbscissaSum (Re s) − mulDistSqTsum f s + 5/2)`.

Every unit of distance from the character costs the series one factor of `e^{-1}` against its trivial
size. At `σ = 1 + 1/log x` the trivial term is of order `log log x`, which is why a distance surplus
above `log log x` is what produces decay — the mechanism the corpus's
`MoebiusUniformFrequency`/`HalaszWindow` layer supplies on the distance side.

## The trivial size, and the Halász input in closed form

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeAbscissaSumBound.lean` (9022 jobs, exit 0,
axiom-clean).

The Euler bound is only as good as an upper bound for `P(σ) = ∑_p p^{-σ}`. Bounding `P` by the whole
`ζ`-sum would give `1/(σ−1) = log x` and make the estimate vacuous; the correct size is logarithmic,
and the `ζ`-Euler product supplies it:

- `antitoneOn_rpow_neg`, `tsum_shift_rpow_neg_le` — the `p`-series value bound
  `∑_{n ≥ 2} n^{-σ} ≤ 1/(σ−1)`, via mathlib's integral test
  (`AntitoneOn.tsum_comp_add_le_integral`) and `integral_Ioi_rpow_of_lt`.
- `zetaHalfPlaneBound_le`, `norm_riemannZeta_real_le` — hence `ζ(σ) ≤ 1 + 1/(σ−1)`, reusing the
  corpus's `HTGeometry` half-plane bound rather than reproving the `ζ`-series estimate.
- `primeAbscissaSum_eq_tsum_re`, `tsum_primes_norm_cpow_sq_le` — the real-abscissa prime sum written as
  the corpus's `∑'_p Re(p^{-s})`, with the prime-inverse-square defect bounded by the module's own
  `tsum_primes_rpow_two_le`.
- `primeAbscissaSum_le` — **`P(σ) ≤ log(1 + 1/(σ−1)) + 1`**, from
  `ZetaLogPrimeSum.abs_log_norm_riemannZeta_sub_tsum_re_le` (`|log‖ζ‖ − ∑_p Re(p^{-s})| ≤ ∑_p ‖p^{-s}‖²`).
  At `σ = 1 + 1/log x` this is `log log x + O(1)`.
- `norm_tsum_twistedSummand_le_mul_exp_neg_dist` — **the Halász input in closed form**:

  `‖∑_n f(n) n^{-s}‖ ≤ (1 + 1/(Re s − 1)) · exp(7/2 − D²(f,s))`.

The series is at most its trivial size times `e^{-D²}`. Every constant is explicit and absolute, and
nothing about `f` beyond `|f| ≤ 1` and multiplicativity on coprime arguments is used.

## Remaining on this path

1. **Bridge to the corpus's finite distance.** `MultiplicativeDistance.mulDistSq f t P` is weighted by
   `1/p` at `σ = 1`; `mulDistSqTsum` is weighted by `p^{-σ}`. `PrimeSigmaShift.abs_sum_weight_shift_le`
   is exactly the conversion (free at `σ = 1 + 1/log z`), and needs the polar split
   `p^{-s} = p^{-σ}·p^{-it}` (`Complex.cpow_add` + `Complex.ofReal_cpow`, both now used in this module).
2. **Integrate over `t`.** With the closed form above, Halász's mean-value theorem needs the measure of
   the set where `D²` is small — which is what `HalaszWindow`/`HalaszUniqueClose` control — against the
   Perron kernel of `SmoothWeightPerron`.

## The bridge to the harmonic distance — the layer is now closed end-to-end

`formal/GaloisForLFunctions/RHTower/Sieve/DistanceAbscissaBridge.lean` (9026 jobs, exit 0,
axiom-clean).

The Euler bound damps by `exp(−D²)` with `D²` weighted by `p^{-σ}` over *all* primes, while every
distance lower bound in the corpus is weighted by `1/p` over the primes *up to `z`*. The bridge:

- `natCast_cpow_neg_eq_mul` — the polar split `p^{-s} = p^{-Re s} · conj(charFn (Im s) p)`, via
  `Complex.cpow_add`, `Complex.ofReal_cpow` and `Complex.ofReal_log`.
- `distDefect f t p = 1 − Re(f(p) conj(charFn t p))`, with `mulDistSqPair f (charFn t) P =
  ∑_{p ∈ P} distDefect f t p / p` true by `rfl`, and `distDefect_nonneg`, `distDefect_le_two`.
- `rpow_sub_re_twistedSummand` — each abscissa-weighted term *is* `p^{-σ}` times the harmonic defect.
- `sum_primesLE_le_mulDistSqTsum` — the finite prime sum is at most the infinite one.
- `mulDistSqPair_le_mulDistSqTsum_add` — **the bridge**:
  `mulDistSqPair f (charFn t) (primesLE z) ≤ mulDistSqTsum f s + 2(σ−1)(log z + log 4)`,
  the shift cost coming from the corpus's own `PrimeSigmaShift.abs_sum_weight_shift_le` applied to the
  defects halved (so the weights have modulus ≤ 1). At `σ = 1 + 1/log z` the cost is `O(1)`.
- `norm_tsum_twistedSummand_le_of_mulDistSqPair` — **the closed layer**:

  `‖∑_n f(n) n^{-s}‖ ≤ (1 + 1/(σ−1)) · exp(7/2 + 2(σ−1)(log z + log 4) − mulDistSqPair f (charFn t) (primesLE z))`.

The right-hand side now contains *exactly* the quantity the corpus bounds from below — e.g.
`MoebiusUniformFrequency.exists_mulDistSqPair_ge_uniform` (`≥ log log z − 7 log log T − C`, uniform over
`|t| ≤ T`). Substituting it is a direct instantiation, no new analysis.

What is still missing for Halász's mean-value theorem is only the `t`-integration against the Perron
kernel; the Euler-product side of the argument is complete.

## Lean notes worth keeping

- `Finset.subtype Nat.Prime s : Finset {x // Nat.Prime x}` breaks instance search for
  `(SummationFilter.unconditional Nat.Primes).NeBot` in `Summable.sum_le_tsum`. Transport through an
  `ℕ`-indexed indicator plus `Function.Injective.summable_iff` / `Function.Injective.tsum_eq` instead —
  over `ℕ` the instances are unproblematic.

## The discrete large-values input, for the whole series

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszFullSeriesSum.lean` (9066 jobs, exit 0, axiom-clean).

The corpus's `HalaszDichotomy` / `HalaszUniqueClose` prove the dichotomy and the separated-set sum for
the squarefree smooth proxy `smoothMulSum`. With the closed Euler layer the same three statements now
hold for the Dirichlet series itself:

- `norm_tsum_twistedSummand_le_trivial` — `‖∑_n f(n)n^{-s}‖ ≤ (1 + 1/(σ−1)) e^{7/2}`, the trivial size
  (distance is nonnegative).
- `norm_tsum_twistedSummand_le_of_far` — a frequency at distance `≥ δ` gives
  `‖∑_n f(n)n^{-s}‖ ≤ (1 + 1/(σ−1)) exp(7/2 + shift − δ²)`.
- `sum_norm_tsum_twistedSummand_le_of_card` and `sum_norm_tsum_twistedSummand_le_of_spacing` —
  **the discrete large-values input**: for a frequency set `S` with mesh exceeding the corpus's
  frequency window,

  `∑_{t ∈ S} ‖∑_n f(n) n^{-σ-it}‖ ≤ (1 + 1/(σ−1)) · e^{7/2+shift} · (|S| e^{-δ²} + 1)`.

  The uniqueness input is the corpus's own `card_filter_close_le_one_of_spacing`; only the close point
  pays the trivial size, every other point is damped.

This is the object Perron inversion consumes. The Euler-product and large-values sides of Halász's
method are now both stated for the series; what remains is the passage from the discrete frequency sum
to the `t`-integral (Gallagher/Sobolev step) and the Perron assembly.
