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

## Large values are confined to one window

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszLargeValueWindow.lean` (9067 jobs, exit 0,
axiom-clean).

The damping bound and the corpus's window estimate combine into the statement that converts pointwise
damping into a measure bound:

- `abs_sub_mul_log_le_of_abs_sub_le` — on an interval of length `π / log z` the window lemma's
  smallness hypothesis `|(t−u) log p| ≤ π` holds automatically for every `p ≤ z`.
- `sub_sq_mul_logSqWeight_le_of_norm_gt` — if the series exceeds the damped bound at both `t` and `u`,
  then both frequencies are close (contrapositive of `norm_tsum_twistedSummand_le_of_far`), so
  `(t−u)² · logSqWeight z ≤ 2π²δ²`.
- `abs_sub_le_of_norm_gt` — hence `|t − u| ≤ √(2π²δ² / logSqWeight z)`, i.e. the large-value set has
  diameter `O(δ / log z)`.

So on any interval of length `π / log z`, the set where `‖∑_n f(n)n^{-σ-it}‖` exceeds
`(1 + 1/(σ−1)) e^{7/2+shift−δ²}` is contained in a single window of width `O(δ / log z)`; everywhere
else the series obeys the damped bound. Integrating over a long range requires covering it by such
intervals — that covering step, and the Perron assembly, are what remain.

## The covering step — a measure bound over a long range

`formal/GaloisForLFunctions/HTGeometry/DiameterCoveringMeasure.lean` (2480 jobs) — a general
real-analysis device, stated without reference to Dirichlet series:

- `volume_le_of_pairwise_dist_le` — a pairwise-`w`-close set of reals has measure at most `2w` (it lies
  in an interval of length `2w`; only monotonicity of the outer measure is used, so no measurability
  hypothesis).
- `volume_inter_Icc_le_of_cells` — if the set is only thin *cell by cell*, i.e. its intersection with
  every interval of length `h` is pairwise-`w`-close, then covering `[-T, T]` by `⌊2T/h⌋ + 1` cells
  gives `volume (A ∩ [-T,T]) ≤ (2T/h + 1)·2w`.

The cell count must be `⌊2T/h⌋ + 1`, not `⌈2T/h⌉`: at the right endpoint with `2T/h` an integer the
ceiling count leaves the last point uncovered.

`RHTower/Sieve/HalaszLargeValueWindow.lean`, appended (9068 jobs, exit 0, axiom-clean):

- `volume_largeValues_le` — **the measure bound**:

  `volume {t ∈ [-T,T] : ‖∑_n f(n)n^{-σ-it}‖ > (1+1/(σ−1))e^{7/2+shift−δ²}}
     ≤ (2T·log z/π + 1) · 2√(2π²δ²/logSqWeight z)`.

  Cells of length `π/log z` make the window lemma's smallness hypothesis automatic, and inside each
  cell the large-value set has diameter `O(δ/log z)`. Since `logSqWeight z ≍ (log z)²/2`, the
  right-hand side is `O(T·δ) + O(δ/log z)`: the large-value set occupies a proportion `O(δ)` of the
  range.

With `integral_norm_dirPoly_halasz`-style splitting (`∫₀^T|F| ≤ V·T + M·|{|F| ≥ V}|`, already in
`DirichletMeasureLargeValues`) this is the last geometric input to the `t`-integral; the Perron
assembly is what remains.

## The `t`-integral — Halász's mean-value estimate for the series

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszIntegralBound.lean` (9069 jobs, exit 0, axiom-clean).

- `continuous_tsum_twistedSummand` — the series is continuous in the frequency, by the Weierstrass test
  (`continuous_tsum`) against `∑_n n^{-σ}`. Hence the large-value set is *open*, so measurable, and the
  covering bound applies to it.
- `integral_norm_tsum_twistedSummand_le` — **the mean-value bound**:

  `∫_{-T}^{T} ‖∑_n f(n)n^{-σ-it}‖ dt ≤ damped·2T + trivial·(2T log z/π + 1)·2√(2π²δ²/logSqWeight z)`

  with `damped = (1 + 1/(σ−1))e^{7/2+shift−δ²}` and `trivial = (1 + 1/(σ−1))e^{7/2}`. The proof splits
  the integral at the damped level (`integral_inter_add_sdiff`): off the exceptional window the damped
  bound holds pointwise, on it the trivial bound holds, and the window is thin by the covering estimate.

Every constant is explicit and absolute; the only inputs are `|f| ≤ 1`, multiplicativity on coprime
arguments, and `σ > 1`. This is Halász's mean-value estimate for the object Perron inversion consumes.

## State of the thread

| Step | Module | Status |
|---|---|---|
| local Euler factor | `MultiplicativeEulerBound` | done |
| full-series Euler bound | `MultiplicativeEulerBound` | done |
| trivial size `P(σ) ≤ log(1+1/(σ−1))+1` | `PrimeAbscissaSumBound` | done |
| bridge to the harmonic distance | `DistanceAbscissaBridge` | done |
| dichotomy + discrete large values | `HalaszFullSeriesSum` | done |
| large values confined to one window | `HalaszLargeValueWindow` | done |
| covering ⇒ measure bound | `DiameterCoveringMeasure` + `HalaszLargeValueWindow` | done |
| `t`-integral | `HalaszIntegralBound` | done |
| Perron assembly | `HTGeometry.SmoothWeightPerron` | **remaining** |

The Perron step is the only one left, and its inputs are already generic: `SmoothWeightPerron` is
stated for an arbitrary coefficient sequence with `‖a n‖ ≤ 1`.

## The Perron assembly — the chain is closed

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszPerronAssembly.lean` (9074 jobs, exit 0, axiom-clean).

- `perronKernel σ N H y = mellin (smoothWeight N H) (σ + iy)` — the vertical kernel.
- `norm_tsum_mul_smoothWeight_le` — **the assembled bound**:

  `2π ‖∑ₙ f(n) w(n)‖ ≤ Wsup · (Halász integral bound) + trivial · ∫_{(|y| ≤ T)ᶜ} ‖W‖`

  for any uniform kernel bound `Wsup`. Proof: the corpus's `SmoothWeightPerron.
  tsum_mul_smoothWeight_eq_integral` (stated for arbitrary unit-bounded coefficients) turns the
  smoothed sum into the vertical integral; `norm_integral_le_integral_norm` passes to moduli;
  `integral_add_compl` splits at height `T`; the range piece is bounded by `Wsup` times the mean-value
  bound of `HalaszIntegralBound`, the tail piece by the trivial size times the kernel tail.
  Integrability of the product comes from `Integrable.mono'` against `triv · ‖W‖`.

So every step of Halász's method is now formalized for the actual Dirichlet series, with all constants
explicit and no `sorry`, `axiom` or interface hypothesis anywhere in the chain:

`local factor → full series → trivial size → harmonic distance → dichotomy → discrete large values →
window confinement → covering measure → t-integral → Perron`.

**What is still parametric.** The assembled bound takes the two kernel quantities as inputs: a uniform
bound `Wsup` on `‖mellin (smoothWeight N H) (σ+iy)‖` and the tail integral
`∫_{|y| > T} ‖mellin (smoothWeight N H) (σ+iy)‖`. Neither is an open problem — the corpus's
`HTGeometry/SmoothWeightMellin.norm_mellin_smoothWeight_le_pow` and `PerronKernelBound` bound exactly
these — but instantiating them (and then choosing `z`, `δ`, `T`, `H` to make the total decay) is the
next mechanical step, and only after it does a decay statement for a specific `f` follow.

## One of the two kernel parameters is now discharged

Appended to `HalaszPerronAssembly.lean` (9074 jobs, exit 0, axiom-clean):

- `norm_perronKernel_le` — `‖perronKernel σ N H y‖ ≤ (N+H)^σ / σ`, **uniformly in `y`**, from the
  corpus's `SmoothWeightMellin.norm_mellin_smoothWeight_le_pow` (the cutoff has modulus ≤ 1 and
  vanishes past `N+H`).
- `norm_tsum_mul_smoothWeight_le_explicit` — the assembled bound with `Wsup` replaced by that explicit
  value:

  `2π‖∑ₙ f(n)w(n)‖ ≤ ((N+H)^σ/σ)·(Halász integral bound) + trivial·∫_{|y|>T} ‖perronKernel‖`.

Only the kernel *tail* is still free. The corpus's `SmoothWeightInversion.
exists_bound_mellin_smoothWeight_line` supplies `∃ C > 0, ∀ y, ‖W(σ+iy)‖ ≤ C/(1+y²)`, so the tail is
at most `C·(π − 2 arctan T)` — an explicit computation via `intervalIntegral.integral_one_div_one_add_sq`
that would close the last parameter. After that, choosing `z, δ, T, H, σ` is arithmetic, and only then
does a decay statement for a specific `f` follow.

## Both kernel parameters discharged — the estimate is fully explicit

Appended to `HalaszPerronAssembly.lean` (9074 jobs, exit 0, axiom-clean):

- `integral_compl_Icc_inv_one_add_sq_le` — the Cauchy tail: `∫_{|y| > T} (1+y²)⁻¹ ≤ π − 2 arctan T`,
  via `integral_Iic_inv_one_add_sq` and `integral_Ioi_inv_one_add_sq` after covering the complement of
  `[-T,T]` by `Iic (-T) ∪ Ioi T` (disjoint, which needs `0 ≤ T`).
- `exists_norm_tsum_mul_smoothWeight_le` — **the estimate with no free kernel quantity**:

  `∃ C ≥ 0, 2π‖∑ₙ f(n)w(n)‖ ≤ ((N+H)^σ/σ)·(Halász integral bound) + trivial·C·(π − 2 arctan T)`,

  the `C` being the corpus's own quadratic-decay constant from
  `SmoothWeightInversion.exists_bound_mellin_smoothWeight_line`.

Every quantity on the right is now explicit in `σ, z, δ, T, N, H` and one decay constant. The only work
left in this thread is arithmetic: choose the parameters (`σ = 1 + 1/log z`, `z` a power of `log T`,
`δ` from the corpus's uniform distance lower bound, `T` and `H` to balance the two terms) and check that
the total is `o(1)` for a specific `f`. That is a calculation, not a missing theorem — but it is not done,
so no decay statement is claimed.

## Parameter audit — the assembled bound does NOT yet yield decay, and why

Before choosing parameters I costed the assembled estimate. It does not close, for two independent
reasons. Both are recorded here so the chain is not mistaken for a decay theorem.

Write `σ = 1 + 1/log N`, `w = smoothWeight N H`, so the target is `‖∑ₙ f(n)w(n)‖ = o(N)`.

**(1) The covering step is too lossy by a factor `T log z`.** `volume_largeValues_le` allows one
exceptional window *per cell of length `π/log z`*, so over `[-T,T]` the large-value set has measure
`≍ T·δ` — a fixed *proportion* of the range, not `O(δ/log z)`. Multiplied by the trivial size
(`≍ log N`) and the kernel size (`≍ N`), the window term alone is `≍ N·log N·T·δ`, which is never
`o(N)`.

*The fix is available in the corpus.* The `π/log z` restriction comes from
`HalaszWindow.sq_sub_mul_logSqWeight_le`, which uses `1 − cos x ≥ x²/π²` and so needs
`|(t−u) log p| ≤ π`. Global uniqueness over the whole range follows instead from the triangle
inequality of `DistanceTriangle` together with an *upper* bound for `∑_{p ≤ z} cos(v log p)/p`, i.e. an
upper bound for `|ζ(1 + 1/log z + iv)|` — which `Sieve/ZetaOneLineBound.lean` supplies. That gives
`D(n^{it}, n^{iu})² ≥ log log z − log log(2+|t−u|) − O(1)`, so two frequencies both within `δ` of `f`
force `2δ ≥ √(log log z − log log T − O(1))`: for `δ` below that threshold the close frequency is
unique in the *whole* range, and the exceptional set is one window of width `O(δ/log z)`.

**(2) The kernel constant must be explicit.** With global uniqueness the window term becomes
`N·log N·δ/log z`, which is fine, and the main term is `damped × ∫_ℝ ‖W‖`. But
`exists_bound_mellin_smoothWeight_le`'s constant is existential, and the whole `1/log N` saving of
Halász's theorem sits in the *dependence of that constant on `H`*: the second-order bound is
`‖W(σ+iy)‖ ≲ (N+H)^σ/(H y²)`, so `∫_ℝ ‖W‖ ≍ N/H`, and the smoothing width `H = N/log N` is what
converts `exp(P(σ)) ≍ log N` into `O(1)`. With an `∃ C` one cannot see this. The corpus's
`SmoothWeightMellin.norm_mellin_smoothWeight_mul_eq` is the exact identity from which the explicit
`C(N,H)` follows (it equates `‖s‖·∏_{i<j}‖s+1+i‖·‖mellin‖` with an explicit derivative integral).

So the two upgrades needed, both with corpus inputs already present, are: replace the covering step by
global uniqueness via the one-line `ζ` bound, and replace the existential kernel constant by the
explicit second-order one. Until both are done the chain is an unconditional *estimate*, not a decay
theorem, and this card claims nothing more.

## Repair (1), first half: the window-free character distance

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeCosineSumUpper.lean` and
`.../CharacterDistanceLower.lean` (9339 jobs, exit 0, axiom-clean).

- `sum_cos_div_prime_le_of_ge` — the **mirror** of the corpus's `sum_cos_div_prime_ge_of_le`: whatever
  upper bound the Euler comparison gives for the prime series at `σ = 1 + 1/log z`, the finite cosine
  sum inherits it up to the same two absolute constants (truncation, abscissa shift). Both corpus
  devices (`abs_tsum_prime_tail_re_le`, `abs_sum_weight_shift_le`) are two-sided, so the proof is the
  reflected one.
- `charFn_mul_conj_re`, `mulDistSqPair_charFn_eq_sub` —
  `D(n^{it}, n^{iu}; z)² = ∑_{p ≤ z} 1/p − ∑_{p ≤ z} cos((t−u) log p)/p`.
- `le_mulDistSqPair_charFn` — **the window-free lower bound**:

  `logLog z − mertensSecondLowerConst − L − C_tail − (1 + log 4) ≤ D(n^{it}, n^{iu}; z)²`

  for any upper bound `L` on the prime series at frequency `t − u`, using the corpus's
  `MertensSecond.le_mertensS`.

This holds for **every** pair `t, u` — no `|t−u| log z ≤ π` restriction. That is exactly what the
covering step lacked. Completing repair (1) now needs only `L ≍ log log(2+|t−u|)`, i.e. the classical
one-line upper bound for `|ζ|`, for which `ZetaTruncated.norm_riemannZeta_le_log_uniform`
(`‖ζ w‖ ≤ 2 + e log N + e/‖w−1‖ + 2e`) is the corpus's explicit form; then the triangle inequality of
`DistanceTriangle` turns it into uniqueness of the close frequency over the whole range.

## Corrected diagnosis — the loss is in the prefactor, not the exceptional set

The repair list above is wrong about *which* step loses. Costing the route again, more carefully:

**The exceptional set is not the problem, and neither repair is needed.** The corpus's
`MoebiusUniformFrequency.exists_mulDistSqPair_ge_uniform` is a lower bound *uniform over `|t| ≤ T`* —
that is exactly the `M = min_{|t| ≤ T} D(f, n^{it}; z)²` of Halász's statement. With `δ² = M` the
hypothesis of `norm_tsum_twistedSummand_le_of_far` holds at **every** `t`, so the damped bound is
pointwise on the whole range: there is no exceptional frequency, no window, no covering. The
`HalaszLargeValueWindow` / `DiameterCoveringMeasure` layer is not needed for this route at all (it
remains a correct general statement, and `DiameterCoveringMeasure` is reusable, but it is not on the
critical path).

**Where the route really loses: a factor `log²N`.** With the damped bound holding pointwise,

`2π‖∑ₙ f(n)w(n)‖ ≤ damped · ∫_ℝ ‖W‖`,  `damped ≍ (log N)·e^{-M}`,  `∫_ℝ ‖W‖ ≍ N²/H`.

Two integrations by parts give `‖W(σ+iy)‖ ≲ (N+H)^{σ+1}/(H‖s(s+1)‖)`, so the kernel mass is `≍ N²/H`;
with the natural `H = N/log N` this is `N log N`. Hence `‖∑ₙ f(n)w(n)‖ ≲ N (log N)² e^{-M}`, and `o(N)`
requires `M > 2 log log N`. But for `f = μ` the true size is `M ≈ log log N`, which is exactly what
Halász's `(1+M)e^{-M}` consumes — his bound has prefactor `(1+M) ≍ log log N`, not `(log N)²`.

**The reason is structural.** Bounding `∫ ‖F‖‖W‖ ≤ (sup ‖F‖)·∫‖W‖` throws away all cancellation in `F`
across the range. Halász's proof instead bounds `∫ ‖F‖` by a *mean-value* estimate — in the corpus's
terms, `DirichletMeasureLargeValues.integral_norm_dirPoly_halasz` (`∫₀^T‖F‖ ≤ V·T + M·|{‖F‖ ≥ V}|`)
together with `DirichletIntegralMeanValue` — which uses `∑|aₙ|²`, not `sup‖F‖`. That is the missing
ingredient, and it is a different theorem, not a constant.

So the state of this thread is: an unconditional, fully explicit chain that reproves the *shape* of
Halász's estimate and is `(log N)²` weaker than it; the gap is precisely the mean-square input. Nothing
in the chain is wasted — the Euler bound, the trivial size, the distance bridge and the Perron assembly
are all exactly what the mean-value route also needs — but no decay follows from what is built, and the
earlier "two upgrades" note is superseded by this one.
