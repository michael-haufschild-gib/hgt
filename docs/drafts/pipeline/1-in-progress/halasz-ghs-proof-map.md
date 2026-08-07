# Build map: the sharp Halász theorem after Granville–Harper–Soundararajan

- **ID:** halasz-ghs-proof-map
- **Stage:** 1-in-progress
- **Type:** BUILD MAP (Lean)
- **Goal:** an unconditional Lean proof of Halász's theorem in the sharp form, the input that Route E's
  Matomäki–Radziwiłł wall needs.

The route is the one of Granville–Harper–Soundararajan, *A more intuitive proof of a sharp version of
Halász's theorem* (arXiv:1706.03755), with the companion *A new proof of Halász's Theorem, and its
consequences* (arXiv:1706.03749, Compositio 2019). Their statement: for `|f(n)| ≤ 1`, with
`F_x(s) = ∏_{p ≤ x}(1 + ∑_k f(p^k)p^{-ks})` and

`L(x)² := ∑_{|N| ≤ log²x + 1} (N²+1)^{-1} · sup_{|t−N| ≤ 1/2} |F_x(1+it)|²`,

`|S(x)| ≪ x·(L(x)/log x)·log(100 log x/L(x)) + x log log x/log x`.

With `L(x) ≍ log x · e^{−M}` this is `(1+M)e^{−M}`, so the `1+M` prefactor is *the dyadic count of
scales*, not an artefact of a crude estimate. That is the structural reason the corpus's earlier
contour route lost `(log N)²` (`halasz-programme-session-index.md`, no-gos 1–3): it had no scale
decomposition and no prime-supported mean-square.

## The skeleton, and what the corpus already has

| Step | Content | Status |
|---|---|---|
| 1 | `∑_{n ≤ x} f(n) log n = ∑_{mp ≤ x} f(m) f(p) log p + O(x)`, hence `S(x) log x = ∑_{p ≤ x} f(p) log p S(x/p) + O(x)` | **done** — `RHTower.Sieve.norm_sum_Icc_mul_log_sub_sum_primes_le'` (`ghs-multiplicative-log-recursion.md`) |
| 2 | apply step 1 again to `S(x/p)`, after discarding `p ≤ log⁴x` and `p > x/2`, giving the triple convolution `S(x) = (1/log x)∑_{log⁴x<p≤x/2} (f(p) log p/log(x/p)) ∑_{nq ≤ x/p} f(n)f(q) log q + O(x log log x/log x)` | open — needs `∑_{log⁴x<p≤x/2} log p/(p log(x/p)) ≪ log log x` |
| 3 | partition `p ∈ [(log x)⁴, x/2]` into `P_k = (x^{1−e^{1−k}}, x^{1−e^{−k}}]`, `k ≤ log log x + O(1)`; trivial bound `S_k ≪ e^{−k} x log x` kills `k > log(100 log x/L(x))` | open — elementary, needs Mertens' first theorem only (corpus has it) |
| 4 | for the surviving `k`, truncated Perron + Cauchy–Schwarz: `S_k(x) ≪ x √(I₁I₂) + x` with `I₁ = ∫|A_k|²|ds|`, `I₂ = ∫|B_k|²|F_x|²|ds|/|s|²`; then `I₂ ≪ L(x)²e^{1−k}log x` and `I₁ ≪ e^k/log x`, so `S_k ≪ xL(x) + x` | open — needs the truncated Perron formula and Lemma 1 |
| L1 | **GHS Lemma 1**: `∫_{−T}^{T} \|∑_{T² ≤ n ≤ x} a_n Λ(n) n^{−1−it}\|² dt ≪ ∑_{T² ≤ n ≤ x} \|a_n\|² Λ(n)/n` | **half done** — see below |

GHS are explicit that the *standard* Dirichlet-polynomial mean value theorem does not suffice here: it
would give the weight `Λ(n)²`, not `Λ(n)`. This is exactly the sharpening the corpus's no-go 3 named as
missing. The proof of Lemma 1 is a smooth weight plus Brun–Titchmarsh for primes in short intervals.

## What was built for it today

`RHTower/Sieve/GallagherReverse.lean` — **Gallagher's lemma in the mean-value direction**:

`∫_{−W}^{W} ‖∑_n a_n n^{2πiw}‖² dw ≤ (5/(4δ²)) ∫_ℝ ‖∑_{u < log n ≤ u+δ} a_n‖² du`   for `2πδW ≤ 1`.

The corpus already owned the exact overlap identity `gallagher_identity` (an equality), so only a *lower*
bound for the Fejér weight on the central range was missing:

* `four_fifths_sq_le_two_sub_two_mul_cos` — `2 − 2cos θ ≥ (4/5)θ²` for `|θ| ≤ 1`, from mathlib's
  `Real.cos_bound`;
* `le_fejerWeightAt_re` — `(fejerWeightAt T L).re ≥ (4/5)T` for `|TL| ≤ 1`;
* `le_fourier_triC_re` — `Re 𝓕(δ−|·|)₊(w) ≥ (4/5)δ²` for `|2πδw| ≤ 1`;
* `integral_Icc_normSq_logPoly_le_window` — the lemma itself.

## The remaining path to Lemma 1

With `c_n = a_n Λ(n)/n` supported on primes, Gallagher's lemma reduces the frequency integral to
`∫_ℝ ‖∑_{u < log n ≤ u+δ} c_n‖² du`. Cauchy–Schwarz inside each window gives
`(#{primes in (e^u, e^{u+δ}]}) · ∑_{window} |c_n|²`, and the corpus's Brun–Titchmarsh shape
(`Sieve/BrunTitchmarsh.card_coprime_Ioc_le_log`, `Sieve/PrimeWindowUpper.card_primes_Ioc_le_explicit`)
bounds the count by `≪ δe^u/u`. Integrating in `u` gives `δ` per index, so the total is
`δ² ∑_n |a_n|² log n/n`, and the `(5/(4δ²))` prefactor cancels the `δ²`: exactly the `Λ(n)/n` weight.
Every ingredient is in the corpus; the work is the bookkeeping.

## Discipline

Nothing on this card is conditional and nothing may become conditional: no step assumes a bound on `S`
or on `F_x`. `L(x)` is a *definition*, not a hypothesis — it is a finite supremum-sum over the
frequency grid, computable from `f` alone.

## Second brick: the almost-diagonal mean value theorem

`RHTower/Sieve/GallagherAlmostDiagonal.lean` (green, axiom-clean, wired):

* `logNeighbourCount s δ n = #{m ∈ s : |log n − log m| < δ}`;
* `integral_normSq_logWindowSum_le_count` — `∫_ℝ ‖∑_{u < log n ≤ u+δ} a_n‖² du ≤ δ ∑_n (count n)‖a_n‖²`,
  from the corpus's *exact* quadratic form `integral_normSq_logWindowSum` by
  `Re(a_n conj a_m) ≤ (‖a_n‖²+‖a_m‖²)/2` and `(δ−|Δ|)₊ ≤ δ·1_{|Δ|<δ}`. No hypothesis on `δ` at all;
* `integral_Icc_normSq_logPoly_le_count` — **the mean value theorem**:

  `∫_{−W}^{W} ‖∑_n a_n n^{2πiw}‖² dw ≤ (5/(4δ)) ∑_n (count n) ‖a_n‖²`,   `2πδW ≤ 1`.

All arithmetic is now inside a single count. For `s` a set of primes and `δ` small this count is `O(1)`
for most `n`, whereas the classical mean value theorem's error `O(N ∑‖a_n‖²)` is blind to the support —
that difference is exactly `Λ(n)` versus `Λ(n)²` in GHS Lemma 1.

Remaining for Lemma 1: bound `logNeighbourCount` for a prime support by the corpus's Brun–Titchmarsh
count (`Sieve/PrimeWindowUpper.card_primes_Ioc_le_explicit`), then specialise
`a_n = c_n Λ(n)/n`.

## Third brick: the arithmetic input of Lemma 1 is discharged

`RHTower/Sieve/PrimeLogWindowCount.lean` (green, axiom-clean, wired):

* `logNeighbourCount_le_card_prime_Ioc` — a multiplicative window `|log n − log m| < δ` around `n`
  consists of integers of the single interval `(⌊n e^{−δ}⌋, ⌊n e^{δ}⌋]`;
* `logNeighbourCount_le_sieve` — hence, for a prime support, the corpus's Selberg-sieve short-interval
  count applies:

  `#{p ∈ s : |log n − log p| < δ} ≤ 2(n(e^δ − e^{−δ}) + 1)/log Y + selbergFibreError z Y + z`

  for every sieve level `1 ≤ Y ≤ z`, `2 ≤ z` — reusing `RHTower.Sieve.card_prime_Ioc_le`;
* `integral_Icc_normSq_logPoly_le_prime_sieve` — **the prime-supported mean value theorem**:

  `∫_{−W}^{W} ‖∑_{p ∈ s} a_p p^{2πiw}‖² dw
     ≤ (5/(4δ)) ∑_{p ∈ s} (2(p(e^δ − e^{−δ}) + 1)/log Y + selbergFibreError z Y + z) ‖a_p‖²`.

With `a_p = c_p (log p)/p` and `log Y ≍ (log p)/3` the main term per prime is `≍ ‖c_p‖² (log p)/p`: that
is GHS Lemma 1's right-hand side, `∑ |a_n|² Λ(n)/n`, and the `δ` cancels between the `(5/(4δ))` of
Gallagher and the `e^δ − e^{−δ} ≍ 2δ` of the window. The one logarithm of saving over the count of
*integers* in the window is precisely the difference between `Λ(n)` and `Λ(n)²`.

Steps 2 and 3 of the skeleton (the second application of the recursion, and the dyadic partition of the
prime range) and the truncated Perron formula of step 4 remain.

## Fourth brick: the whole frequency line, with no parameters

`RHTower/Sieve/LorentzianMeanSquare.lean` (green, axiom-clean, wired). The weight a sharp Perron kernel
attaches to a vertical line is `1/|s|`, so the governing quantity is the Lorentzian-weighted mean square.
Cutting the line into the unit block and the dyadic annuli of `GallagherDyadicTail`, and paying each
piece by the almost-diagonal mean value theorem at the matching window length `δ = 1/(2πT)`:

`∫_ℝ ‖∑_n a_n n^{2πiw}‖² dw/(1+w²) ≤ (25π/2) ∑_n ‖a_n‖² · #{m ∈ s : |log n − log m| < 1/(2π)}`.

**This theorem has no hypotheses at all** — no positivity, no range, no growth condition: `a` and `s` are
arbitrary. Each annulus contributes `4^{-k}` from the weight against `2^k` from the mean value theorem,
so the dyadic sum is geometric and the constant is absolute; `logNeighbourCount_mono` lets every block
be charged to the *unit-scale* count.

Declarations: `logNeighbourCount_mono`, `continuous_normSq_logPoly`,
`integral_Icc_normSq_logPoly_le_unit_count`, `integrable_lorentz_normSq_logPoly`,
`integral_dyadicAnnulus_lorentz_le`, `integral_lorentz_normSq_logPoly_le_count`.

With `PrimeLogWindowCount` this is `I₂` of GHS step 4 over the *whole* line: their
`∑_{|N| ≤ log²x+1} (N²+1)^{-1} sup_{|t−N| ≤ 1/2}|F_x(1+it)|²` is a Lorentzian-weighted sum of unit-block
suprema, i.e. the same weight, and their truncation at height `(log x)²` is no longer needed on the
`B_k` factor.

## Fifth and sixth bricks: GHS Lemma 1, over the whole line

`RHTower/Sieve/LorentzianDirPoly.lean` — the same theorem in the frequency variable in which every
vertical-line estimate of the corpus is stated, via the corpus's own `logPoly_eq_dirPoly`:

`∫_ℝ ‖∑_{n ≤ N} a_n n^{it}‖² dt/(1+t²) ≤ 25π² ∑_{n ≤ N} ‖a_n‖² · #{m ≤ N : |log n − log m| < 1/(2π)}`.

The substitution `t = 2πw` costs `2π` and the weight *improves*: `1 + 4π²w² ≥ 1 + w²`.

`RHTower/Sieve/LorentzianPrimeSupport.lean` — the count only ever sees indices with a nonzero
coefficient, so dropping the vanishing terms (`logPoly_eq_logPoly_filter`) replaces the count over the
index set by the count over the **support** (`integral_lorentz_normSq_logPoly_le_support_count`). For
coefficients supported on primes the support count is a short-interval prime count, and the sieve
discharges it:

`∫_ℝ ‖∑_p a_p p^{2πiw}‖² dw/(1+w²)
   ≤ (25π/2) ∑_p (2(p(e^δ − e^{−δ}) + 1)/log Y + selbergFibreError z Y + z) ‖a_p‖²`,  `δ = 1/(2π)`.

That is **GHS Lemma 1 over the whole frequency line**: a prime-supported mean square with weight
`Λ(n)/n` in place of `Λ(n)²/n`, with no truncation of the line, and no parameter except the sieve level
`Y ≤ z`. The only hypothesis is that the coefficients vanish off the primes.

What remains of the skeleton: steps 2 and 3 (the second application of the recursion and the dyadic
partition of the prime range, both Mertens bookkeeping over corpus assets), and the outer Perron passage
extracting `S_k(x)` from its Dirichlet series.

## Seventh brick: Mertens on a block

`RHTower/Sieve/MertensBlock.lean` — subtracting two instances of the corpus's `mertens_first_prime`:

`|∑_{y < p ≤ z} (log p)/p − (log z − log y)| ≤ 2C`,   `C = (log 4 + 4) + (8 + mertensTail)`,

with the one-sided form `sum_Ioc_prime_log_div_le`. This is what the dyadic partition of step 3 consumes:
on `P_k = (x^{1−e^{1−k}}, x^{1−e^{−k}}]` the block sum is `(e−1)e^{−k} log x + O(1)`, so the blocks carry
geometrically decreasing mass and only `log(100 log x/L(x))` of them matter — the mechanism behind
Halász's `1 + M` prefactor.

## Eighth brick: step 2, the second application of the recursion

`RHTower/Sieve/MultiplicativePrimeAverage.lean` (green, axiom-clean, wired):

* `norm_sum_Icc_sub_prime_average_le` — **the averaged recursion**, the prime-only recursion divided by
  `log N`:

  `‖S_f(N) − (∑_{p ≤ N} f(p) log p S_f(⌊N/p⌋))/log N‖ ≤ (9 + mertensTail)·N/log N`   (`N ≥ 2`);

* `norm_prime_average_le` — the prime average at its trivial size, `≤ N log N + O(N)`;
* `norm_sum_primes_sub_double_average_le` — **step 2**: replacing every inner `S_f(⌊N/p⌋)` by its own
  prime average, for any chosen prime range `P` with `⌊N/p⌋ ≥ 2`, costs exactly the sum of the individual
  averaging errors:

  `∑_{p ∈ P} log p · (9 + mertensTail)·⌊N/p⌋/log⌊N/p⌋`.

The result is the double prime average — the triple multiplicative convolution GHS feed to
Cauchy–Schwarz. `P` and the condition `⌊N/p⌋ ≥ 2` are choices of range, not assumptions about `f`.

### The one arithmetic estimate that remains for step 2

`∑_{p ≤ N} (log p)/(p·log(N/p)) ≪ log log N`.

Its proof is a dyadic decomposition of the prime range in `u = log p/log N`: on the block
`P_j = (N^{1−2^{−j}}, N^{1−2^{−j−1}}]` one has `1/log(N/p) ≤ 2^{j+1}/log N`, while `MertensBlock` gives
that block's mass as `2^{−j−1} log N + O(1)`; each block therefore contributes `1 + O(2^{j}/log N)`, and
the number of blocks that are nonempty is `≍ log log N`. Nothing else in step 2 is missing.

## Eighth brick: step 2, the second application of the recursion

`RHTower/Sieve/MultiplicativePrimeAverage.lean` (green, axiom-clean, wired):

* `norm_sum_Icc_sub_prime_average_le` — **the averaged recursion**, the prime-only recursion divided by
  `log N`:

  `‖S_f(N) − (∑_{p ≤ N} f(p) log p S_f(⌊N/p⌋))/log N‖ ≤ (9 + mertensTail)·N/log N`   (`N ≥ 2`);

* `norm_prime_average_le` — the prime average at its trivial size, `≤ N log N + O(N)`;
* `norm_sum_primes_sub_double_average_le` — **step 2**: replacing every inner `S_f(⌊N/p⌋)` by its own
  prime average, for any chosen prime range `P` with `⌊N/p⌋ ≥ 2`, costs exactly the sum of the individual
  averaging errors `∑_{p ∈ P} log p · (9 + mertensTail)·⌊N/p⌋/log⌊N/p⌋`.

The result is the double prime average — the triple multiplicative convolution GHS feed to
Cauchy–Schwarz. `P` and the condition `⌊N/p⌋ ≥ 2` are choices of range, not assumptions about `f`.

### The one arithmetic estimate that remains for step 2

`∑_{p ≤ N} (log p)/(p · log⌊N/p⌋) ≪ log log N`, for which there is a decomposition needing no real
powers at all: group the primes by the **dyadic size of the quotient**,

`B_j = {p : 2^j ≤ ⌊N/p⌋ < 2^{j+1}} = {p : ⌊N/2^{j+1}⌋ < p ≤ ⌊N/2^j⌋}`,

an interval of integers with integer endpoints. On `B_j` one has `log⌊N/p⌋ ≥ j log 2`, while
`MertensBlock` gives the block mass `log⌊N/2^j⌋ − log⌊N/2^{j+1}⌋ + O(1) = log 2 + O(1)`. So block `j`
contributes `O(1/j)`, and the harmonic sum over `j ≤ log₂ N` is `O(log log N)`.

## Ninth brick: the `log log` estimate, and step 2 is complete

`RHTower/Sieve/PrimeLogQuotientSum.lean` (green, axiom-clean, wired):

`∑_{p ≤ N, ⌊N/p⌋ ≥ 2} (log p)/(p · log⌊N/p⌋) ≤ ((log 3 + 2C)/log 2)·(1 + log⌊log₂ N⌋)`,
`C = (log 4 + 4) + (8 + mertensTail)`.

That is `O(log log N)`, which is what step 2's error budget needs, and the proof uses **no real powers at
all**:

* `two_pow_le_div_iff` — `2^j ≤ ⌊N/p⌋ ↔ p ≤ ⌊N/2^j⌋`, so the dyadic fibre of the quotient is an
  interval of integers with integer endpoints;
* `logQuotient_fiber_subset` — `{p : Nat.log 2 ⌊N/p⌋ = j} ⊆ (⌊N/2^{j+1}⌋, ⌊N/2^j⌋]`;
* `div_two_pow_le` — the endpoints are within a factor `3`: `⌊N/2^j⌋ ≤ 2⌊N/2^{j+1}⌋ + 1`;
* `sum_logQuotientFiber_prime_log_div_le` — hence each fibre's Mertens mass is `≤ log 3 + 2C`, the top
  fibre being empty of primes;
* `sum_prime_log_div_inv_log_quotient_le` — on the fibre `log⌊N/p⌋ ≥ j log 2`, so fibre `j` contributes
  `O(1/j)`, and `Finset.sum_fiberwise_of_maps_to` plus the corpus's own
  `sum_Icc_one_div_le_one_add_log` turn the total into a harmonic sum over `j ≤ log₂ N`.

**Step 2 of the GHS skeleton is now complete**: `norm_sum_primes_sub_double_average_le` reduces its error
to exactly this sum (after `⌊N/p⌋ ≤ N/p`), and this card's estimate bounds it by `O(N log log N)`, i.e.
`O(N log log N/log N)` after the division by `log N` — GHS's error term.

Remaining: step 3 (the dyadic partition of the prime range, now pure bookkeeping over `MertensBlock`) and
step 4's outer Perron passage.

## Tenth brick: the geometric blocking of step 3, without real powers

GHS partition the primes into `P_k = (x^{1−e^{1−k}}, x^{1−e^{−k}}]`, whose Mertens mass decays like
`e^{−k} log x`.  The same blocking is available with **integer** endpoints: a window of dyadic quotient
sizes.  Appended to `RHTower/Sieve/PrimeLogQuotientSum.lean`:

* `quotient_window_subset` — `{p : 2^m ≤ ⌊N/p⌋ < 2^n} ⊆ (⌊N/2^n⌋, ⌊N/2^m⌋]`;
* `div_two_pow_le_window` — `⌊N/2^m⌋ ≤ 2^{n−m}⌊N/2^n⌋ + 2^{n−m}`, so the endpoints are within
  `2^{n−m+1}`;
* `sum_quotient_window_prime_log_div_le` — **the window's Mertens mass**:

  `∑_{p : 2^m ≤ ⌊N/p⌋ < 2^n} (log p)/p ≤ ((n − m) + 1)·log 2 + 2C`.

Taking `m = 2^i`, `n = 2^{i+1}` gives exactly GHS's geometric blocks: block `i` has mass `≍ 2^i log 2`,
and on it `log⌊N/p⌋ ≥ 2^i log 2`, so the trivial bound for the corresponding piece of the triple
convolution is `O(2^i x)` — geometric in `i`, which is what makes the low blocks summable and leaves only
`O(log(log x/L))` blocks for the analytic estimate.  This subsumes the `n = m+1` case
(`sum_logQuotientFiber_prime_log_div_le`) up to the constant.

No real powers anywhere in the blocking: `2^m ≤ ⌊N/p⌋ ↔ p ≤ ⌊N/2^m⌋` does all the work.

## Eleventh brick: step 3's trivial bound per window

`RHTower/Sieve/TripleConvolutionWindow.lean` (green, axiom-clean, wired):

* `norm_inner_double_le` — the inner double sum at its trivial size:
  `‖∑_{q ≤ M} f(q) log q · S_f(⌊M/q⌋)‖ ≤ M(log M + C)`, by Mertens' first theorem against `‖S_f‖ ≤ ·`;
* `norm_window_triple_le` — **the window's contribution**: for `1 ≤ m ≤ n`,

  `‖∑_{p : 2^m ≤ ⌊N/p⌋ < 2^n} f(p) log p/log⌊N/p⌋ · (inner double sum at ⌊N/p⌋)‖
      ≤ (1 + C/log 2)·N·(((n − m) + 1)·log 2 + 2C)`.

The two factors are exactly GHS's: the inner sum contributes `⌊N/p⌋ log⌊N/p⌋`, which cancels the outer
`1/log⌊N/p⌋` and leaves `N·(log p)/p`; summing that over the window is the window's Mertens mass. With
`m = 2^i`, `n = 2^{i+1}` the bound is `O(2^i N)` — geometric in the block index, so all blocks below the
analytic range sum to `O(2^{i₀} N)`, which is `O(N·L(x))` for the right cut `i₀`.

Step 3 now needs only the choice of the cut and the summation of the two regimes; step 4's outer Perron
passage is the one analytic ingredient still missing.

## Twelfth brick: step 3 is complete — one threshold, no block summation

`RHTower/Sieve/DoubleAverageSplit.lean` (green, axiom-clean, wired):

* `filter_large_quotient_eq` — the primes with a large quotient form an **initial segment**:
  `{p : 2^n ≤ ⌊N/p⌋} = {p ≤ ⌊N/2^n⌋}`;
* `sum_split_at_quotient_threshold` — the prime range splits at the threshold;
* `doubleAverageTerm f N p` — the summand of the double prime average;
* `norm_double_average_sub_initial_le` — **step 3**: for `n ≥ 1`,

  `‖∑_{p : ⌊N/p⌋ ≥ 2} term − ∑_{p ≤ ⌊N/2^n⌋} term‖ ≤ (1 + C/log 2)·N·(n·log 2 + 2C)`.

GHS's block bookkeeping disappears: because the window bound is already additive in the number of dyadic
scales the window spans, the union of all discarded blocks is a *single* window `2 ≤ ⌊N/p⌋ < 2^n`, and one
application of `norm_window_triple_le` bounds it by `O(N·n)`. Their discarded part is `x·L/100`, obtained
at `n ≍ L`; the surviving part is the restriction to the initial segment `p ≤ ⌊N/2^n⌋`, which is exactly
the range on which step 4's Dirichlet polynomials live.

**Status of the skeleton: steps 1, 2, 3 complete; step 4's Lemma 1 complete over the whole frequency
line.** The single remaining ingredient is step 4's outer Perron passage — extracting the initial-segment
sum from its Dirichlet series — for which the corpus's exact smoothed identity
(`SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral`, kernel Lorentzian by
`exists_bound_mellin_smoothWeight_line`) is the candidate at smoothing scale `H = N/(log N)³`.

## Thirteenth brick: the triple hyperbola identity, and a generalisation

`RHTower/Sieve/TripleSummatorySwap.lean`:

* `sum_Icc_mul_mul_apply` — `∑_{m ≤ N} (a*(b*c))(m) = ∑_{p ≤ N} a(p) ∑_{q ≤ ⌊N/p⌋} b(q) ∑_{k ≤ ⌊N/p/q⌋} c(k)`,
  two lines from the corpus's own summatory swap applied twice;
* `le_div_div_iff` — the nested floors are the hyperbola: `k ≤ ⌊⌊N/p⌋/q⌋ ↔ pqk ≤ N`.

To get there, `RHTower.sum_Icc_mul_apply` (`DirichletSummatorySwap`) was **generalised from
`ArithmeticFunction ℝ` to `ArithmeticFunction R` for any semiring** — its proof is scalar-agnostic
(`sum_sigma`, `divisorsAntidiagonal`, `sum_nbij'`), and all four existing users (`VonMangoldtLogSummatory`,
`ChebyshevPsiLogSummatory`, `MoebiusFloorSummatory`, `VonMangoldtConvHarmonicSummatory`) still build
unchanged. That removes the need for a ℂ-valued copy, which is what the GHS convolution requires.

This is the identity step 4's Perron passage consumes: after two applications of the log recursion the
partial sum is a triple convolution, and Perron applies to `∑_{m ≤ N} d(m)` with `D(s) = A(s)B(s)C(s)`.
The remaining obstacle is that `d` is not bounded — its coefficients carry two logarithms — so the
corpus's smoothed Perron identity (stated for `‖a n‖ ≤ 1`) needs its hypothesis relaxed to polynomial
growth. That is the next brick.

## Fourteenth brick: step 4's outer Perron passage

`RHTower/Sieve/TripleConvolutionPerron.lean` (green, axiom-clean, wired):

`2π ∑ₙ (a ⍟ (b ⍟ c))(n)·w(n) = ∫_ℝ L(a,s_y)·L(b,s_y)·L(c,s_y)·W(s_y) dy`,   `s_y = σ + iy`, `σ > 1`,

with `w` the smoothing weight and `W` its Mellin transform.  The only hypotheses are `LSeriesSummable` for
each factor at `σ` — **no boundedness of the coefficients**, which is essential: the convolution produced
by two applications of the log recursion carries two logarithms.

The premise that looked like the obstacle was already discharged inside the corpus:

* `RHTower.Sieve.tsum_mul_smoothWeight_eq_integral_summable` (`Sieve/PerronSummable`) is exactly the
  smoothed Perron identity with the boundedness hypothesis replaced by absolute summability — the
  generalisation this card said was "the next brick" was already there;
* `RHTower.Sieve.summable_norm_mul_rpow_of_LSeriesSummable` (`Sieve/VonMangoldtPerron`) is the glue
  converting `LSeriesSummable` into that form (my duplicate of it was deleted before commit);
* mathlib's `LSeriesSummable.convolution` and `LSeries_convolution'` supply the summability and the
  product identity.

So the whole outer passage is assembly, and step 4 now has both of its analytic inputs: this identity and
`integral_lorentz_normSq_logPoly_le_prime_sieve` (Lemma 1 over the whole line).  What remains is the
Cauchy–Schwarz assembly itself, the definition of `L(x)`, and the smoothing-versus-sharp-cutoff error at
`H = N/(log N)³`.
