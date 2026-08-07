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

## Fifteenth brick: the Cauchy–Schwarz device of step 4

`HTGeometry/WeightedCauchySchwarz.lean` (green, axiom-clean, wired):

`‖∫ g₁ g₂ W‖ ≤ (∫ ‖g₁‖²‖W‖)^{1/2}·(∫ ‖g₂‖²‖W‖)^{1/2}`,

for any measurable `g₁, g₂, W` whose two weighted mean squares are integrable.  Splitting the weight
symmetrically, `‖g₁ g₂ W‖ = (‖g₁‖√‖W‖)(‖g₂‖√‖W‖)`, reduces it to Hölder with conjugate exponents `2, 2`
(mathlib's `integral_mul_le_Lp_mul_Lq_of_nonneg`, `Real.HolderConjugate.two_two`).

It lives in `HTGeometry` because nothing about it is arithmetic.  Combined with
`tsum_mul_smoothWeight_convolution_eq_integral` it is GHS's step-4 split: with `g₁ = A`, `g₂ = B·F` and
`W` the smoothing kernel,

`‖2π ∑ₙ (a ⍟ (b ⍟ c))(n) w(n)‖ ≤ (∫ ‖A‖²‖W‖)^{1/2}·(∫ ‖B F‖²‖W‖)^{1/2}`,

in which the first factor is a prime-supported mean square (`Lemma 1`) and the second pairs the pointwise
Euler-product bound against the Lorentzian-weighted mean square.

The three analytic devices of step 4 — Perron for a triple convolution, Cauchy–Schwarz against the
kernel, and the prime-supported mean square — are now all in the corpus.

## Sixteenth brick: the smoothing error for unbounded coefficients

`HTGeometry/SmoothWeightWindow.lean` (green, axiom-clean, wired):

`‖∑_{n < m} a(n)·w(n) − ∑_{n ≤ K} a(n)‖ ≤ ∑_{K < n ≤ ⌊K+H⌋} ‖a(n)‖`   whenever `K + H ≤ m`,

with **no hypothesis on the coefficients**.  Above `K+H` the weight vanishes and the sharp sum omits the
term too, so the whole difference lives in the transition window, where the weight is in `[0,1]`.

The corpus's `norm_weighted_sub_partialSum_le` is the unit-bounded case, where the window mass is `≤ H+1`.
The general form is what the triple convolution needs: its coefficients carry two logarithms, so the window
mass must be estimated arithmetically (a divisor-type bound) rather than by counting terms.

With this, every passage of step 4 is available in the corpus:

| Passage | Declaration |
|---|---|
| sharp cutoff → smoothed sum | `norm_weighted_sub_partialSum_le_window` |
| smoothed sum → vertical integral | `tsum_mul_smoothWeight_convolution_eq_integral` |
| integral → two mean squares | `norm_integral_mul_mul_le_sqrt_mul_sqrt` |
| prime-supported mean square | `integral_lorentz_normSq_logPoly_le_prime_sieve` |
| Lorentzian mean square of a general polynomial | `integral_lorentz_normSq_logPoly_le_count` |

What is left is not a missing device but the instantiation: choosing `H = N/(log N)³`, naming the three
coefficient sequences produced by steps 2–3, defining `L(x)`, and estimating the window mass of the triple
convolution.

## Which Perron device step 4 must use — and why the cheap ones fail

The smoothing error is now available in the sharp form
`‖smoothed − sharp‖ ≤ √H · √(∑_{K<n≤⌊K+H⌋} ‖d(n)‖²)` (`norm_weighted_sub_partialSum_le_sqrt`), so the
remaining question is which quantity one is willing to estimate for the triple-convolution coefficients
`d = a ⍟ (b ⍟ c)`, whose size is `‖d(n)‖ ≲ (log x)² d₃(n)`.

Three routes were considered and two are dead:

1. **Fine smoothing** (`H = x/(log x)^A`).  The error needs `∑_{x<n≤x+H} d₃(n)²` or `∑_{x<n≤x+H} d₃(n)`
   — a *short-interval* divisor estimate.  An upper bound for `∑_{n≤x} d₃(n)` does not give it; one needs
   either Shiu's theorem or the Piltz asymptotic with a power-saving error.  Both are substantial.
2. **Coarse smoothing** (`H ≍ x`, e.g. the Cesàro weight of PNTPlus's `x^s/(s(s+1))` Perron formula,
   which is *exact* and needs no error analysis).  Here the sharp-versus-smoothed difference is
   `∑_{n≤x} d(n)·(n/x)`, a full sum of size `≍ x(log x)⁴`, not small.  Higher-order Riesz means move the
   problem back to a window sum, i.e. back to route 1.
3. **Truncated Perron with the `1/s` kernel.**  Its error is the *global* sum
   `≪ (x^σ/T) ∑_n ‖d(n)‖/n^σ` at `σ = 1 + 1/log x`, which is `≍ x(log x)^c/T` — bounded by a
   Mertens-type global estimate only, with no short-interval input at all.  With `T` a fixed power of
   `log x` the error is `x/(log x)^{B−c}`, inside GHS's budget.

So the crux is genuinely Perron's lemma: for `y > 0`, `y ≠ 1`, `σ > 0`, `T > 0`,

`|(1/2πi)∫_{σ−iT}^{σ+iT} y^s ds/s − 1_{y>1}| ≪ y^σ · min(1, 1/(T|log y|))`,

whose proof is a contour shift plus the residue at `s = 0`.  PNTPlus supplies the rectangle machinery
(`Rectangle`, `ResidueCalcOnRectangles`, `RectangleIntegral`) but its own Perron file works with the
absolutely integrable kernel `x^s/(s(s+1))`, which is route 2 and therefore not usable here.  This is the
one remaining analytic development of the whole chain, and it is classical and unconditional.

## Seventeenth brick: the horizontal segments of the truncated Perron contour

`HTGeometry/PerronKernelSegments.lean` (green, axiom-clean, wired) — the first piece of Perron's lemma:

* `integral_exp_mul_const` — `∫_a^b e^{uL} du = (e^{bL} − e^{aL})/L`;
* `norm_integral_horizontal_le` — for `y > 1`, `T > 0`, `−A ≤ σ`:

  `‖∫_{−A}^{σ} y^{u+iT}/(u+iT) du‖ ≤ y^σ/(T log y)`,   **uniformly in `A`**.

On the horizontal segment the kernel is elementary: `‖y^s‖ = y^{Re s}` and `‖s‖ ≥ T`, so the integrand is
at most `y^u/T` and the `u`-integral is at most `y^σ/log y`.  This is precisely the estimate that produces
Perron's `min(1, 1/(T|log y|))` factor — the factor whose absence in the smoothed routes forced them to
need a short-interval divisor estimate.

Remaining for Perron's lemma: the contour shift itself (residue `1` at `s = 0` for `y > 1`, none for
`y < 1`) and the vanishing of the left edge as `A → ∞`.  PNTPlus's `Rectangle` and
`ResidueCalcOnRectangles` are the intended tools.

### The other two elementary pieces of Perron's lemma

Also in `HTGeometry/PerronKernelSegments.lean`:

* `norm_integral_vertical_edge_cpow_le` — on the line `Re s = a` (`a ≠ 0`) the truncated edge satisfies
  `‖∫_{−T}^{T} y^{a+it}/(a+it) dt‖ ≤ 2T·y^a/|a|`.  For `y > 1` and `a = −A` this tends to `0` as
  `A → ∞`, which is what licenses the leftward contour shift; for `y < 1` and `a = +A` likewise.
* `norm_integral_horizontal_le'` — the `y < 1` companion of the horizontal bound, shifting rightwards:
  `‖∫_σ^A y^{u+iT}/(u+iT) du‖ ≤ y^σ/(T|log y|)`, uniformly in `A`.

Both are elementary: `‖y^s‖ = y^{Re s}`, and `‖s‖` is at least `|Re s|` on a vertical line and at least
`|Im s|` on a horizontal one.  Note the name `norm_integral_vertical_edge_le` was already taken in
`RHTower.Sieve` (`VerticalMassSharp`, a different statement about the smoothing kernel), hence the
`_cpow_` in this one.

With the three segment bounds in place, what is left of Perron's lemma is purely the residue calculus:
the rectangle `[−A, σ] × [−T, T]` winds once around `s = 0` with residue `1` when `y > 1`, and the
rectangle `[σ, A] × [−T, T]` contains no pole when `y < 1`.

## Eighteenth brick: the residue of the Perron kernel

`RHTower/Sieve/PerronKernelResidue.lean` (green, axiom-clean, wired):

`RectangleIntegral' (fun s => y^s/s) z w = 1` for every rectangle whose interior contains `0`, `y > 0`.

The principal part of `y^s/s` at the origin is exactly `1/s`, because the slope `(y^s − 1)/s` tends to
`log y` — that is `hasStrictDerivAt_const_cpow` plus `hasDerivAt_iff_tendsto_slope` plus
`Filter.Tendsto.isBigO_one`.  The residue theorem itself is **PNTPlus's**
`ResidueTheoremOnRectangleWithSimplePole'`, reused as is; only the principal part of this kernel is new.

### Perron's lemma is now a finite assembly

The rectangle integral is the difference of the two vertical edges plus the two horizontal ones.  With

* `rectangleIntegral'_cpow_div_eq_one` — the rectangle value is `1` when `0` is inside (`y > 1` case,
  rectangle `[−A, σ] × [−T, T]`), and `0` when it is not (`y < 1` case, rectangle `[σ, A] × [−T, T]`,
  by `HolomorphicOn.vanishesOnRectangle`, also PNTPlus);
* `norm_integral_vertical_edge_cpow_le` — the far edge is `≤ 2T·y^{∓A}/A → 0`;
* `norm_integral_horizontal_le`, `norm_integral_horizontal_le'` — each horizontal piece is
  `≤ y^σ/(T|log y|)`, uniformly in `A`,

Perron's lemma
`|(1/2πi)∫_{σ−iT}^{σ+iT} y^s ds/s − 1_{y>1}| ≤ y^σ/(πT|log y|)`
follows by letting `A → ∞`.  Every ingredient is in the tree; what remains is the limit bookkeeping.

## Nineteenth brick: Perron's lemma, the `y < 1` half

`RHTower/Sieve/PerronVerticalBound.lean` (green, axiom-clean, wired):

`‖∫_{-T}^{T} y^{σ+it}/(σ+it) dt‖ ≤ 2·y^σ/(|T|·|log y|)`   for `0 < y < 1`, `σ > 0`, `T > 0`.

The rectangle `[σ, A] × [−T, T]` lies in the right half-plane, so it contains no pole and its boundary
integral vanishes — PNTPlus's `HolomorphicOn.vanishesOnRectangle`.  Reading the four sides off
`RectangleIntegral` expresses the wanted vertical integral as the two horizontal sides plus the far
vertical one, each already bounded uniformly in `A`, and `ge_of_tendsto` with `y^A → 0` removes the far
side in the limit.

The horizontal bounds had to hold at height `−T` as well as `+T`, which is why the segment lemmas were
generalised to `T ≠ 0` with `|T|` in the denominator first.

Remaining for the full lemma: the `y > 1` half — the same argument with the rectangle `[−A, σ] × [−T, T]`,
whose interior contains the origin, so the boundary value is the residue `1` (already proved as
`rectangleIntegral'_cpow_div_eq_one`) instead of `0`.

## Twentieth brick: Perron's lemma is complete

`RHTower/Sieve/PerronVerticalBound.lean` now carries both halves, for `σ > 0`, `T > 0`:

* `norm_vertical_perron_le_of_lt_one` — `0 < y < 1`:
  `‖∫_{−T}^{T} y^{σ+it}/(σ+it) dt‖ ≤ 2y^σ/(|T||log y|)`;
* `norm_vertical_perron_sub_two_pi_le_of_one_lt` — `y > 1`:
  `‖∫_{−T}^{T} y^{σ+it}/(σ+it) dt − 2π‖ ≤ 2y^σ/(|T| log y)`.

The constant is `2π`, not `2πi`: the contour integral `∫_{σ−iT}^{σ+iT} … ds` equals `i∫_{−T}^{T} … dt`, so
the `i` cancels against the `1/2πi` of the normalisation.  The two proofs are the same rectangle argument
in mirror image — to the right of the line (no pole, boundary value `0`) and to the left (pole at the
origin, boundary value `2πi` by `rectangleIntegral'_cpow_div_eq_one`) — with the far vertical edge killed
by `y^{∓A} → 0` and each horizontal side bounded uniformly in `A`.

**Every analytic device the GHS chain needs is now in the corpus.** Steps 1–3 are complete; step 4 has its
Perron passage for a triple convolution, the weighted Cauchy–Schwarz split, the prime-supported mean
square, the Lorentzian mean square, the smoothing-window error, and now Perron's lemma with the sharp
`1/s` kernel, whose error is a global Dirichlet-series sum rather than a short-interval divisor estimate.

## Correction: the coefficients are polylog, so no divisor estimate is needed anywhere

The no-go recorded above ("every smoothed route needs a short-interval divisor estimate") rested on
`‖d(n)‖ ≲ (log x)² d₃(n)`.  **That over-estimates the triple convolution.**  Two of its three factors are
supported on primes, so a factorisation `n = pqk` contributing to `d(n)` is determined by a *pair of prime
divisors* of `n`:

`‖d(n)‖ ≤ ∑_{p, q prime, pq ∣ n} (log p)(log q) ≤ (ω(n)·log n)² ≤ (log n)⁴/(log 2)²`,

using `ω(n) ≤ log n/log 2`.  The coefficients are therefore **polylogarithmic pointwise** — there is no
divisor function in them at all.

Consequences:

* the fine-smoothing error `∑_{x<n≤x+H} ‖d(n)‖ ≪ H(log x)⁴` is `≤ x/(log x)²` already at
  `H = x/(log x)⁶`, with no arithmetic input;
* the near-diagonal block of the truncated Perron error, `∑_{|n−x| ≤ x/T} ‖d(n)‖ ≪ (x/T)(log x)⁴`, is
  likewise small at `T = (log x)⁶`;
* so **both** routes are viable, and neither needs Shiu's theorem or the Piltz asymptotic.

The truncated Perron lemma proved above is still worth having (it is the sharp classical device, and it is
the one that keeps `T` a free parameter), but the chain no longer depends on it: the exact smoothed
identity `tsum_mul_smoothWeight_convolution_eq_integral` together with
`norm_weighted_sub_partialSum_le_window` suffices.

The corpus does own Dirichlet's divisor asymptotic with power saving —
`RHTower.abs_sum_div_sub_dirichlet_le`, `|∑_{d ≤ N}⌊N/d⌋ − N log N − (2γ−1)N| ≤ 20√N` — so a `d₂`
short-interval bound is available by differencing if some later step wants it.  It is not needed here.

**Next brick:** the pointwise bound above, `‖(a ⍟ (b ⍟ c))(n)‖ ≤ (ω(n) log n)²` for prime-supported `a, b`
with `‖a_p‖ ≤ log p`, `‖b_q‖ ≤ log q`, `‖c‖ ≤ 1`.

## Twenty-first brick: the polylog bound, proved

`RHTower/Sieve/PrimeSupportedConvolutionBound.lean` (green, axiom-clean, wired):

* `filter_prime_divisors_eq_primeFactors` — the prime divisors among the divisors are `n.primeFactors`;
* `norm_convolution_prime_support_le` — `‖(b ⍟ c)(m)‖ ≤ ω(m)·log m` for `b` prime-supported with
  `‖b_q‖ ≤ log q` and `‖c‖ ≤ 1`;
* `norm_convolution_triple_prime_support_le` — `‖(a ⍟ (b ⍟ c))(n)‖ ≤ ω(n)²·(log n)²` when both `a` and `b`
  are prime-supported.

Mechanism: expanding a convolution as `∑_{q ∣ m} b(q)·c(m/q)` (`Nat.sum_divisorsAntidiagonal`), every term
with `b(q) ≠ 0` has `q` prime and `q ∣ m`, so the support of the sum is `m.primeFactors` and each term is
at most `log m`.  Iterating gives the square.

With `ω(n) ≤ log n/log 2` this is `(log n)⁴/(log 2)²`, so the correction recorded above is now formal: the
triple convolution's coefficients are polylogarithmic, and **no short-interval divisor estimate appears
anywhere in the chain**.

### The bound in closed form

Appended to the same module:

* `two_pow_card_primeFactors_le` — `2^{ω(n)} ≤ n`, from `Nat.prod_primeFactors_dvd` and `p ≥ 2`;
* `card_primeFactors_mul_log_two_le_log` — hence `ω(n)·log 2 ≤ log n`;
* `norm_convolution_triple_le_log_pow` — **`‖(a ⍟ (b ⍟ c))(n)‖ ≤ (log n)⁴/(log 2)²`**.

That is the closed form the error budgets consume.  The window mass over `(K, K+H]` is at most
`(H+1)(log(K+H))⁴/(log 2)²` with no arithmetic input at all, so the smoothing error at `H = x/(log x)⁶` is
`O(x/(log x)²)` — inside GHS's budget by two logarithms.

## Twenty-second brick: the smoothing error of the triple convolution, closed form

`RHTower/Sieve/ConvolutionSmoothingError.lean` (green, axiom-clean, wired):

`‖∑_{n<m} d(n)·w(n) − ∑_{n≤K} d(n)‖ ≤ (⌊K+H⌋ − K)·(log⌊K+H⌋)⁴/(log 2)²`   whenever `K + H ≤ m`,

for `d = a ⍟ (b ⍟ c)` with `a, b` prime-supported (`‖a_p‖ ≤ log p`, `‖b_q‖ ≤ log q`, `‖c‖ ≤ 1`).

This is the window bound against the pointwise coefficient bound: `⌊K+H⌋ − K` terms, each at most
`(log⌊K+H⌋)⁴/(log 2)²`.  At `H = K/(log K)⁶` it reads `O(K/(log K)²)`.

**Step 4's chain is now closed end to end with explicit constants**: sharp cutoff → smoothed sum (this
brick) → vertical integral (`tsum_mul_smoothWeight_convolution_eq_integral`) → two mean squares
(`norm_integral_mul_mul_le_sqrt_mul_sqrt`) → prime-supported mean square
(`integral_lorentz_normSq_logPoly_le_prime_sieve`) and Lorentzian mean square
(`integral_lorentz_normSq_logPoly_le_count`).  No step is conditional and no step needs an arithmetic
input that is not already in the tree.

## Twenty-third brick: the GHS coefficient sequences, and the uniform smoothing law

`RHTower/Sieve/GhsCoefficients.lean` (green, axiom-clean, wired) names the three sequences that the two
applications of the logarithmic recursion produce, for any `f` with `‖f‖ ≤ 1`:

* `ghsOuter f N p = f(p)·log p/log⌊N/p⌋` on primes with `⌊N/p⌋ ≥ 2`, zero elsewhere;
* `ghsInner f q = f(q)·log q` on primes, zero elsewhere;
* `f` itself.

`norm_ghsOuter_le : ‖ghsOuter f N p‖ ≤ (1/log 2)·log p` — the denominator is at least `log 2` on the
support — and `norm_ghsInner_le : ‖ghsInner f q‖ ≤ log q`, both with prime support, whence

`norm_ghsTriple_le : ‖(ghsOuter f N ⍟ (ghsInner f ⍟ f))(n)‖ ≤ (log n)⁴/(log 2)³`.

To make this usable the polylogarithmic bounds were generalised to carry constants
(`norm_convolution_prime_support_le_const`, `norm_convolution_triple_prime_support_le_const`,
`norm_convolution_triple_le_log_pow_const`: `‖a_p‖ ≤ A log p`, `‖b_q‖ ≤ B log q` give
`A·B·(log n)⁴/(log 2)²`); the unit-constant statements survive as one-line corollaries.  The constant is
not cosmetic — in the dyadic quotient window `2^m ≤ ⌊N/p⌋` the outer weight obeys
`‖a_p‖ ≤ log p/(m log 2)`, so the constant *improves* with the block index.

`ConvolutionSmoothingError.lean` was refactored under the law it was an instance of:

`norm_weighted_sub_partialSum_le_uniform` — window length times any uniform coefficient bound on
`(K, ⌊K+H⌋]`, for an arbitrary coefficient sequence.

Both the general triple convolution and the GHS instance are now one-line corollaries of it
(`… ≤ (⌊K+H⌋ − K)·(log⌊K+H⌋)⁴/(log 2)²` and `… /(log 2)³`).

## Twenty-fourth brick: the smoothed sum is connected to the sharp partial sum

`RHTower/Sieve/SmoothedPartialSumConnector.lean` (green, axiom-clean, wired).

The corpus's Halász layer (`HalaszPerronAssembly`) bounds the *smoothly* cut series `∑ₙ f(n)w(n)`; a mean
value theorem is a statement about `∑_{n ≤ K} f(n)`.  The gap is exactly the transition window:

* `tsum_mul_smoothWeight_eq_sum_range` — the smooth cutoff vanishes past `K + H`, so the weighted series
  is the finite sum over any range containing the window;
* `card_smoothing_window_le` — the window `(K, ⌊K+H⌋]` has at most `H` elements;
* `norm_partialSum_le_of_smoothed_bound` — for `‖f‖ ≤ 1`,
  `‖∑_{n ≤ K} f(n)‖ ≤ B/(2π) + H` whenever `2π‖∑ₙ f(n)w(n)‖ ≤ B`.

The third is a pure connector: its hypothesis is verbatim the conclusion of the assembled Halász bound, so

* `exists_norm_partialSum_le_halasz` — the corpus's `exists_norm_tsum_mul_smoothWeight_le`, transported to
  the sharp partial sum of a bounded multiplicative function, explicit in `z, δ, T, K, H` with the cost of
  removing the smoothing being exactly `H`.

This closes a premise that has been open in the corpus since the Halász assembly was built: the existing
route produced a bound only for the smoothed sum, and every application needs the sharp one.  It also
serves the GHS route, whose Perron step consumes the same window bound with polylogarithmic coefficients.

## Twenty-fifth brick: the smooth-versus-sharp comparison, as one law

The corpus had two half-devices for the same comparison: `HTGeometry.SmoothWeightWindow` handled a
*natural* cutoff `K` with an arbitrary `ℓ¹` window mass, and `RHTower/Sieve/SmoothVsSharp` handled a *real*
cutoff `N` but only for unimodular coefficients.  Neither covered what the routes actually need — a real
cutoff with polylogarithmic coefficients.

`HTGeometry/SmoothWeightWindow.lean` now carries the law both are cases of:

* `tsum_mul_smoothWeight_eq_sum_range_real` — the cutoff vanishes past `N + H`, so the weighted series is a
  finite sum (real `N`);
* `norm_weighted_sub_partialSum_le_window_real` — the difference lives on `(⌊N⌋, ⌊N+H⌋]`;
* `card_window_real_le` — that window holds at most `H + 1` integers;
* `norm_tsum_mul_smoothWeight_sub_partialSum_le_window` and `…_le_width` — for any uniform bound `C` on
  the window coefficients, the smoothing costs at most `(⌊N+H⌋ − ⌊N⌋)·C ≤ (H+1)·C`.

`SmoothVsSharp.norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one` is now the `C = 1` case, proved in three
lines instead of seventy, and the Möbius statement above it is unchanged.  The GHS route can take `C` to be
the polylogarithmic coefficient bound at a real cutoff `x`, which is what its parameter choices
(`H = x/(log x)⁶`) actually require.

## Twenty-sixth brick: the Perron passage, for the actual sequences

`RHTower/Sieve/GhsSummability.lean` (green, axiom-clean, wired).

`LSeriesSummable_of_norm_le_const_mul_log` — coefficients with `‖a_n‖ ≤ C·log n` are absolutely summable
on every line `Re s > 1`.  The proof is explicit rather than asymptotic: `log x ≤ x^ε/ε`, applied with
`ε = (Re s − 1)/2`, gives `a = O(n^ε)` and mathlib's `LSeriesSummable_of_isBigO_rpow` finishes.

Instantiated at the two prime weights (`LSeriesSummable_ghsOuter`, `LSeriesSummable_ghsInner`) and combined
with `LSeriesSummable_of_bounded_of_one_lt_re` for `f`, this discharges every hypothesis of the triple
Perron identity, giving

`tsum_mul_smoothWeight_ghs_eq_integral` :
`2π ∑ₙ (a ⍟ (b ⍟ f))(n) w(n) = ∫_ℝ L(a,σ+iy)·L(b,σ+iy)·L(f,σ+iy)·W(σ+iy) dy`

for every `f` with `‖f‖ ≤ 1`, every cutoff `N > 0`, width `H > 0` and every `σ > 1`.  The Perron step of
step 4 is now stated for the sequences the log recursion produces, not for abstract summable factors.

## Twenty-seventh brick: the mean square in the Perron variable

`RHTower/Sieve/LorentzianLSeriesLine.lean` (green, axiom-clean, wired).

The mean-square estimates of the corpus live in the Gallagher variable `w` (frequency `n^{2πiw}`); the
Perron passage delivers its integral in `y` (frequency `n^{-iy}`).  Three steps bridge them:

* `natCast_cpow_neg_eq` — the polar split `n^{-(σ+iy)} = n^{-σ}·e^{-iy log n}`, obtained from the corpus's
  `natCast_cpow_neg_eq_mul` and `conj_charFn` rather than re-derived;
* `LSeries_eq_logPoly_of_support` — a **finitely supported Dirichlet series is a Dirichlet polynomial**:
  `L(a, σ+iy) = logPoly (a_n n^{-σ}) s (-y/2π)`;
* `integral_lorentz_comp_neg_div_le` — the reflection and rescaling `y = -2πw` sends the weight `1/(1+y²)`
  to `2π/(1+4π²w²)`, dominated by `2π/(1+w²)`; stated for an arbitrary nonnegative continuous `F`, so it is
  reusable for any Lorentzian-weighted quantity, not just this mean square.

Consequences, in the variable the Perron integral uses:

`integral_lorentz_normSq_LSeries_le_count`  :
`∫_ℝ ‖L(a,σ+iy)‖² dy/(1+y²) ≤ 25π² ∑_{n ∈ s} #{m ∈ s : |log n − log m| < 1/2π}·‖a_n n^{-σ}‖²`;

`integral_lorentz_normSq_LSeries_le_prime_sieve` — the same with the count discharged by the Selberg sieve
for prime-supported coefficients.  This is GHS Lemma 1 on the Perron line, with the damping `n^{-σ}`
carried inside the coefficients where the Cauchy–Schwarz split needs it.
