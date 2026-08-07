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

## Twenty-eighth brick: the master inequality of the three-factor integral

`HTGeometry/WeightedCauchySchwarz.lean` (appended; green, axiom-clean):

* `norm_integral_mul_three_le_sup_mul_sqrt_mul_sqrt` — Cauchy–Schwarz with one factor bounded pointwise:
  absorbing the bounded factor into the weight gives
  `‖∫ g₁g₂g₃W‖ ≤ (sup‖g₃‖)·√(∫‖g₁‖²‖W‖)·√(∫‖g₂‖²‖W‖)`;
* `integrable_normSq_mul_weight_of_le`, `integral_normSq_mul_weight_le` — a weight dominated by `C/(1+y²)`
  transfers a mean square to the Lorentzian one at the cost of `C`;
* `norm_integral_mul_three_le_sup_mul_lorentz` — the two combined:

  `‖∫ g₁g₂g₃W‖ ≤ M·C·√(∫‖g₁‖²/(1+y²))·√(∫‖g₂‖²/(1+y²))`   for `‖g₃‖ ≤ M`, `‖W‖ ≤ C/(1+y²)`.

Nothing about Dirichlet series enters the statement; the hypotheses are exactly what a smoothed Perron
kernel (`exists_bound_mellin_smoothWeight_line`) and an Euler product bound
(`norm_tsum_twistedSummand_le_trivial`) supply.

`RHTower/Sieve/LorentzianLSeriesLine.lean` gains `integrable_lorentz_normSq_LSeries`, the integrability
side condition for a finitely supported series: the polynomial is bounded on the line by the `ℓ¹` mass of
its damped coefficients, and the kernel is integrable.

**Step 4 is now one substitution away from assembled**: the master inequality's three hypotheses are held
by the Euler bound, the kernel decay bound and the two prime-supported mean squares, all present.

## Step 4 is assembled

`RHTower/Sieve/EulerBoundLSeries.lean` and `RHTower/Sieve/GhsStepFour.lean` (green, axiom-clean, wired).

Two preparatory connectors:

* `LSeries_eq_tsum_twistedSummand` — away from `s = 0` the corpus's twisted-summand series *is* `LSeries`
  (they differ only at `n = 0`, where one inserts `0` and the other carries `0^{-s} = 0`); hence
  `norm_LSeries_le_trivial`: `‖L(f,s)‖ ≤ (1 + 1/(σ−1))e^{7/2}` for bounded multiplicative `f`.
* The inner prime weight now carries a cutoff, `ghsInner f M q = f(q)log q` for primes `q ≤ M`, so both
  prime weights have finite support (`ghsOuter_mem_Icc`: its condition forces `2p ≤ N`; `ghsInner_mem_Icc`).
  This is what makes the Dirichlet-polynomial mean squares applicable to them, and it is faithful to the
  argument, whose second recursion runs over `q ≤ N/p ≤ N`.

The assembly, `exists_norm_tsum_ghs_smoothWeight_le`:

`2π‖∑ₙ (a ⍟ (b ⍟ f))(n)w(n)‖ ≤ (1 + 1/(σ−1))e^{7/2} · C · (√(25π²·sieve a)·√(25π²·sieve b))`

for every bounded multiplicative `f`, every `N₀, M`, cutoff data `N, H`, every `σ > 1` and every admissible
sieve level `Y ≤ z`, with `C` the quadratic-decay constant of the smoothing kernel and
`sieveMeanSquare a s σ z Y` the Selberg-sieve majorant of the mean square of a prime-supported polynomial
on the line.

Every input is a named unconditional theorem of the corpus: the triple Perron identity, absolute convergence
of logarithmically bounded coefficients, the Euler bound, the master three-factor Cauchy–Schwarz inequality,
and GHS Lemma 1 on the Perron line.  **What remains is not a device but a computation**: choosing
`σ = 1 + 1/log x`, the sieve level, `H`, and evaluating the two sieve sums — the first of which is where
the `(1+M)e^{-M}` shape of the sharp Halász theorem finally appears.

## The two halves meet: the recursion output is the convolution's summatory function

`RHTower/Sieve/ConvolutionSummatorySwap.lean` and `RHTower/Sieve/GhsRecursionJoin.lean` (green, axiom-clean,
wired).  **Every statement in both modules is hypothesis-free.**

* `sum_Icc_convolution_apply`, `sum_Icc_convolution_triple_apply` — the summatory swap for plain sequences
  `ℕ → R` over any semiring, with no condition at `0`: a convolution evaluated at `n ≥ 1` never reads the
  value at `0`, so the corpus's arithmetic-function swap applies verbatim to the zero-extended sequences.
  `∑_{n ≤ N} (a ⍟ (b ⍟ c))(n) = ∑_{p ≤ N} a_p ∑_{q ≤ N/p} b_q ∑_{k ≤ N/p/q} c_k`.
* `sum_Icc_ghsTriple_eq_prime_double_average` — the join:

  `∑_{n ≤ N} (a ⍟ (b ⍟ f))(n) = ∑_p f(p)·log p/log⌊N₀/p⌋ ∑_q f(q)·log q ∑_{k ≤ N/pq} f(k)`,

  outer sum over primes `p ≤ N` with `⌊N₀/p⌋ ≥ 2`, inner over primes `q ≤ min(N/p, M)`.

The left side is what the Perron and mean-square steps estimate; the right side is what two applications of
the logarithmic recursion produce.  With this identity the two halves of the programme are the same object,
and the chain from `(∑_{n≤N} f(n))·log N` to the sieve mean squares is closed except for the numerical choice
of `σ, z, Y, H` and the evaluation of the two sieve sums.

## The second application of the recursion, with its error evaluated

`RHTower/Sieve/SecondLogRecursion.lean` (green, axiom-clean, wired).

* `norm_log_mul_partialSum_sub_inner_le` — at one prime: dividing the recursion at scale `⌊N/p⌋` by
  `log⌊N/p⌋` and weighting by `f(p)log p`,
  `‖f(p)log p·S(N/p) − (f(p)log p/log⌊N/p⌋)·T(N/p)‖ ≤ (9 + mertensTail)·(log p/log⌊N/p⌋)·⌊N/p⌋`,
  where `T` is the inner prime average.  The condition `⌊N/p⌋ ≥ 2` is exactly what keeps the divisor
  positive — the same condition that defines the support of `ghsOuter`.
* `norm_sum_primes_sub_double_prime_average_le` — the same summed over the outer primes.
* `sum_prime_log_div_log_quotient_mul_quotient_le` — the total weighted error against the dyadic
  quotient-window estimate: `∑_p (log p/log⌊N/p⌋)·⌊N/p⌋ ≤ N·(B/log 2)·(1 + log log₂ N)`.
* `norm_sum_primes_sub_double_prime_average_le_explicit` — hence the second application costs
  `O(N log log N)` against a main term of size `N log N`.

The saving of the second application is therefore a full logarithm up to `log log`, and it is the dyadic
quotient-window blocking that delivers it — no double-exponential dissection of the prime range is needed,
which is where the original argument spends a factor.

**The paper chain is now complete in Lean from `(∑_{n ≤ N} f(n))·log N` to the sieve mean squares**: step 1
(`norm_sum_Icc_mul_log_sub_sum_primes_le'`), step 2 (this module), the join
(`sum_Icc_ghsTriple_eq_prime_double_average`), and step 4 (`exists_norm_tsum_ghs_smoothWeight_le`) with the
smoothing connector (`norm_partialSum_le_of_smoothed_bound`).  What is left is the arithmetic evaluation of
`sieveMeanSquare` at the natural parameters.

## The paper half is closed: partial sum versus triple convolution

`RHTower/Sieve/PartialSumVsTripleConvolution.lean` (green, axiom-clean, wired).

`norm_sum_Icc_mul_log_sub_ghsTriple_le` :

`‖(∑_{n ≤ N} f(n))·log N − ∑_{n ≤ N} (a ⍟ (b ⍟ f))(n)‖
    ≤ (9+c)N + N log 4 + (9+c)·N·(B/log 2)·(1 + log log₂ N)`

for the two prime weights at `N₀ = M = N`, where the inner truncation is vacuous because the inner primes
already satisfy `q ≤ N/p ≤ N` (`sum_Icc_ghsTriple_self_eq`).

Three errors, all `O(N log log N)`:

1. the first recursion, `(9+c)N`;
2. the primes above `N/2`, whose inner partial sum is the single term `f(1)` — bounded by Chebyshev's
   `∑_{p ≤ N} log p ≤ N log 4`, which the corpus already owned (`sum_log_primesLE_le`), reached through
   `filter_prime_Icc_eq_primesLE` (`norm_sum_prime_head_le`);
3. the second recursion against the dyadic quotient window.

The left-hand object is what a mean value theorem is about; the right-hand object is what step 4 estimates.
Both halves of the programme are now closed in Lean, and they meet at this inequality:

* paper half: `(∑_{n≤N} f)·log N ≈ ∑_{n≤N} (a ⍟ (b ⍟ f))` with error `O(N log log N)`;
* analytic half: `2π‖∑ₙ (a ⍟ (b ⍟ f))(n)w(n)‖ ≤ (Euler)·(kernel)·√(sieve a)·√(sieve b)`, and
  `‖∑_{n≤K} d(n)‖ ≤ (that)/2π + H` for the sharp cutoff.

The only remaining input is arithmetic: evaluating `sieveMeanSquare` at the natural parameters.

## The master bound: the whole chain in one inequality

`RHTower/Sieve/HalaszGhsMasterBound.lean` (green, axiom-clean, wired).

`exists_norm_sum_Icc_mul_log_le` — for totally multiplicative `f` with `f(1) = 1`, `‖f‖ ≤ 1`, every `N ≥ 2`,
every width `H > 0`, every `σ > 1` and every admissible sieve level `Y ≤ z`:

`‖∑_{n ≤ N} f(n)‖·log N`
  `≤ [(9+c)N + N log 4 + (9+c)N(B/log 2)(1 + log log₂ N)]`
  `+ (H+1)·(log⌊N+H⌋)⁴/(log 2)³`
  `+ (1/2π)·(1 + 1/(σ−1))e^{7/2}·C·√(25π²·sieve a)·√(25π²·sieve b)`.

Supporting bricks: `sum_range_convolution_eq_sum_Icc` (a convolution vanishes at `0`, so the two ranges
agree) and `norm_tsum_ghs_smoothWeight_sub_sum_Icc_le` (the real-cutoff window law at `N ∈ ℕ`, with the
polylogarithmic coefficient bound as its uniform constant).

**The Granville–Harper–Soundararajan chain is discharged end to end in Lean, unconditionally.**  Every term
is explicit, no hypothesis assumes an estimate, and the three groups of errors are the recursion errors
`O(N log log N)`, the smoothing error, and the analytic term.

The remaining input is arithmetic: evaluating

`sieveMeanSquare a s σ z Y = ∑_{n ∈ s} (2(n(e^δ−e^{−δ})+1)/log Y + selbergFibreError z Y + z)·‖a_n n^{−σ}‖²`

at the natural parameters.  This is where a saving in `N` is created, and it is a prime-sum computation of
the kind the corpus's Mertens layer already supports — the mean square of the outer weight is
`∑_p (log p/log⌊N/p⌋)²p^{−2σ}` against a linear sieve count, and it is that pairing which produces the
`(1+M)e^{−M}` shape of the sharp theorem.

## The sieve mean square reduced to two zeta-type sums

`RHTower/Sieve/SieveMeanSquareZetaSums.lean` (green, axiom-clean, wired).

`sieveMeanSquare_le_of_norm_le_log` — the Selberg majorant `2(n·2 sinh δ + 1)/log Y + E + z` is linear in
`n`, so against coefficients with `‖a_n‖ ≤ A log n` it splits into exactly two sums:

`sieveMeanSquare a s σ z Y
    ≤ (4 sinh δ/log Y)·A²·∑_{n ∈ s} n^{1−2σ}(log n)² + (2/log Y + E + z)·A²·∑_{n ∈ s} n^{−2σ}(log n)²`.

The statement needs no positivity of `A` (the square supplies it) and no primality: only the coefficient
bound, `1 ≤ n` on the index set, `2 ≤ z` and `log Y > 0`.

Instantiations: `sieveMeanSquare_ghsInner_le` with `A = 1`, `sieveMeanSquare_ghsOuter_le` with `A = 1/log 2`.

Both sums converge for `σ > 1`; the first is the one that grows as `σ ↓ 1`, being of size `(log N)²` at
`σ = 1 + 1/log N`.  **The remaining analytic input of the whole programme is now exactly two sums**:

`∑_{n ≤ N} n^{1−2σ}(log n)²`   and   `∑_{n ≤ N} n^{−2σ}(log n)²`,

with no arithmetic content — no primes, no divisor functions, no short-interval estimates.  Each is a
Dirichlet-type sum of `(log n)²n^{-w}` and is bounded by the corresponding tail integral.

## The last analytic input: the logarithmically weighted partial zeta cap

`RHTower/Sieve/LogSqZetaCap.lean` (green, axiom-clean, wired).

`sum_Icc_logSq_rpow_neg_le` — a squared logarithm is absorbed by a power: `log t ≤ t^δ/δ` at
`δ = (w−1)/4` turns `n^{−w}(log n)²` into `(16/(w−1)²)n^{−(w+1)/2}`, and the corpus's partial zeta cap
(`RHTower.sum_Icc_rpow_neg_le`, reused, not rebuilt) finishes:

`∑_{n ≤ N} n^{−w}(log n)² ≤ (16/(w−1)²)·(1 + 2/(w−1))`,   `w > 1`, uniformly in `N`.

At the two exponents of the sieve majorant:

`∑_{n ≤ N} n^{1−2σ}(log n)² ≤ (16/(2σ−2)²)(1 + 2/(2σ−2))`   (`sum_Icc_logSq_rpow_one_sub_two_mul_le`),
`∑_{n ≤ N} n^{−2σ}(log n)² ≤ (16/(2σ−1)²)(1 + 2/(2σ−1))`   (`sum_Icc_logSq_rpow_neg_two_mul_le`).

At `σ = 1 + 1/log N` the first is of size `(log N)³` and the second is bounded.

**Every analytic input of the chain is now evaluated.**  From the master bound, the two sieve mean squares
are bounded by these caps, so the whole right-hand side is an explicit function of `N, H, σ, z, Y` alone.
The programme's remaining task is the parameter optimisation: choosing `σ`, the sieve level `Y ≤ z` and the
smoothing width `H` so that the sum of the three error groups beats the trivial bound `N log N` — the point
at which the argument becomes a mean value theorem rather than a chain of identities.

## The master bound with every quantity explicit

`RHTower/Sieve/HalaszExplicitParameters.lean` (green, axiom-clean, wired).

`sieveBound A σ z Y` closes the sieve mean square of any prime weight with `‖a_n‖ ≤ A log n`:

`sieveBound A σ z Y = (4 sinh δ/log Y)·A²·(16/(2σ−2)²)(1 + 2/(2σ−2))
                        + (2/log Y + E + z)·A²·(16/(2σ−1)²)(1 + 2/(2σ−1))`

(`sieveMeanSquare_le_sieveBound`, with `sieveCapLinear`, `sieveCapConst` naming the two caps and both shown
nonnegative).  Substituted for both weights — `A = 1/log 2` outside, `A = 1` inside —

`exists_norm_sum_Icc_mul_log_le_sieveBound` :
`‖∑_{n ≤ N} f(n)‖·log N ≤ (recursion errors) + (H+1)(log⌊N+H⌋)⁴/(log 2)³
    + (1/2π)(1 + 1/(σ−1))e^{7/2}·C·√(25π²·sieveBound (1/log 2) σ z Y)·√(25π²·sieveBound 1 σ z Y)`.

**Nothing in the statement is an unevaluated sum or an assumed estimate.**  Whether it beats the trivial
`N log N` is now a question about the parameters alone, and the shape of that question is visible:

* the linear cap contributes `1/(σ−1)²·(1 + 1/(σ−1))` — at `σ = 1 + 1/log N` this is `(log N)³`;
* the sieve level enters as `1/log Y` in the linear part and as `E + z` in the constant part, with
  `E = Y²e^{4c}(log z)⁴`, so `Y` must stay small against `z` and `z` small against the main term;
* the smoothing width enters as `(H+1)(log(N+H))⁴`, so `H = N/(log N)⁶` is admissible and costs
  `N/(log N)²`;
* `C` is the kernel's decay constant, free in `N`.

That is the optimisation the programme now faces, and it is a question about explicit real functions with no
number theory left in it.

## A loss found in the evaluation: the prime saving was thrown away

Auditing the assembled bound against the trivial bound `N log N` exposes a defect that is not in the chain
but in the *evaluation* of the last step.

`sieveMeanSquare_le_of_norm_le_log` bounds the mean square with **no primality hypothesis** — the docstring
says so proudly — and the caps `sum_Icc_logSq_rpow_neg_le` then run over all integers `n ≤ N`.  But

`∑_{n ≤ N} (log n)²n^{-w} ≍ 2/(w−1)³`   while   `∑_{p ≤ N} (log p)²p^{-w} ≍ 1/(w−1)²`,

so dropping the prime restriction costs a full factor `1/(w−1)`, which at `σ = 1 + 1/log N` is `log N`.  The
prime support of the two weights is exactly the resource the argument lives on, and the current evaluation
discards it at the last step.  With it discarded the analytic term is of size `N(log N)⁴` where the trivial
bound is `N log N`; the chain is therefore correct but not yet a mean value theorem.

**The fix, and the shape of the missing brick.**  Keep the prime restriction and use Chebyshev's `θ` per
dyadic block.  For a prime `p` put `j = ⌊log₂ p⌋`, so `2^j ≤ p < 2^{j+1}`; then

`(log p)²p^{−w} ≤ (log p)·((j+1) log 2)·2^{−jw}`,

and summing over the fibre `{p : ⌊log₂ p⌋ = j}` the factor `∑_{p ∈ fibre} log p ≤ θ(2^{j+1}) ≤ 2^{j+1} log 4`
is where the saving enters — the block holds `≈ 2^j/j` primes, not `2^j` integers.  Summing the blocks,

`∑_{p ≤ N} (log p)²p^{−w} ≤ 2 log 2 log 4 · ∑_{j ≥ 0} (j+1) r^j = 2 log 2 log 4 (1/(1−r) + r/(1−r)²)`,
`r = 2^{1−w} < 1`,

uniformly in `N`.  Every input exists in the corpus: `sum_log_primesLE_le` for `θ`, `Nat.pow_log_le_self` and
`Nat.lt_pow_succ_log_self` for the block, `Finset.sum_fiberwise_of_maps_to` for the grouping, and mathlib's
geometric sums for the tail.  This replaces the integer caps in `sieveMeanSquare_le_sieveBound` and restores
the logarithm.

A second parameter obstruction, visible once the saving is restored: the Selberg count is
`2·(window)/log Y + E + z` with `E = Y²e^{4c}(log z)⁴`, and the additive terms `E + z` are multiplied by the
whole coefficient mass, so they force `z` small (`z ≈ (log N)^{1/2}` and `Y` bounded is admissible).  Because
the count is sharp only when `log Y ≈ log p`, a single sieve level cannot serve the whole prime range: the
prime range must itself be split dyadically, with the level chosen per block.  That is the same dyadic
decomposition as above, so the two obstructions are resolved by one construction.

## The prime saving restored

`RHTower/Sieve/PrimeLogSqZetaCap.lean` (green, axiom-clean, wired, no `sorry`).

`sum_prime_logSq_rpow_neg_le` :

`∑_{p ≤ N} p^{−w}(log p)² ≤ 2 log 2 log 4 · ((1−r)⁻¹ + r/(1−r)²)`,   `r = 2^{1−w} < 1`, uniformly in `N`,

for every `w > 1`.  The proof is the dyadic block bound announced above: `j = ⌊log₂ p⌋` gives
`p^{−w} ≤ 2^{−jw}` and `log p ≤ (j+1)log 2`, the block's remaining factor `∑_{p ∈ block} log p` is bounded by
Chebyshev's `θ(2^{j+1}) ≤ 2^{j+1} log 4` (the corpus's `sum_log_primesLE_le`), and the blocks are summed
against the geometric series (`sum_range_succ_mul_geometric_le`, from mathlib's two geometric sums).

`Finset.sum_fiberwise_of_maps_to` does the grouping, `Nat.pow_log_le_self` and `Nat.lt_pow_succ_log_self`
the block, and `Nat.log_mono_right` the range of block indices.

Against the integer cap this is smaller by `1/(w−1)`, so the factor discarded above is recovered.  As
`w ↓ 1` the bound behaves like `1/(w−1)²` rather than `1/(w−1)³`: at `σ = 1 + 1/log N` and `w = 2σ−1` that is
`(log N)²` in place of `(log N)³`.

**Next:** replace the integer caps inside `sieveMeanSquare_le_sieveBound` by this one.  That needs the
mean-square split restated over the prime-filtered index set — the coefficients are supported on primes, so
`∑_{n ∈ Icc 1 M}` may be replaced by `∑_{p ∈ Icc 1 M with p.Prime}` at no cost, which is the missing
bookkeeping step.

## The master bound with the prime saving kept

`RHTower/Sieve/HalaszPrimeSavingBound.lean` (green, axiom-clean, wired).

* `sieveMeanSquare_eq_filter_prime` — for prime-supported coefficients the majorant only sees the primes, so
  the index set of the split may be cut down to them at no cost.  This is the bookkeeping step that was
  missing; with it the *existing* split (which takes an arbitrary index set) delivers prime-restricted sums,
  so nothing had to be re-proved.
* `sieveBoundPrime A σ z Y = (4 sinh δ/log Y)·A²·cap(2σ−1) + (2/log Y + E + z)·A²·cap(2σ)` with
  `cap(w) = 2 log 2 log 4 ((1−2^{1−w})⁻¹ + 2^{1−w}/(1−2^{1−w})²)` (`sieveCapPrime`).
* `sieveMeanSquare_le_sieveBoundPrime`, and `exists_norm_sum_Icc_mul_log_le_sieveBoundPrime`: the master
  bound verbatim with these caps in place of the integer ones.

Each cap is smaller than its integer counterpart by `1/(w−1)`, so at `σ = 1 + 1/log N` the linear term is
`(log N)²` where it was `(log N)³`.  Tracking the whole analytic term at that `σ`: the Euler factor is
`(1 + log N)e^{7/2}`, the two square roots contribute `25π²·(log N)²/log Y` between them, and the kernel
constant `C` is of size `N`, giving `≈ N(log N)³/log Y` — still a factor `(log N)²/log Y` above the trivial
`N log N`.

**What that isolates.**  The remaining excess is exactly the `1/log Y` of the sieve count against the
`(log N)²` of the linear cap.  The sieve count is sharp only when `log Y ≈ log p`, so the fix is the
per-block sieve level of the second obstruction recorded above: split the prime range dyadically, take
`Y ≈ 2^{j/2}` on the block `2^j ≤ p < 2^{j+1}`, and the linear cap's `(log N)²` is met by a `1/j` from each
block rather than a single global `1/log Y`.  That is the next construction, and it is the last one.

## Minkowski for the weighted mean square: blocks may carry their own parameters

`HTGeometry/WeightedCauchySchwarz.lean` restructured (green, axiom-clean; all statements unchanged, the old
proof now delegates).

* `integral_mul_mul_weight_le_sqrt_mul_sqrt` — the weighted Cauchy–Schwarz inequality in the form of the
  integral of the moduli, `∫ ‖g₁‖‖g₂‖‖W‖ ≤ √(∫‖g₁‖²‖W‖)·√(∫‖g₂‖²‖W‖)`.  This was the Hölder step buried
  inside the old proof; exposing it removes the duplication, and
  `norm_integral_mul_mul_le_sqrt_mul_sqrt` is now four lines on top of it.
* `integrable_normSq_add_mul_weight` — the weighted mean square of a sum is integrable when both parts are.
* `sqrt_integral_normSq_add_mul_weight_le` — **Minkowski's inequality for the weighted mean square**:
  `√(∫‖g₁+g₂‖²‖W‖) ≤ √(∫‖g₁‖²‖W‖) + √(∫‖g₂‖²‖W‖)`, the cross term handled by the exposed
  Cauchy–Schwarz step, so no `L²` space is constructed and no `withDensity` measure is needed.

This is the device the per-block sieve level requires: a Dirichlet polynomial may be split into blocks, each
block's mean square estimated with **its own** sieve level `Y_j ≈ 2^{j/2}`, and the results added.  The excess
factor `(log N)²/log Y` identified above becomes `∑_j (1/j)`-shaped instead of a single global `1/log Y`.

## Minkowski over a finite decomposition

`HTGeometry/WeightedCauchySchwarz.lean` (appended; green, axiom-clean).

* `integrable_normSq_sum_mul_weight` — the weighted mean square of a finite sum is integrable when each
  part's is;
* `sqrt_integral_normSq_sum_mul_weight_le` — `√(∫‖∑_i g_i‖²‖W‖) ≤ ∑_i √(∫‖g_i‖²‖W‖)` over an arbitrary
  `Finset` of indices.

Both by induction on the index set from the two-term case; the index type is arbitrary, so the same statement
serves dyadic blocks, prime-support fibres, or any other decomposition.

With this the per-block estimate is available in the form the argument needs: writing the prime polynomial as
`∑_j` over dyadic blocks, its Lorentzian mean square is at most `(∑_j √(block j))²`, and each block may be
sieved at its own level.  What remains for the block route is the decomposition itself — `L(a, σ+iy)` as the
finite sum of the `L` of the blocks, which is the fibrewise splitting of a finite sum and needs no analysis.

## The block decomposition of a Dirichlet polynomial

`RHTower/Sieve/LSeriesBlockDecomposition.lean` (green, axiom-clean, wired).

* `LSeries_eq_sum_term_of_support` — a finitely supported Dirichlet series is the finite sum of its terms,
  with no condition at `0` (the term there vanishes either way).
* `coeffBlock a κ j = a·1_{κ = j}` with `coeffBlock_support`, `norm_coeffBlock_le`, `coeffBlock_prime`:
  restriction only kills coefficients, so support, size bounds and primality are all inherited.
* `LSeries_eq_sum_blocks` — for any index map whose image on the support lies in a finite `u`,
  `L(a, t) = ∑_{j ∈ u} L(a·1_{κ = j}, t)`.
* `LSeries_eq_sum_dyadic_blocks` — the instance `κ = ⌊log₂ ·⌋`, `u = range(⌊log₂ M⌋+1)`: the blocks are the
  ranges `2^j ≤ n < 2^{j+1}`.

The name `coeffBlock` was chosen after finding a matrix-valued `blockRestrict` already in
`HTGeometry/ProjectiveHorizonJetDeterminant.lean`: different namespace, so no build error, but a module
opening both would have been ambiguous.

**Both halves of the per-block route are now in place**: the decomposition here and Minkowski for the
weighted mean square, so `√(mean square of L(a))≤ ∑_j √(mean square of L(a_j))` with each block free to
choose its own sieve level.  What remains is to choose those levels — on the block `2^j ≤ p < 2^{j+1}` the
Selberg count is sharp at `log Y ≈ j log 2`, i.e. `Y ≈ 2^{j/2}` with `z ≈ 2^j` — and to sum the resulting
`(j+1)`-indexed series, which is the geometric-type sum the dyadic cap already handles.

## The mean square block by block, with a free level per block

`RHTower/Sieve/BlockMeanSquare.lean` (green, axiom-clean, wired).

* `sqrt_integral_lorentz_normSq_LSeries_le_sum_blocks` :
  `√(∫‖L(a,σ+iy)‖²dy/(1+y²)) ≤ ∑_j √(∫‖L(a_j,σ+iy)‖²dy/(1+y²))`, `a_j` carried by `2^j ≤ n < 2^{j+1}`.
* `sqrt_integral_lorentz_normSq_LSeries_le_sum_prime_sieve` — the same with each block's mean square
  discharged by the Selberg sieve **at its own level**:

  `√(∫‖L(a,σ+iy)‖²dy/(1+y²)) ≤ ∑_j √(25π²·sieveMeanSquare a_j (Icc 1 M) σ (z_j) (Y_j))`,

  the levels being arbitrary functions of the block index, with only admissibility assumed of each.

This is the last structural device the route needed.  The Selberg count's main term `2(window)/log Y` is sharp
only when `log Y` matches the logarithm of the primes in play; on the block that logarithm is `j log 2`, so
the level may now be chosen as `Y_j ≈ 2^{j/2}`, `z_j ≈ 2^j`, and the additive errors `E_j + z_j` — which
previously forced one global compromise — are charged per block against a block whose coefficient mass is
itself geometrically small.

**All devices are now in the corpus.**  What is left is arithmetic: substituting a concrete level sequence and
summing the `j`-indexed series, in the same style as the dyadic Chebyshev cap.

## The three quantities of a dyadic block

`RHTower/Sieve/DyadicBlockQuantities.lean` (green, axiom-clean, wired).

* `norm_coeffBlock_le_block_bound` — a logarithmic coefficient bound becomes the **constant** `A(j+1)log 2`
  on the block, so a block's coefficients are bounded rather than log-weighted;
* `rpow_neg_le_block_rpow` — `n^{−c} ≤ 2^{−cj}` on the block, the damping at the left endpoint;
* `card_prime_block_le` — the block holds at most `2^{j+1}log 4/(j log 2)` primes, Chebyshev's `θ` divided by
  the least logarithm of the block.  This is the block's length over its logarithm: the saving the sieve is
  supposed to produce, here for free from `sum_log_primesLE_le`.

Together they turn a block's sieve mean square into a product of powers of `2^j` and polynomials in `j`,
which is what makes the block sum a geometric-type series — the same shape the dyadic Chebyshev cap already
sums.

## A block's sieve mean square, in closed form

`RHTower/Sieve/BlockSieveMeanSquare.lean` (green, axiom-clean, wired).

`sieveMeanSquare_coeffBlock_le` — the three block quantities substituted into the majorant:

`sieveMeanSquare a_j (Icc 1 M) σ z Y
    ≤ (2^{j+1}log 4/(j log 2))·(2(2^{j+1}·2 sinh δ + 1)/log Y + E + z)·(A(j+1)log 2)²·2^{−2σj}`

— the number of primes of the block, the largest value of the Selberg count on it, the block's uniform
coefficient bound squared, and the damping at its left endpoint.  The sum over the block is reduced to its
primes first (the coefficients vanish elsewhere), then bounded termwise and counted.

Every factor is a power of `2^j` or a polynomial in `j`, so with a level sequence `(z_j, Y_j)` fixed the block
sum is a geometric-type series in `j`.  The level remains free in the statement: nothing constrains `Y` beyond
admissibility.

**The route is now device-complete and reduced to one choice.**  Writing `L = log 2` and `δ = 1/2π`, the block
sum to be bounded is

`∑_{j ≤ log₂M} √( 25π²·(2^{j+1}·log 4/(jL))·(2(2^{j+1}·2 sinh δ + 1)/log Y_j + E_j + z_j)·(A(j+1)L)²·2^{−2σj} )`,

and the question is which `(z_j, Y_j)` makes it small.  The factor `2^{j}·2^{−2σj} = 2^{-j(2σ-1)}` decays, the
count contributes `2^{j}/j`, and `E_j = Y_j²e^{4c}(log z_j)⁴` must stay below the main term — which caps
`Y_j` at about `2^{j/2}/(j log z_j)²`.  With `log Y_j ≍ j` the linear part of each block is
`≍ 2^{2j}(j+1)²/(j²·j)·2^{−2σj}`, whose square root is `≍ 2^{j(1−σ)}·j^{-1/2}`, and the geometric sum over
`j ≤ log₂ N` is dominated by its last block: `≍ N^{1−σ}/√(log N)`.  At `σ = 1 + 1/log N` that is
`≍ 1/√(log N)`, which against the Euler factor `log N` and the kernel constant `N` gives
`N(log N)^{1/2}` — below the trivial `N log N` by `√(log N)`.  Establishing that in Lean is the arithmetic
that remains; the estimate above is the target, not a theorem.

## The sieve level chosen per block

`RHTower/Sieve/BlockSieveLevels.lean` (green, axiom-clean, wired).

`blockSieveLevel j = max 2 (2^{⌊j/4⌋})`, `blockSieveModulus j = 2^{j+1}` — the level is a quarter of the
block's logarithm, floored at `2`; the modulus is the block's right endpoint.  The quarter is what keeps the
Selberg fibre error `E = Y²e^{4c}(log z)⁴` below the block's main term `2^{j+1}·2 sinh δ/log Y`, and the floor
keeps `log Y > 0` on every block, including the first, where `⌊j/4⌋ = 0` would give `Y = 1`.  Admissibility on
every block: `1 ≤ Y_j`, `2 ≤ Y_j`, `2 ≤ z_j`, `Y_j ≤ z_j`, `0 < log Y_j`, all four proved for all `j`, which is
why the modulus is `2^{j+1}` and not `2^j` (at `j = 0` the latter is `1 < 2 = Y_0`).

* `sqrt_integral_lorentz_normSq_LSeries_le_block_sum` — the mean square at these levels;
* `sqrt_integral_lorentz_normSq_LSeries_le_block_sum_explicit` — with every block past the first replaced by
  the closed-form estimate, so the right-hand side is a function of `j`, `σ` and `A` alone.

**The parameters are now fixed and the remaining work is a single summation**: bounding

`∑_{1 ≤ j ≤ log₂M} √( 25π²·(2^{j+1}log4/(j log2))·(2(2^{j+1}·2 sinh δ+1)/log Y_j + E_j + 2^{j+1})·(A(j+1)log2)²·2^{−2σj} )`

by a closed expression in `σ` and `M`.  Each summand is `√` of a product of powers of `2^j` and polynomials in
`j`; the `j`-dependence of `log Y_j = ⌊j/4⌋ log 2` is the only non-elementary piece, and it is bounded below by
`(j−3)log 2/4`, which is enough.

## Correction to the level choice: the modulus enters additively

Estimating the block summand at the levels of the previous entry exposed an error in that choice.  The Selberg
count is `2(window)/log Y + E + z`, and the modulus `z` enters **additively**: with `z_j = 2^{j+1}`, the
block's right endpoint, the count is at least `2^{j+1}`, which is worse than counting *every integer* of the
block.  The choice was self-defeating — it satisfied admissibility (`Y_j ≤ z_j` for all `j`, which is what
pushed it up to the endpoint) at the cost of the entire saving.

The scales are now

`blockSieveLevel j = max 2 (2^{⌊j/8⌋})`,   `blockSieveModulus j = max 2 (2^{⌊j/2⌋})`,

so `z_j ≈ 2^{j/2}`, far below the block's length `2^j`, and `Y_j ≈ 2^{j/8} ≤ z_j` keeps admissibility on every
block.  All four conditions still hold for all `j` and the block-sum theorems are unchanged.

Sizes for the summation (`RHTower/Sieve/BlockSieveLevels.lean`, appended):

* `log_blockSieveLevel_ge` — `log Y_j ≥ ((j−7)/8)·log 2`, so the count's main term is `O(2^j/j)`;
* `blockSieveLevel_le_two_mul` — `Y_j ≤ 2·2^{⌊j/8⌋}`, so `E_j = Y_j²e^{4c}(log z_j)⁴ = O(2^{j/4}j⁴)`;
* `blockSieveModulus_le_two_mul` — `z_j ≤ 2·2^{⌊j/2⌋}`.

Against the block's main term `≈ 2^j/j` both `E_j` and `z_j` are now negligible, which is what the choice has
to achieve.  The summand's dominant factor is therefore `2^j/j·(j+1)²·2^{−2σj}`, whose square root is
`2^{j(1/2−σ)}(j+1)/√j`; summing over `j ≤ log₂M` is again a geometric-type series.

## Accounting the block sum: a deficit of two logarithms, and where they must come from

With the corrected levels the block summand can be tracked exactly.  Two identities help: `log 4 = 2 log 2`
makes the count factor `2^{j+1}·log 4/(j log 2) = 2^{j+2}/j` exactly, and `log Y_j ≥ ((j+1)/16)log 2` (a single
bound valid for every `j`, from `log Y_j ≥ log 2` for `j ≤ 15` and `log Y_j ≥ ((j−7)/8)log 2` beyond).  Then

* the count's main term is `2·2^{j+1}S/log Y_j ≤ 64S·2^j/((j+1) log 2)`;
* `E_j = O(2^{j/4}(j+1)⁴)` and `z_j = O(2^{j/2})`, both subordinate;
* so the block bound is `≍ A²·((j+1)/j)·2^{2j(1−σ)}`, and its square root `≍ A·2^{j(1−σ)}`;
* summing, `∑_{j ≤ log₂M} 2^{j(1−σ)} ≤ 1/(1−2^{1−σ})`, which at `σ = 1 + 1/log M` is `≍ log M/log 2`.

So each block sum is `≍ A log M`, the product of the two is `≍ (log M)²`, and with the Euler factor `log M`
and the kernel constant `C ≍ N` the analytic term is `≍ N(log M)³` against a main term `N log N`.  **The
deficit is two logarithms.**  Both have identified sources:

1. **The outer weight's own damping is being discarded.**  `ghsOuter f N p = f(p)log p/log⌊N/p⌋`, and
   `norm_ghsOuter_le` bounds `1/log⌊N/p⌋ ≤ 1/log 2` — a constant.  On the block `2^j ≤ p < 2^{j+1}` the true
   factor is `1/log⌊N/2^{j+1}⌋ ≍ 1/((log₂N − j) log 2)`, so keeping it block-refined weights the `j`-th block
   by `1/(log₂N − j)`.  Summed against `2^{j(1−σ)}`, whose mass sits at `j ≍ log₂N`, this is worth a
   logarithm.  The missing brick is `norm_ghsOuter_le_block`.
2. **The kernel constant's dependence on the smoothing width is not exposed.**
   `exists_bound_mellin_smoothWeight_line` produces *some* `C` with `‖W(σ+iy)‖ ≤ C/(1+y²)`, and the assembly
   treats it as a black box; the accounting above uses only `C ≍ N^σ ≍ N`.  A cutoff of width `H` has a
   transform decaying from height `1/H`, so the honest constant should carry a factor `H/N` against the
   trivial `N^σ`, and `H = N/(log N)⁶` would then give back several logarithms.  Whether the corpus's `C` can
   be sharpened this way is the question to settle next; if it cannot, the route caps at `N(log N)³` and the
   smoothing must be replaced by a sharper kernel.

Neither is an obstruction of principle, and both are local to one lemma.  Recording them here so the next step
attacks the right lemma rather than re-deriving the accounting.

## The kernel constant read off, and a structural cap on the global-line route

Reading `exists_bound_mellin_smoothWeight` (`HTGeometry/SmoothWeightMellin.lean:542`) settles item 2 of the
previous entry, and the answer is worse than assumed.  The constant produced there is

`C = M·|N + H + 1 − N/2|`,   `M = C_j/H^{j+1}·(N+H+1)^{σmax+j}`,

so for the quadratic decay `j = 1` used by the Lorentzian route, `C ≍ N^{σ+2}/H² = N^σ·(N/H)²`.  The
`(N/H)²` is a *penalty*, not the hoped-for gain: the transform's quadratic decay is bought by two derivatives
of the cutoff, each costing `1/H`.

That caps the global-line route.  The smoothing error is `≍ H(log N)⁴`, forcing `H ≪ N/(log N)³`, at which
point `C ≍ N(log N)⁶`, and with the Euler factor `log N` and the two block sums `(log M)²` the analytic term
is `≍ N(log N)⁹`.  Increasing `H` to shrink `C` increases the smoothing error linearly, and the two cannot be
balanced below `N log N`: **the Lorentzian mean-square route, applied to the whole line, cannot beat the
trivial bound.**  This is a structural cap of the device combination, not a bookkeeping loss.

**The corpus's own Halász assembly already avoids it.**  `HalaszPerronAssembly.norm_tsum_mul_smoothWeight_le`
splits the vertical integral at height `T`: on `[−T, T]` it uses the *uniform* kernel bound
`‖W‖ ≤ (N+H)^σ/σ ≍ N` — no `(N/H)²` — and beyond `T` it uses the decay, where the large constant is harmless
because the tail integral is small.  The mean-square treatment must be applied the same way: Cauchy–Schwarz on
`[−T, T]` against the uniform bound, with the tail bounded by the kernel's decay.  The corpus has the
truncated mean square for exactly this (`integral_Icc_normSq_logPoly_le_prime_sieve`, over `Icc (−W) W`), and
`integral_compl_Icc_inv_one_add_sq_le` for the tail.

**Next brick, and a subsumption.**  The three-factor master inequality and the weighted Cauchy–Schwarz family
are stated for `volume` on the line.  The truncated route needs them on `volume.restrict (Icc (−T) T)`, and
the proofs use nothing but Hölder for the measure at hand: restating the family for an arbitrary measure `μ`
subsumes both the global and the truncated case, with the present statements recovered by `μ = volume`.  That
is the next step, followed by the truncated assembly.

## Weighted Cauchy–Schwarz over an arbitrary measure

`HTGeometry/WeightedHolder.lean` (new, green, axiom-clean, wired); `WeightedCauchySchwarz.lean` now delegates.

`integral_mul_mul_weight_le_sqrt_mul_sqrt_measure` and `norm_integral_mul_mul_le_sqrt_mul_sqrt_measure` state
the weighted Cauchy–Schwarz inequality for an arbitrary measure on an arbitrary measurable space:

`∫ ‖g₁‖‖g₂‖‖W‖ ∂μ ≤ (∫ ‖g₁‖²‖W‖ ∂μ)^{1/2}(∫ ‖g₂‖²‖W‖ ∂μ)^{1/2}`.

Nothing about the line or about Lebesgue measure was used in the old proof — only Hölder with conjugate
exponents `2, 2` — so the generalisation is the same proof with `volume` replaced by `μ`, and the version on
the line is now a one-line corollary (`integral_mul_mul_weight_le_sqrt_mul_sqrt` delegates; every downstream
user is untouched and `BlockMeanSquare` rebuilds).

The instance that matters next is `μ = volume.restrict (Icc (−T) T)`: on a bounded height range the smoothed
Perron kernel obeys the uniform bound `‖W‖ ≤ (N+H)^σ/σ ≍ N`, with none of the `(N/H)²` its global
quadratic-decay bound carries.  That is the route the corpus's own Halász assembly takes, and the truncated
mean square (`integral_Icc_normSq_logPoly_le_prime_sieve`) and tail estimate
(`integral_compl_Icc_inv_one_add_sq_le`) are already in place for it.

## The three-factor inequality with a uniformly bounded weight

`HTGeometry/WeightedHolder.lean` (appended; green, axiom-clean).

* `integral_mul_le_sqrt_mul_sqrt_measure` — Cauchy–Schwarz without a weight, the weighted inequality at
  `W ≡ 1`;
* `integrable_mul_norm_of_integrable_sq` — the product of two moduli is integrable when both mean squares are;
* `norm_integral_mul_three_le_sup_mul_sqrt_measure` :

  `‖∫ g₁g₂g₃W ∂μ‖ ≤ M·Wsup·(∫‖g₁‖² ∂μ)^{1/2}(∫‖g₂‖² ∂μ)^{1/2}`   for `‖g₃‖ ≤ M`, `‖W‖ ≤ Wsup`.

All three for an arbitrary measure.  The nonnegativity of `M` and `Wsup` is taken as data rather than derived
from the pointwise bounds, since on an empty domain the bounds are vacuous while the conclusion still needs
them — a reminder that "a bound on a norm is nonnegative" is only available where there is a point to evaluate
at.

Instantiated at `μ = volume.restrict (Icc (−T) T)` and `Wsup = (N+H)^σ/σ` this is the truncated analogue of the
master inequality, with none of the `(N/H)²` that the global quadratic-decay bound carries.  What the truncated
route still needs is the tail: `‖∫_{|y| > T} g₁g₂g₃W‖`, where the trivial bound `‖g₁g₂g₃‖ ≤ (Euler)³` meets the
kernel's decay through `integral_compl_Icc_inv_one_add_sq_le` — the same split the corpus's own Halász assembly
performs.
