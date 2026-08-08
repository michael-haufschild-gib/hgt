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

## The truncated master inequality

`RHTower/Sieve/TruncatedVerticalSplit.lean` (green, axiom-clean, wired).

* `norm_integral_compl_Icc_le` — beyond height `T` the integrand is bounded by its trivial size times the
  kernel's decay, whose integral is `π − 2 arctan T` (the corpus's `integral_compl_Icc_inv_one_add_sq_le`);
* `norm_integral_le_truncated_add_tail` — the split of the vertical integral at height `T`;
* `norm_integral_mul_three_le_truncated_add_tail` :

  `‖∫_ℝ g₁g₂g₃W‖ ≤ M·Wsup·(∫_{|y|≤T}‖g₁‖²)^{1/2}(∫_{|y|≤T}‖g₂‖²)^{1/2} + Mg·C·(π − 2 arctan T)`.

The point of the shape: the truncated part sees only `Wsup`, the *uniform* size of the kernel on a bounded
height range — for a smoothed cutoff `(N+H)^σ/σ ≍ N`, with no `(N/H)²` — while the quadratic-decay constant
`C ≍ N^σ(N/H)²`, which capped the global route, is confined to the tail and multiplied by `π − 2 arctan T`.
Choosing `T` large enough that `C(π − 2 arctan T) ≍ C/T` is small costs only `log T` in the truncated mean
square, so a polynomial `T` in `N` suffices.

**The truncated route now has all its devices**: this inequality, the truncated prime-supported mean square
(`integral_Icc_normSq_logPoly_le_prime_sieve`, over `Icc (−W) W`), the Perron identity, and the recursion half
of the argument, which is independent of the kernel treatment.  The remaining step is to assemble them as
`GhsStepFour` assembles the global versions, and then to redo the parameter accounting with `Wsup ≍ N` in place
of `C ≍ N(log N)⁶` — where the previous cap came from.

## The truncated mean square in the two frequency variables

`RHTower/Sieve/TruncatedMeanSquareChange.lean` (green, axiom-clean, wired).

`integral_Icc_normSq_LSeries_eq` :

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖² dy = 2π ∫_{|w| ≤ T/2π} ‖logPoly (a_n n^{−σ}) s w‖² dw`

for finitely supported `a` — an exact identity, not an inequality.  The Perron passage delivers its integral in
`y` (frequency `n^{−iy}`), the corpus's truncated mean value theorem is stated in `w` (frequency `n^{2πiw}`),
and on a symmetric interval the substitution `y = −2πw` carries one to the other: the reflection is absorbed by
the symmetry and the scaling costs the Jacobian `2π`.

Mechanically this is `integral_Icc_eq_integral_Ioc` to reach an interval integral, then
`intervalIntegral.integral_comp_div` and `integral_comp_neg`, with `neg_div` to align `−y/2π` with `−(y/2π)`
before the substitution — the two differ syntactically and the rewrite fails without it.

With this the truncated route can consume `integral_Icc_normSq_logPoly_le_prime_sieve` directly: that theorem's
window parameter `W` is `T/2π`, and its hypothesis `2πδW ≤ 1` fixes the neighbour scale `δ = 1/(2πW) = 1/T`,
so a large truncation height gives a *narrow* multiplicative window — where the Selberg sieve's short-interval
count is strongest.  That is the opposite regime from the Lorentzian route, whose `δ = 1/2π` was fixed, and it
is the next thing to exploit.

## The truncated mean square of a prime-supported series, on the Perron line

`RHTower/Sieve/TruncatedPrimeSieveMeanSquare.lean` (green, axiom-clean, wired).

`integral_Icc_normSq_LSeries_le_prime_sieve` :

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖² dy ≤ 2π·(5T/4)·∑_n (2(n(e^{1/T} − e^{−1/T}) + 1)/log Y + E + z)·‖a_n n^{−σ}‖²`

for prime-supported finitely supported `a`.  Built by the change of variables, then `logPoly_eq_logPoly_filter`
to cut the index set down to the nonzero coefficients — whose elements are prime, which is what the window
theorem demands (it needs *every* index prime, not merely the support) — then the sum enlarged back to `s`
because the terms are nonnegative.

**Two features of this bound decide the route.**  The scale is sharp: the window theorem's hypothesis
`2πδW ≤ 1` at `W = T/2π` is an equality when `δ = 1/T`, so truncation height and window width are reciprocal.
And the factor `5T/4` in front is cancelled by `e^{1/T} − e^{−1/T} ≍ 2/T` inside, so

* the leading term is `≍ ∑_n n‖a_n n^{−σ}‖²/log Y`, **independent of `T`**;
* only the additive part `(5T/4)(E + z)·∑‖a_n n^{−σ}‖²` grows with `T`.

So `T` is free up to `T(E+z)` staying below the leading term — and the truncated master inequality's tail costs
`Mg·C/T`, which wants `T` large.  The two constraints pull in opposite directions but with room between them:
`C ≍ N^σ(N/H)²` and `E + z ≍ Y²(log z)⁴ + z` are polynomially separated once `H` is a fixed power of `N` and the
sieve level is a small power.  That is the balance the final accounting has to strike, and unlike the global
route there is now a window in which both constraints hold.

## The trivial size of a finitely supported series

`RHTower/Sieve/LSeriesTrivialSize.lean` (green, axiom-clean, wired).

* `norm_LSeries_le_sum_of_support` — `‖L(a,σ+iy)‖ ≤ ∑_{n ∈ s} ‖a_n‖n^{−σ}`, uniformly in `y`: every phase has
  modulus one, so the polar split of `natCast_cpow_neg_eq` plus `Complex.norm_exp_ofReal_mul_I` reduces the
  bound to the `ℓ¹` mass of the damped coefficients;
* `norm_LSeries_mul_three_le` — the product of three series, two finitely supported and one merely bounded, is
  at most the product of the two `ℓ¹` masses and the bound.

This is the constant `Mg` that the tail of the truncated master inequality consumes.  No mean square appears
there: the tail is charged to the trivial size of the integrand against the kernel's decay, which is why a
crude `ℓ¹` bound suffices for it while the truncated part carries the sieve.

With this, all the inputs of the truncated assembly are in the corpus: the Perron identity, the truncated master
inequality, the uniform kernel bound (`norm_perronKernel_le`), the decay constant
(`exists_bound_mellin_smoothWeight_line`), the Euler bound, this `ℓ¹` bound, and the truncated prime-sieve mean
square.  Assembling them is the next step, and then the accounting with `Wsup ≍ N` — the quantity that replaces
the `C ≍ N(log N)⁶` which capped the global route.

## Step 4 assembled on a truncated height range

`RHTower/Sieve/GhsStepFourTruncated.lean` (green, axiom-clean, wired).

`exists_norm_tsum_ghs_smoothWeight_le_truncated` :

`2π‖∑ₙ (a ⍟ (b ⍟ f))(n)w(n)‖
    ≤ E·((N+H)^σ/σ)·√(truncSieveSum a)·√(truncSieveSum b) + (ℓ¹a)(ℓ¹b)·E·C·(π − 2 arctan T)`,

for every bounded multiplicative `f`, every `N₀`, cutoff `N, H > 0`, `σ > 1`, height `T > 0` and admissible
sieve level, with `E = (1 + 1/(σ−1))e^{7/2}` and `dampedL1`, `truncSieveSum` naming the two auxiliary
quantities.

**The whole point is which constant multiplies the mean squares.**  Here it is `(N+H)^σ/σ`, the uniform size of
the kernel — of order `N` — while the global assembly multiplies them by `C ≍ N^σ(N/H)²`, and no `H` reconciles
that with the smoothing error `H(log N)⁴`.  In this form `C` appears only against `π − 2 arctan T ≍ 1/T`.

Everything is now in place for the accounting that the global route failed:

* `Wsup ≍ N` (was `C ≍ N(log N)⁶`);
* the truncated sieve sum's leading term is `T`-free, so its size is the same
  `≍ ∑_p p(log p)²p^{−2σ}/log Y` as before;
* the tail is `(ℓ¹a)(ℓ¹b)·E·C/T`, and `ℓ¹` masses of the two prime weights are `O((log N)²)` at `σ` near `1`,
  so `T` polynomial in `N` kills it;
* the smoothing error stays `H(log N)⁴` with `H` free up to `N`.

With `Wsup ≍ N` in place of `N(log N)⁶` the earlier deficit of `(log N)⁸` becomes `(log N)²`, and the two
remaining logarithms are the ones already identified: the outer weight's discarded `1/log⌊N/p⌋` damping, and the
per-block sieve levels.  Both devices exist; the next step is to combine them in this truncated form.

## The outer weight's own damping, kept block by block

`RHTower/Sieve/GhsOuterBlockDamping.lean` (green, axiom-clean, wired).  This closes the first of the two
logarithms identified in the accounting.

* `norm_ghsOuter_le_block` — on the block `2^j ≤ p < 2^{j+1}`,
  `‖a_p‖ ≤ (j+1)log 2/log⌊N/2^{j+1}⌋`.  The numerator is the block's upper endpoint, the denominator the
  complementary scale at that endpoint, and `Nat.div_le_div_left` supplies the monotonicity in between.
* `log_div_block_ge` — `log⌊N/2^{j+1}⌋ ≥ (⌊log₂N⌋ − j − 1)·log 2`, from `⌊N/2^{j+1}⌋ ≥ 2^{⌊log₂N⌋−j−1}`.

So the `j`-th block's coefficient constant is `≍ (j+1)/(log₂N − j)`: small for the early blocks, large only for
the last few — where the block is short and the sieve count small.  A global bound can only say `1/log 2`, and
the difference summed against `2^{j(1−σ)}`, whose mass sits at `j ≍ log₂N`, is a logarithm.

Both remaining devices are now present: this and the per-block sieve levels.  What is left is to state the
truncated block sum with the block-dependent coefficient constant — `sieveMeanSquare_coeffBlock_le` currently
takes a single `A` — and then the accounting.

## The block estimate with a block-dependent coefficient constant

`RHTower/Sieve/BlockSieveMeanSquare.lean` generalised (green, axiom-clean; the previous statement survives as a
corollary).

`sieveMeanSquare_coeffBlock_le_of_bound` takes any uniform bound `Bc` on the block's coefficients:

`sieveMeanSquare a_j (Icc 1 M) σ z Y ≤ (primes of the block)·(count max)·(Bc²·2^{−2σj})`,

and `sieveMeanSquare_coeffBlock_le` is the case `Bc = A(j+1)log 2` of a logarithmic bound.  The nonnegativity of
`Bc` turned out to be unnecessary — the square supplies it — so the generalisation has one hypothesis fewer than
the special case it replaces.

This is what lets the two remaining devices meet.  For the outer weight, `Bc` is now the block-damped constant
`(j+1)log 2/log⌊N/2^{j+1}⌋` of the previous entry rather than the constant `(1/log 2)(j+1)log 2`, and the
`(log₂N − j)` in its denominator is the logarithm the accounting was missing.  For the inner weight, `Bc` is the
logarithmic case unchanged.

## The outer weight's block estimate, with its damping

`RHTower/Sieve/GhsOuterBlockEstimate.lean` (green, axiom-clean, wired).

* `norm_coeffBlock_ghsOuter_le` — the outer weight's block is bounded by `(j+1)log 2/log⌊N/2^{j+1}⌋`
  (zero off the block, the block bound on it);
* `sieveMeanSquare_coeffBlock_ghsOuter_le` — the block estimate with that constant, a one-line instance of
  the generalised block lemma.

Since `log⌊N/2^{j+1}⌋ ≥ (⌊log₂N⌋ − j − 1)log 2`, the `j`-th block's constant is `≍ (j+1)/(log₂N − j)`.  The
geometric weight `2^{−2σj}` puts the block sum's mass at `j ≍ log₂N`, which is exactly where this damping is
strongest — the factor a constant bound discards.

**Both logarithms of the accounting are now carried by theorems.**  The route's inventory is complete:

| device | theorem |
|---|---|
| paper half, `O(N log log N)` | `norm_sum_Icc_mul_log_sub_ghsTriple_le` |
| sharp ← smoothed | `norm_partialSum_le_of_smoothed_bound` |
| Perron identity | `tsum_mul_smoothWeight_ghs_eq_integral` |
| truncated step 4, `Wsup ≍ N` | `exists_norm_tsum_ghs_smoothWeight_le_truncated` |
| truncated mean square | `integral_Icc_normSq_LSeries_le_prime_sieve` |
| block decomposition + Minkowski | `sqrt_integral_lorentz_normSq_LSeries_le_sum_blocks`, `sqrt_integral_normSq_sum_mul_weight_le` |
| per-block levels | `blockSieveLevel`, `blockSieveModulus` |
| block estimate, block-dependent constant | `sieveMeanSquare_coeffBlock_le_of_bound` |
| outer damping per block | this module |

What remains is arithmetic only: the truncated analogue of the block decomposition (Minkowski over
`volume.restrict (Icc (−T) T)` rather than the Lorentzian weight — the finite-sum Minkowski is already stated for
an arbitrary weight, so this is an instantiation), and then summing the `j`-indexed series with the two dampings
in place.

## Minkowski over an arbitrary measure, unweighted

`HTGeometry/WeightedHolder.lean` (appended; green, axiom-clean).

* `integrable_normSq_add_measure`, `sqrt_integral_normSq_add_le_measure` — the two-term case;
* `integrable_normSq_sum_measure`, `sqrt_integral_normSq_sum_le_measure` —
  `(∫‖∑_i g_i‖² ∂μ)^{1/2} ≤ ∑_i (∫‖g_i‖² ∂μ)^{1/2}` over an arbitrary `Finset` and an arbitrary measure.

These are the unweighted (`W ≡ 1`) versions of the weighted family, proved from the general-measure
Cauchy–Schwarz rather than from the weighted Minkowski: for the truncated route the weight is the *measure*
(`volume.restrict (Icc (−T) T)`), not a function, so the unweighted statement over a general measure is the
right shape and is simpler than the weighted one over `volume`.

With them the truncated block decomposition is an instantiation: `μ = volume.restrict (Icc (−T) T)` and
`g_j = L(a_j, σ+i·)` give

`(∫_{|y| ≤ T} ‖L(a,σ+iy)‖²)^{1/2} ≤ ∑_j (∫_{|y| ≤ T} ‖L(a_j,σ+iy)‖²)^{1/2}`,

each block then carrying its own sieve level and, for the outer weight, its own damping.

## The truncated mean square, block by block

`RHTower/Sieve/TruncatedBlockMeanSquare.lean` (green, axiom-clean, wired).

* `sqrt_integral_Icc_normSq_LSeries_le_sum_blocks` —
  `(∫_{|y| ≤ T}‖L(a,σ+iy)‖²)^{1/2} ≤ ∑_j (∫_{|y| ≤ T}‖L(a_j,σ+iy)‖²)^{1/2}`, Minkowski over the restricted
  measure;
* `sqrt_integral_Icc_normSq_LSeries_le_sum_block_sieve` — each block discharged by the Selberg sieve at a level
  free to depend on the block:
  `≤ ∑_j √(truncSieveSum a_j (Icc 1 M) σ T (z_j) (Y_j))`.

This is the truncated counterpart of the Lorentzian block sum, and with it **the truncated route has every
device the global one had, plus the two savings the global one could not use**:

* the mean squares are multiplied by `Wsup ≍ N`, not by `C ≍ N^σ(N/H)²`;
* the sieve level is chosen per block, where the count is sharp;
* the outer weight keeps its own damping per block.

Nothing in the chain assumes an estimate, and every statement above is proved.  What remains is the arithmetic
of choosing `σ, T, H` and the level sequence, and summing the `j`-indexed series — the step whose two previous
attempts (the global Lorentzian accounting, and the modulus at the block endpoint) both failed for reasons now
recorded and repaired.

## The accounting again, and a structural correction: the mean square complements the distance, it does not replace it

Doing the truncated accounting honestly settles what the mean-square route can and cannot do on its own.

With the chosen levels and both dampings, per block `j`:

* the count's main term contributes `(5T/4)·2·2^{j+1}S_T/log Y_j` with `S_T = e^{1/T} − e^{−1/T} ≤ 3/T`, so the
  `T` cancels and the term is `≍ 2^{j}/(j log 2)`;
* `E_j = O(2^{j/4}j⁴)` and `z_j = O(2^{j/2})` are subordinate;
* with `#primes ≍ 2^{j+2}/j` and the damping `2^{−2σj}`, the block's sum is `≍ Bc_j²·2^{2j(1−σ)}/j²`, whose
  square root is `≍ Bc_j·2^{j(1−σ)}/j`.

At `σ = 1 + 1/log N` the factor `2^{j(1−σ)} = e^{−j log 2/log N}` lies in `[e^{−1}, 1]` across the whole range
`j ≤ log₂N` — it does not decay.  So

* outer block sum, with `Bc_j ≍ (j+1)/(log₂N − j)`: `≍ ∑_j 1/(log₂N − j) ≍ log log N`;
* inner block sum, with `Bc_j ≍ (j+1)log 2`: `≍ ∑_j 1 ≍ log N`.

Their product is `≍ log N·log log N`, and with the Euler factor `≍ log N` and `Wsup ≍ N` the analytic term is
`≍ N(log N)²log log N`.  Since the paper half equates the smoothed sum with `S(N)·log N`, this gives
`S(N) ≲ N log N log log N` — weaker than the trivial `S(N) ≤ N`.

**The diagnosis is structural, not arithmetic.**  The Euler factor enters as `‖L(f,σ+iy)‖ ≤ (1+1/(σ−1))e^{7/2}`,
the *maximum* size of the series, applied at every height.  That is the trivial bound, and no mean-square
estimate of the other two factors can recover a saving from it: in Granville–Harper–Soundararajan the mean
square is what controls the contribution *away from the exceptional frequency*, while the exceptional frequency
is where the distance bound does the work.  Lemma 1 complements the dichotomy; it does not replace it.

The corpus's own `HalaszPerronAssembly.norm_tsum_mul_smoothWeight_le` already has the right architecture: the
damped bound `exp(7/2 + 2(σ−1)(log z + log 4) − δ²)` off one window (`norm_tsum_twistedSummand_le_of_far`), the
trivial bound on the window, and `volume_halaszLargeValues_le` for the window's measure.  What my assembly
should do is the same split with Cauchy–Schwarz on the *complement*:

* off the window: three-factor inequality with `M` the **damped** Euler bound — the `e^{−δ²}` is the saving;
* on the window: Cauchy–Schwarz over a set of measure `O(δ/log z)`, where the truncated mean square is
  correspondingly small.

Both pieces are instances of `norm_integral_mul_three_le_sup_mul_sqrt_measure` at `μ = volume.restrict S`, since
that lemma is stated for an arbitrary measure and takes the bound on `g₃` as a hypothesis.  So the next brick is
not a new device but a second instantiation of one already built, together with the corpus's large-value window
measure.  **Recorded so the next attempt starts from the dichotomy rather than from the trivial bound.**

## The three-factor inequality split across a set: the dichotomy's architecture

`HTGeometry/WeightedHolder.lean` (green, axiom-clean; the three-factor lemma's hypotheses weakened, one new
theorem).

Two changes, the first enabling the second:

* the bounds on `g₃` and `W` in `norm_integral_mul_three_le_sup_mul_sqrt_measure` are now **a.e.** rather than
  pointwise.  This is what lets the lemma be applied on a restricted measure, where only a bound *on the set* is
  available; the pointwise callers pass `Filter.Eventually.of_forall`.
* `norm_integral_mul_three_le_split` :

  `‖∫ g₁g₂g₃W ∂μ‖ ≤ M₁·Wsup·√(∫_S‖g₁‖²)√(∫_S‖g₂‖²) + M₂·Wsup·√(∫_{Sᶜ}‖g₁‖²)√(∫_{Sᶜ}‖g₂‖²)`,

  the bounded factor bounded **differently on the two pieces**, for any measurable `S` and any measure.

This is the architecture the previous entry said was missing.  In the Halász application `S` is the window around
the exceptional frequency: on `S` the third factor has only its trivial bound `M₁ ≍ log N`, but `S` has measure
`O(δ/log z)` so the mean squares over `S` are small; off `S` the factor is damped, `M₂ ≍ e^{−δ²}·log N`.  Neither
piece uses the trivial bound over the whole range, which is what made the previous accounting collapse.

The pieces to supply now are the two corpus facts the corpus's own assembly already uses:
`norm_tsum_twistedSummand_le_of_far` for `M₂` and `volume_halaszLargeValues_le` for the measure of `S` — with the
mean square over `S` bounded by the window mean value theorem at width `|S|` rather than at width `T`.

## The mean square over a short set

`HTGeometry/WeightedHolder.lean` and `RHTower/Sieve/LSeriesTrivialSize.lean` (both green, axiom-clean).

* `integral_normSq_le_measure_mul_sq` — for any measure and any set of finite measure,
  `∫_S ‖g‖² ∂μ ≤ μ.real S · B²` when `‖g‖ ≤ B`.  No nonnegativity of `B` is needed: it follows at any point of
  `S`, and on the empty set both sides vanish.
* `integral_normSq_LSeries_le_measure` — the instance for a finitely supported series, with `B` the `ℓ¹` mass of
  the damped coefficients.

This is the estimate that turns "the exceptional window is short" into a saving, and it completes the two
ingredients of the split:

| piece | bound on `L(f)` | bound on the mean squares |
|---|---|---|
| `S` = large-value set ∩ `[−T,T]` | trivial, `(1+1/(σ−1))e^{7/2}` | `volume.real S · (ℓ¹)²` — small because `S` is short (`volume_halaszLargeValues_le`) |
| `Sᶜ` | damped, `…e^{−δ²}` — **by definition of `S`** | window mean value theorem at width `T` |

Note the economy on the complement: `S` is *defined* as the set where the damped bound fails, so on `Sᶜ` that
bound holds definitionally and `norm_tsum_twistedSummand_le_of_far` is not needed at the point of use — it is
what makes `S` small, inside `volume_halaszLargeValues_le`.

What remains is to instantiate `norm_integral_mul_three_le_split` with this `S`, which needs the measurability of
the large-value set (its defining inequality is continuous in `t`, so it is open in the subspace, hence
measurable) and the arithmetic of choosing `δ` against `logSqWeight z`.

## The large-value window as a measurable set

`RHTower/Sieve/HalaszWindowMeasurable.lean` (green, axiom-clean, wired).

* `isOpen_halaszLargeValues`, `measurableSet_halaszLargeValues` — the exceptional set
  `{t | (damped bound) < ‖L(f,σ+it)‖}` is a strict inequality between a constant and a continuous function of
  the frequency (`continuous_tsum_twistedSummand`), hence open and measurable;
* `volume_inter_Icc_ne_top` — intersected with a bounded height range it has finite measure;
* `norm_tsum_twistedSummand_le_of_not_mem` — off the set the damped bound holds, by definition of the set.

These are exactly the side conditions `norm_integral_mul_three_le_split` requires: a measurable `S`, finite
measure, and a bound on the third factor on each piece.  **Every ingredient of the dichotomy-shaped assembly is
now present:**

| ingredient | theorem |
|---|---|
| the split itself | `norm_integral_mul_three_le_split` |
| `S` measurable, finite | this module |
| damped bound off `S` | this module (definitional) |
| measure of `S` | `volume_halaszLargeValues_le` (corpus) |
| mean square on `S` | `integral_normSq_LSeries_le_measure` |
| mean square off `S` | `integral_Icc_normSq_LSeries_le_prime_sieve` |
| uniform kernel bound | `norm_perronKernel_le` |
| Perron identity | `tsum_mul_smoothWeight_ghs_eq_integral` |

The next step is the assembly, and then the accounting — which this time has the `e^{−δ²}` saving off the window
and the factor `volume S ≍ (T log z/π + 1)·δ/√(logSqWeight z)` on it, the two quantities that the previous
accounting lacked entirely.

## The dichotomy split, assembled

`RHTower/Sieve/DichotomySplitAssembly.lean` (green, axiom-clean, wired).

`norm_integral_Icc_mul_three_le_dichotomy` — for **any** threshold `c ≥ 0`, with `S` the set of heights where the
bounded factor exceeds `c`:

`‖∫_{|y| ≤ T} L(a)L(b)L(f)·W‖
    ≤ (1+1/(σ−1))e^{7/2}·Wsup·√(|S|(ℓ¹a)²)·√(|S|(ℓ¹b)²) + c·Wsup·√(sieve a)·√(sieve b)`.

On `S` the third factor keeps only its trivial size, but the mean squares are charged to `|S|` — the measure of
`S` inside the height range — by the short-set estimate.  Off `S` the factor is at most `c` *by the definition of
`S`*, and the mean squares are the Selberg-sieve ones, reached after enlarging `Sᶜ ∩ [−T,T]` to `[−T,T]`
(`setIntegral_mono_set`, the integrand being nonnegative).

The statement is parameterised by `c` and says nothing about the dichotomy; that is deliberate.  Choosing
`c = (1 + 1/(σ−1))exp(7/2 + 2(σ−1)(log z + log 4) − δ²)` makes it the dichotomy, with
`volume_halaszLargeValues_le` bounding `|S|` by `(2T log z/π + 1)·2√(2π²δ²/logSqWeight z)`.  **This is the shape
in which the mean square finally buys something**: the trivial size appears only against a short set, and the
long range carries the `e^{−δ²}` damping.

The remaining work is the arithmetic of `δ, z, T, σ, H` in this expression — the first accounting in this
programme that has both savings available at once.

## The dichotomy substituted: both savings present at once

`RHTower/Sieve/HalaszDichotomyInstance.lean` (green, axiom-clean, wired).

`norm_integral_Icc_mul_three_le_halasz`, with `halaszDampedBound σ z δ` and `halaszWindowMeasureBound T z δ`
naming the two corpus quantities:

`‖∫_{|y| ≤ T} L(a)L(b)L(f)W‖
    ≤ (1+1/(σ−1))e^{7/2}·Wsup·(window measure)·(ℓ¹a)(ℓ¹b)
      + (damped bound)·Wsup·√(sieve a)·√(sieve b)`.

Taking the split's threshold to be the damped size makes its exceptional window the corpus's large-value set, so
`volume_halaszLargeValues_le` applies; `ENNReal.toReal_le_of_le_ofReal` converts its `ENNReal` bound to the real
one the estimate needs.  The two square roots of `|S|(ℓ¹)²` combine into `|S|·(ℓ¹a)(ℓ¹b)` exactly, not up to a
constant.

**Both savings are present simultaneously** — the trivial size only against a short window, the `e^{−δ²}` damping
over the whole range.  That is the property the two collapsed accountings lacked, and it is what makes the
remaining arithmetic worth attempting:

* first term: `(log N)·N·[(2T log z/π + 1)·2√(2π²δ²/logSqWeight z)]·(ℓ¹a)(ℓ¹b)`, and `logSqWeight z ≍ (log z)²/2`,
  so the bracket is `≍ Tδ log z·(1/log z) = Tδ`;
* second term: `(log N)e^{−δ²}·N·√(sieve a)√(sieve b)`, with the sieve sums as computed before.

So `δ` trades a linear cost in the window against an exponential gain off it — the classical Halász balance,
now available in the corpus in a form where both terms are explicit.

## The window measure with the frequency weight evaluated

`RHTower/Sieve/HalaszWindowWeightBound.lean` (green, axiom-clean, wired).

* `logSqWeight_ge_quarter` — `logSqWeight z = (log z)²/2 − 39 log z − 25 ≥ (log z)²/4` once `log z ≥ 160`; the
  threshold is what absorbs the linear terms (`160²/4 = 6400 ≥ 39·160 + 25`);
* `halaszWindowMeasureBound_le` —
  `halaszWindowMeasureBound T z δ ≤ (2T log z/π + 1)·(4√2 πδ/log z)`.

Multiplied by the trivial size, the window term is of order `T δ`, so the exceptional window costs a term
**linear** in the distance level while off the window the series is damped by `e^{−δ²}`.  That is the Halász
balance, and both sides of it are now explicit theorems of the corpus.

Substituting into the dichotomy instance, the truncated integral is at most

`(log N)·N·(8√2 Tδ + 4√2 πδ/log z)·(ℓ¹a)(ℓ¹b) + (log N)e^{−δ²}·N·√(sieve a)√(sieve b)`

up to the constants carried by the theorems.  The `ℓ¹` masses of the two prime weights are `O((log N)²)` at `σ`
near `1`, and the sieve sums are as computed earlier, so the balance to strike is

`T δ (log N)^{O(1)}   against   e^{−δ²}(log N)^{O(1)}`,

which is solved by `δ ≍ √(log log N)` provided `T` is at most a power of `log N` — and `T` only needs to be large
enough for the tail `C/T` of the height split, where `C ≍ N^σ(N/H)²` forces `T ≳ (N/H)²`.  That is the last
constraint to check: it wants `H` close to `N`, while the smoothing error wants `H` small, and whether the two
are compatible is now a finite computation with all constants in hand.

## The window term is still too lossy: it needs the sieve, not the trivial size

Balancing the two terms of the dichotomy instance exposes a third loss, in the *window* term this time.

With `H = N/(log N)^k` the kernel's decay constant is `C ≍ N(log N)^{2k}`, so the tail `Mg·C·(π − 2 arctan T) ≍
Mg·C/T` demands `T ≳ (log N)^{2k+4}` (with `Mg ≍ (log N)^5`).  But the window term, as currently bounded, is

`(log N)·N·(8√2 Tδ)·(ℓ¹a)(ℓ¹b) ≍ N(log N)^5·Tδ`,

which demands `Tδ ≪ (log N)^{−4}`.  The two are incompatible: the tail wants `T` large, the window wants it
small.

**Two separate losses in the window term, both repairable, and the corpus already owns the repairs.**

1. *The measure bound is the cell-covering one, not the diameter.*  `volume_halaszLargeValues_le` bounds the
   window by `(2T log z/π + 1)·2√(2π²δ²/logSqWeight z)` — a union of `O(T log z)` cells.  But
   `HalaszLargeValueWindow.abs_sub_le_of_norm_gt` proves all large values lie within a *single* window of
   diameter `O(δ/log z)`: the set is one short interval, and its measure is `O(δ/log z)` with no `T` at all.
2. *The mean square on the window is bounded by measure × (ℓ¹ mass)².*  That is the trivial bound, lossy by the
   square of the coefficient mass: `(ℓ¹)² ≍ (log N)⁴` where the sieve mean square is `≍ (log N)²`.  On an
   interval the right estimate is the corpus's window mean value theorem at the interval's own width, which is
   proportional to the width rather than to the width times `(ℓ¹)²`.

Repair 2 needs one device the corpus lacks: the window is centred at the exceptional frequency `t₀`, not at `0`,
while `integral_Icc_normSq_logPoly_le_prime_sieve` is stated on `Icc (−W) W`.  The fix is **translation
invariance of the mean square**: `L(a, σ+i(t₀+u))` is the polynomial with coefficients `a_n n^{−it₀}` evaluated
at `u`, and those have the same moduli, so every coefficient-modulus bound — in particular the whole sieve
estimate — applies verbatim.  That is the next brick, and it is elementary.

Recorded before attempting it, so the next pass starts from the diameter and the translated sieve rather than
from the covering and the trivial size.

## Translating the frequency twists the coefficients

`RHTower/Sieve/LSeriesTranslate.lean` (green, axiom-clean, wired).  This is the device the previous entry named as
missing.

* `norm_natCast_cpow_im` — the twist `n^{−it₀}` is unimodular;
* `LSeries_translate` — `L(a, σ+i(t₀+u)) = L(a_n n^{−it₀}, σ+iu)`;
* `integral_Icc_normSq_LSeries_translate` — hence the mean square over an interval centred at `t₀` is the mean
  square of the twisted coefficients over an interval centred at `0`;
* `integral_Icc_normSq_LSeries_translate_le_prime_sieve` — and the sieve bound for it is the bound for the
  **untwisted** coefficients: the twist is invisible to any estimate that sees only moduli.

So the window of the dichotomy can be estimated by the window mean value theorem at its own width `W`:

`∫_{|u| ≤ W} ‖L(a,σ+i(t₀+u))‖² du ≤ 2π(5W/4)·∑_n (2(n(e^{1/W} − e^{−1/W}) + 1)/log Y + E + z)‖a_n n^{−σ}‖²`,

which is proportional to `W` — not to `W·(ℓ¹)²`.  With `W ≍ δ/log z` the diameter of the large-value set
(`abs_sub_le_of_norm_gt`), the window term becomes `≍ (δ/log z)·(sieve mass)` instead of
`(Tδ)·(ℓ¹ mass)²`: both the spurious `T` and the square of the `ℓ¹` mass are gone.

The remaining step is to re-derive the split with the window bounded this way — the split lemma itself is
unchanged, only the estimate fed to it on `S` — and then the balance is `δ/log z` against `e^{−δ²}`, which
`δ ≍ √(log log N)` solves with room to spare.

## The window mean square, by the sieve at the window's own width

`RHTower/Sieve/WindowMeanSquareDiameter.lean` (green, axiom-clean, wired).

* `subset_Icc_of_diameter` — a set of diameter `R` is empty or contained in a ball of radius `R` about one of its
  points;
* `integral_Icc_shift` — shifting the interval of integration to the origin;
* `integral_normSq_LSeries_le_of_diameter` — hence, for any set of diameter `R`,

  `∫_S ‖L(a,σ+it)‖² dt ≤ 2π(5R/4)·∑_n (2(n(e^{1/R} − e^{−1/R}) + 1)/log Y + E + z)·‖a_n n^{−σ}‖²`.

Proportional to `R` **and to the sieve mass**, in place of the trivial `R·(ℓ¹ mass)²` — the loss diagnosed two
entries ago.  The empty case is handled separately (both sides nonnegative), and the frequency translation is
absorbed by the coefficients.

Applied to the exceptional window, whose diameter the corpus bounds by
`2√(2π²δ²/logSqWeight z) ≤ 4√2 πδ/log z` (`abs_sub_le_of_norm_gt`, `logSqWeight_ge_quarter`), the window term of
the dichotomy is now

`(log N)·N·√(2π(5R/4)·sieve a)·√(2π(5R/4)·sieve b)   with R ≍ δ/log z`,

i.e. `≍ (log N)·N·(δ/log z)·(sieve mass)` — no `T`, no `(ℓ¹)²`.  Against the off-window term
`(log N)e^{−δ²}·N·(sieve mass)` the balance is `δ/log z` versus `e^{−δ²}`, and `δ ≍ √(log log N)` gives a saving
of `1/log log N` in the first against `1/log N` in the second.

Both terms are now genuinely smaller than the main term, which is what the whole architecture was for.  What
remains is to state the split with this window bound in place — the split lemma is unchanged, only its input on
`S` — and to fix the parameters.

## Correction: the diameter bound is per cell, not global — and the `T` tension is fundamental to the measure route

Reading `abs_sub_le_of_norm_gt` closely corrects the previous entry.  Its hypotheses include the **spacing**
condition `|t − u|·log z ≤ π`: the diameter bound holds only for pairs already within `π/log z` of each other.  The
large-value set is therefore *not* of small diameter globally; it is small **inside each cell** of length
`π/log z`, which is exactly why the corpus's `volume_halaszLargeValues_le` carries the covering factor
`(2T log z/π + 1)`.  My previous entry claimed a global diameter; that was a misreading.

With the per-cell diameter the window mean square is `∑_{cells} ∫_{S ∩ cell}`, and the new
`integral_normSq_LSeries_le_of_diameter` bounds each cell's contribution by `2π(5R/4)·(sieve mass)` with
`R ≍ δ/log z`.  Summing over `O(T log z)` cells gives `≍ Tδ·(sieve mass)`.  So replacing the trivial bound by the
sieve did remove the `(ℓ¹)²`, but the factor `T` remains, and the tension is unresolved:

* the **tail** of the height split needs `T ≳ Mg·C/(N log N) ≍ (log N)^{2k+4}`;
* the **window** needs `Tδ·(sieve mass) ≪ 1`, i.e. `T ≪ 1/(δ(log N)²)`.

These are incompatible for any `δ > 0`.  **The obstruction is structural to the measure-based treatment of the
window**: bounding the window's contribution by (number of cells)×(per-cell mean square) charges every cell of
`[−T,T]` whether or not the large-value set meets it.

**The resolution the classical argument uses, and which the corpus already owns.**  Halász's method does not
measure the exceptional set; it counts *well-spaced* large-value points and uses a large-values estimate — the
number of `δ`-spaced points with `|L| > V` is `≪ T + (coefficient mass)/V²`, so the count is governed by `V`, not
by `T` alone.  The corpus's `DirichletLargeValues`, `DirichletLargeValuesCount`, `DirichletMeasureLargeValues`,
`LargeSieveGallagher` and `PrimePowerLargeValuesCount` are that layer, and `HalaszFullSeriesSum`'s
`sum_norm_tsum_twistedSummand_le_of_spacing` is the corpus's own combination of a spacing hypothesis with the
damped bound.

So the next attempt should replace the "measure of the window" step by the corpus's spacing/count step:
`sum_norm_tsum_twistedSummand_le_of_spacing` bounds a *sum over well-spaced frequencies*, which is what the
Cauchy–Schwarz split should consume in place of an integral over `S`.  Recorded before attempting it — this is the
third architectural correction in this programme, and each has come from computing the balance rather than from
reading the construction.

## The resolution: the exceptional set is one *point*, not a window — discretise the integral

`HalaszFullSeriesSum.sum_norm_tsum_twistedSummand_le_of_spacing` is the corpus's sharp form of the dichotomy, and
reading it settles the architecture.  Over a `Δ`-spaced finite set `S` of frequencies,

`∑_{t ∈ S} ‖L(f,σ+it)‖ ≤ (1 + 1/(σ−1))·exp(7/2 + 2(σ−1)(log z + log 4))·(|S|·e^{−δ²} + 1)`,

because **at most one point of `S` can be close** to the extremal character (`card_filter_close_le_one_of_spacing`).
So one point pays the trivial bound and every other point is damped by `e^{−δ²}` — the exceptional set is a single
*point*, not a set of positive measure.

That is why every measure-based accounting in this programme has failed, including the corpus's own
`HalaszPerronAssembly`, whose bound `Wsup·(damped·2T + trivial·(2T log z/π + 1)·2√(2π²δ²/logSqWeight z))` is
`≍ N(log N)(e^{−δ²}T + Tδ)` and needs `T ≪ 1` to beat `N log N`.  The `T` in the second term comes from charging
the trivial bound to a *window* of `O(T log z)` cells rather than to one point.

**The missing device is a discretisation.**  Cover `[−T,T]` by `O(T/Δ)` cells of length `Δ`; on each closed cell a
continuous integrand attains its maximum (`IsCompact.exists_isMaxOn`), so

`∫_{−T}^{T} |F| ≤ Δ·∑_{cells} max_{cell} |F|`,

and the cell maximisers form a `Δ`-spaced set to which the corpus's spacing bound applies.  Then the integral is
`≲ Δ·[trivial·1 + damped·(T/Δ)] = Δ·trivial + T·damped`, with **no `Tδ` term**: the first is negligible for small
`Δ`, the second carries `e^{−δ²}`.

This is the classical Halász architecture, and it needs exactly one new general lemma — the cell-supremum
discretisation of an integral — plus the observation that cell maximisers are `Δ`-spaced.  Everything else,
including the spacing bound itself, the corpus already owns.  Recorded as the specification for the next brick.

## Discretisation by cell maxima

`HTGeometry/CellMaxDiscretisation.lean` (new, green, axiom-clean, wired) — the device the previous entry specified.

`exists_cell_max_integral_le` : for continuous `F`, splitting `[a, a+mΔ]` into `m` closed cells of length `Δ`,

`∃ c : ℕ → ℝ`, each `c k` in the `k`-th cell, with   `∫_a^{a+mΔ} F ≤ ∑_{k<m} Δ·F(c k)`.

The maximisers are produced by the statement, which is the point: an estimate for sums over well-spaced
frequencies can consume them.  `IsCompact.exists_isMaxOn` supplies each cell's maximiser,
`intervalIntegral.sum_integral_adjacent_intervals` reassembles the cells, and `integral_mono_on` against the
constant `F (c k)` bounds each cell.

**Why this is the right shape.**  Maximisers of cells of the *same parity* are at distance at least `Δ` — cell `k`
ends where cell `k+1` begins, so consecutive maximisers can coincide, but cells `k` and `k+2` are separated by a
full cell.  Splitting into even and odd families therefore gives two `Δ`-spaced families at the cost of a factor
two, and on each the corpus's `sum_norm_tsum_twistedSummand_le_of_spacing` applies: one frequency pays the trivial
size, all others are damped.

That converts the Halász dichotomy into an integral bound of the shape `Δ·(trivial) + T·(damped)` instead of
`Tδ·(trivial) + T·(damped)`.  The next brick is the parity split, and then the balance — which no longer contains
the product `T·δ` that defeated the previous three accountings.

## The parity split: an integral against two well-spaced families

`HTGeometry/CellMaxDiscretisation.lean` (appended; green, axiom-clean).

* `cell_points_spaced` — maximisers of cells of the same parity are at distance at least `Δ`: distinct indices of
  one parity differ by at least two, so a whole cell separates them;
* `exists_spaced_families_integral_le` — hence for continuous `F`,

  `∃ S₁ S₂ : Finset ℝ`, both `Δ`-spaced, with   `∫_a^{a+mΔ} F ≤ Δ·(∑_{t ∈ S₁} F t + ∑_{t ∈ S₂} F t)`.

The spacing gives injectivity of the maximiser map on each parity class, so the sums over index sets become sums
over sets of *points* — which is the form the corpus's `sum_norm_tsum_twistedSummand_le_of_spacing` consumes, its
hypothesis being exactly `∀ t ∈ S, ∀ u ∈ S, t ≠ u → Δ ≤ |t − u|`.

**The chain is now complete in shape.**  For the Halász integrand,

`∫_{−T}^{T} ‖L(f,σ+it)‖ dt ≤ Δ·(∑_{S₁} + ∑_{S₂}) ≤ Δ·2·(1+1/(σ−1))e^{7/2+2(σ−1)(log z+log 4)}·(|S|e^{−δ²} + 1)`

with `|S| ≤ T/Δ`, giving `≍ (log N)(T e^{−δ²} + Δ)`.  Choosing `Δ` small makes the second term negligible, and the
first carries the damping — no `Tδ` term anywhere.  That is the bound the corpus's own assembly was missing, and
with it the Halász mean-value theorem becomes a matter of choosing `δ` and `z`.

## Correction: the corpus's dichotomy is local — but its large-values count is the global mechanism, and it exists

Attempting to feed the spaced families into `sum_norm_tsum_twistedSummand_le_of_spacing` exposes its second
hypothesis: besides the spacing `Δ ≤ |t − u|`, it requires `|(t − u)·log p| ≤ π` for all `p ≤ z` — an *upper* bound
on the spread of the family.  So the bound applies only to families inside a single cell of length `π/log z`, and
"at most one close point" means one per such cell — `O(T log z)` of them across `[−T, T]`.  My previous entry read
it as global; it is local.  Which is the same locality that makes the measure route lose `T log z`.

**But the corpus already owns the global mechanism.**  `DirichletLargeValuesCount.card_largeValues_le` is a
Montgomery-type large-values estimate: for `δ`-spaced frequencies `lam 0 < … < lam R` in `[0,T]` at which a
Dirichlet polynomial of length `N` has `‖dirPoly N a (lam r)‖ ≥ V`,

`(R+1)·V² ≤ (T + 4N(1 + log N))·(1/δ + 2 log N)·∑_m ‖a_m‖²`.

That bounds the *number* of spaced large values by `(T + N log N)(1/δ + log N)·(ℓ² mass)/V²` — governed by the
threshold `V`, not by the measure of a window.  This is exactly the mechanism the classical Halász argument uses in
place of the distance dichotomy, and it applies to the two prime polynomials `L(a)`, `L(b)`, which are finite.

**The next brick is a sum-from-counts device.**  The count gives, for each threshold, how many spaced points exceed
it; a dyadic decomposition in `V` converts that into a bound on `∑_{t ∈ S} ‖D(t)‖` over a spaced set `S`.  With the
discretisation already built, the chain becomes

`∫ |L(a)L(b)L(f)| ≤ Wsup·Δ·∑_{spaced} |L(a)L(b)|·|L(f)| ≤ Wsup·Δ·(trivial size of L(f))·∑_{spaced} |L(a)L(b)|`,

and the last sum is what the large-values count controls — with no window, no measure, and no `Tδ`.

Recorded as the specification: the corpus has the count and the discretisation; what is missing is the dyadic
sum-from-counts lemma, which is elementary and general.

## The sum-from-counts device already exists: `DirichletLargeValuesL1`

The brick specified in the previous entry is already in the corpus, and in a better form than the dyadic
decomposition I was about to write.  `DirichletLargeValuesL1.sum_norm_dirPoly_le_sqrt`:

`∑_{r ≤ R} ‖dirPoly N a (λ_r)‖ ≤ √((R+1)·(T + 4N(1 + log N))(1/δ + 2 log N)·∑_m ‖a_m‖²)`

on any `δ`-spaced set `λ_0 < … < λ_R` in `[0,T]` — the first moment straight from the mean value theorem by
Cauchy–Schwarz, no dyadic decomposition in `V` needed.  Its module docstring says exactly why it is there: "the
first moment and the large-value count, not the mean square, are what the bilinear method uses".

**So the remaining gap is a formulation bridge, not a mathematical device.**  The corpus's large-values layer is
indexed — `lam : ℕ → ℝ` with `hgap : ∀ i, lam i + δ ≤ lam (i+1)`, `hlow`, `hhigh` — while the discretisation
produces `Finset ℝ` families of cell maximisers.  The bridge is to index the even-indexed maximisers,

`lam j := if 2j < m then c (2j) else a + 2jΔ`,

which satisfies the gap condition for *all* `i`: within the range because cells `2j` and `2j+2` are separated by a
full cell, past it because the fallback is an arithmetic progression of step `2Δ`, and at the boundary because
`c (2j) ≤ a + (2j+1)Δ`.  The same for the odd family.

With that bridge the chain is complete and contains no window and no measure:

`∫_{−T}^{T}|L(a)L(b)L(f)| ≤ Wsup·Δ·(trivial size of L(f))·∑_{spaced} |L(a)L(b)|`
  `≤ Wsup·Δ·(log N)·√((T/Δ)(T + 4N(1+log N))(1/Δ + 2 log N)·(ℓ² mass))`,

so the `√` carries `T/Δ·T/Δ ≍ T²/Δ²` against the `ℓ²` mass of the prime coefficients — and `Δ` cancels against the
prefactor.  That is the Montgomery–Halász shape, and unlike every earlier attempt in this programme it has no term
in which the trivial size multiplies a length.

## The bridge: cell maximisers as an indexed sequence with a uniform gap

`HTGeometry/CellMaxDiscretisation.lean` (appended; green, axiom-clean).

`exists_gap_sequence_of_cells` — for cell maximisers `c` and any residue `r`,

`∃ lam : ℕ → ℝ`, with `∀ i, lam i + Δ ≤ lam (i+1)`, and `lam j = c (2j + r)` whenever `2j + r < m`.

The sequence is `lam j = if 2j + r < m then c (2j+r) else a + (2j+r)Δ`: inside the range consecutive terms are
maximisers of cells two apart, hence separated by a full cell; past it the fallback is an arithmetic progression of
step `2Δ`; and at the boundary the last maximiser is at most `a + (2j+r+1)Δ`, one cell below the first fallback
term.  So the gap holds at **every** index, which is what the corpus's large-values estimate requires — it quantifies
over all `i`, not only those below the range.

Taking `r = 0` and `r = 1` gives the two parity families.  This is the last formulation gap between the
discretisation and `DirichletLargeValuesL1.sum_norm_dirPoly_le_sqrt`; what remains to connect them is bookkeeping of
the two remaining mismatches:

* the corpus's estimate is stated for frequencies in `[0,T]` with `hlow : δ/2 ≤ lam 0` and `hhigh : lam R + δ/2 ≤ T`,
  while the discretisation runs over `[−T,T]` — a shift, harmless because translating the frequency twists the
  coefficients without changing their moduli (`LSeries_translate`, and the `ℓ²` mass in the estimate is a sum of
  moduli);
* the estimate is stated for `dirPoly` (coefficients indexed by `Fin N`), while the chain carries `LSeries` of a
  finitely supported sequence — and `logPoly_eq_dirPoly` together with `LSeries_eq_logPoly_of_support` already
  connects those two.

Both are conversions the corpus already owns; neither is a new estimate.

## Reindexing the parity families

`HTGeometry/CellMaxDiscretisation.lean` (appended; green, axiom-clean).

* `sum_filter_even_eq_sum_range` — `∑_{k < m, k even} g k = ∑_{j < ⌈m/2⌉} g (2j)`;
* `sum_filter_odd_eq_sum_range` — `∑_{k < m, k odd} g k = ∑_{j < ⌊m/2⌋} g (2j+1)`.

Both for an arbitrary additive monoid, by `Finset.sum_nbij'` with the inverse pair `k ↦ k/2`, `j ↦ 2j` (resp.
`2j+1`), every side condition discharged by `omega`.

This is the last piece of index bookkeeping: the discretisation delivers sums over parity-filtered ranges, the
corpus's large-values estimate consumes `∑_{r ∈ range (R+1)}`, and these identities convert one to the other with
`R + 1 = ⌈m/2⌉` and `⌊m/2⌋`.

**Inventory for the Montgomery–Halász route.**  All of the following are now in the corpus and unconditional:

| step | theorem |
|---|---|
| integral → cell maxima | `exists_cell_max_integral_le` |
| maxima → two spaced families | `exists_spaced_families_integral_le`, `cell_points_spaced` |
| spaced family → indexed gap sequence | `exists_gap_sequence_of_cells` |
| parity sums → `range (R+1)` sums | this entry |
| spaced sum of a polynomial → `ℓ²` mass | `sum_norm_dirPoly_le_sqrt` (corpus, pre-existing) |
| `LSeries` → `logPoly` → `dirPoly` | `LSeries_eq_logPoly_of_support`, `logPoly_eq_dirPoly` |
| frequency shift | `LSeries_translate` |

What remains is to compose them, which is a single (long) chain of rewrites with no estimate left to prove, and then
the parameter choice — where, for the first time in this programme, the bound to optimise has no term in which a
trivial size multiplies a length.

## Specification of the composition (next brick, ready to implement)

The pieces are all present; what follows is the exact statement to prove and the parameter choices that make the
corpus's hypotheses match, worked out and checked against a type-correct skeleton.

```
theorem integral_norm_dirPoly_le_largeValues (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {Δ : ℝ}
    (hΔ : 0 < Δ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in (Δ/2)..(Δ/2 + (2*n : ℕ)*Δ), ‖dirPoly N a t‖)
      ≤ 2*Δ*√((n : ℝ) * (((2*n+1 : ℕ)*Δ + 4*N*(1 + log N))*(1/Δ + 2*log N)*∑ i, ‖a i‖²))
```

Choices that align the hypotheses:

* **`m = 2n` cells** starting at `a = Δ/2`, so each parity family has exactly `n` points and the corpus's
  `∑_{r ∈ range (R+1)}` matches at `R + 1 = n`;
* **`T = (2n+1)Δ`**, which is `Δ/2 + 2nΔ + Δ/2`: then `hlow : Δ/2 ≤ lam 0` holds because `c 0 ≥ Δ/2`, and
  `hhigh : lam R + Δ/2 ≤ T` because the last maximiser is at most `Δ/2 + 2nΔ`;
* `δ = Δ` in the large-values estimate, supplied by `exists_gap_sequence_of_cells`.

Steps: `exists_cell_max_integral_le` → `sum_filter_even_eq_sum_range`/`sum_filter_odd_eq_sum_range` to reindex →
`exists_gap_sequence_of_cells` at `r = 0, 1` for the gap → `sum_norm_dirPoly_le_sqrt` twice → add the two roots
(`√x + √x = 2√x`).

The `n = 0` case is excluded by `hn` only for convenience: there both sides vanish, but the empty family makes
`hlow` vacuous and the corpus's estimate is stated for a nonempty range.

Recorded at this level of detail because the composition is mechanical and long; the next pass should be able to
write it without re-deriving any of the alignment.

## The composition, done

`RHTower/Sieve/DirichletFirstMomentLargeValues.lean` (green, axiom-clean, wired).

`integral_norm_dirPoly_le_largeValues` :

`∫_{Δ/2}^{Δ/2+2nΔ} ‖D(t)‖ dt ≤ 2Δ·√(n·((2n+1)Δ + 4N(1+log N))(1/Δ + 2 log N)·∑_i ‖a_i‖²)`

for every Dirichlet polynomial of length `N ≥ 2`, every cell length `Δ > 0` and every `n ≥ 1`.  It compiled from the
specification without correction, which is what the specification was for.

**No window and no measure appears anywhere in the bound.**  It is governed by the number of cells and the `ℓ²` mass
of the coefficients; the trivial size of the integrand multiplies nothing.  That is the property the four
measure-based accountings in this programme all lacked, and it is why the earlier routes could not reach below the
trivial bound however the parameters were chosen.

Sizes, for the record.  With `Δ = 1/log N` and `2nΔ = 2T₀` (so `n ≍ T₀ log N`), the bound is

`≍ (1/log N)·√(T₀ log N·(T₀ + N log N)·(log N)·(ℓ² mass))`,

so the first moment over a height range `T₀` is `≍ √(T₀(T₀ + N log N)(ℓ² mass))/√(log N)` — square-root cancellation
in the height, which is the Montgomery–Halász gain and exactly what a mean-value theorem for the partial sums needs.

This closes the analytic half of the programme in a form that can beat the trivial bound.  What remains is to feed it
the two prime polynomials of the Granville–Harper–Soundararajan convolution, whose `ℓ²` masses the dyadic Chebyshev
cap already controls, and to fix the parameters.

## The first moment on an arbitrary interval

`RHTower/Sieve/DirichletFirstMomentShift.lean` (green, axiom-clean, wired).

* `dirPoly_translate` — `D(t₀+t)` is the polynomial with coefficients `a_i e^{i t₀ log(i+1)}` at `t`;
* `norm_dirPoly_twist_coeff` — the twist is unimodular;
* `integral_norm_dirPoly_le_largeValues_shift` — hence the large-values first moment holds on **every** interval of
  length `2nΔ`:

  `∫_{t₀}^{t₀+2nΔ} ‖D(t)‖ dt ≤ 2Δ·√(n·((2n+1)Δ + 4N(1+log N))(1/Δ + 2 log N)·∑‖a_i‖²)`.

The `ℓ²` mass is unchanged by the twist, so the right-hand side is the same for every `t₀`.  In particular the bound
applies to `[−T, T]`, which is the range a Perron integral runs over — the canonical interval `[Δ/2, Δ/2+2nΔ]` of the
composition was an artefact of matching the corpus's `hlow`/`hhigh`, and this removes it.

`intervalIntegral.integral_comp_add_left` does the shift; the twist is what keeps the bound's right-hand side fixed.
One incidental: `ring` failed on the exponent identity where `ring_nf` succeeded, which Lean itself suggested — the
two differ on goals with casts inserted by `push_cast`.

## The first moment for `LSeries`

`RHTower/Sieve/LSeriesFirstMomentLargeValues.lean` (green, axiom-clean, wired).

`integral_norm_LSeries_le_largeValues` :

`∫_{|y| ≤ nΔ} ‖L(a, σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M(1+log M))(1/Δ + 2 log M)·∑_i ‖a_{i+1}(i+1)^{−σ}‖²)`

for `a` supported in `[1, M]`, `M ≥ 2`.  The chain is `LSeries_eq_logPoly_of_support` → `logPoly_eq_dirPoly` →
reflection (absorbed by the symmetric interval) → the shifted large-values first moment.

**The analytic half of the programme is now complete in the Montgomery–Halász form.**  Every step is unconditional
and no step assumes an estimate:

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖ dy  ≲  Δ·√((T/Δ)(T + M log M)(1/Δ + log M)·(ℓ² mass of the damped coefficients))`.

Comparison with the routes that failed: the Lorentzian route multiplied the mean squares by the kernel's
quadratic-decay constant `N^σ(N/H)²`; the measure route charged the trivial size to a window of `O(T log z)` cells.
This bound has neither — the trivial size of the integrand appears nowhere, and the only inputs are the number of
cells and an `ℓ²` mass.

For the two prime weights of the convolution the `ℓ²` masses are `∑_p (log p)²p^{−2σ}` and
`∑_p (log p/log⌊N/p⌋)²p^{−2σ}`, both bounded by the dyadic Chebyshev cap `sum_prime_logSq_rpow_neg_le` at
`w = 2σ`.  Feeding those in, together with the Perron identity and the smoothing connector, is what remains.

## The first moment of the inner prime weight

`RHTower/Sieve/GhsInnerFirstMoment.lean` (green, axiom-clean, wired).

* `sum_fin_normSq_damped_eq` — the `ℓ²` mass over `Fin M` is the sum over `[1, M]`, via the corpus's
  `sum_fin_eq_sum_Icc` (found rather than rebuilt — it is in `DirichletIntegralMeanValue`, where the mean value
  theorem needed the same reindexing);
* `integral_norm_LSeries_ghsInner_le` :

  `∫_{|y| ≤ nΔ} ‖L(b, σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M(1+log M))(1/Δ + 2 log M)·cap(2σ))`

  for the inner weight `b = ghsInner f M`, with `cap` the dyadic Chebyshev bound `sieveCapPrime`.

Every quantity on the right is explicit in `n, Δ, M, σ`: no window, no measure, and no trivial size of the series.
The coefficients vanish off the primes and are at most `log p` on them, so the mass is bounded by the prime sum the
cap controls.

**This is the first bound in the programme that is both about the actual GHS weights and free of every structural
defect diagnosed along the way.**  The outer weight follows the same route with its block-damped bound in place of
`log q`, and then the two feed the Perron identity.

## Both prime weights: one law, two instances

`RHTower/Sieve/GhsInnerFirstMoment.lean` generalised (green, axiom-clean).

`integral_norm_LSeries_prime_le` — for **any** coefficients supported on the primes of `[1, M]` with
`‖a_k‖ ≤ A log k`:

`∫_{|y| ≤ nΔ} ‖L(a, σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M(1+log M))(1/Δ + 2 log M)·A²·cap(2σ))`.

The two weights of the convolution are instances: `integral_norm_LSeries_ghsInner_le` at `A = 1`, and
`integral_norm_LSeries_ghsOuter_le` at `A = 1/log 2`.  The inner theorem committed last round is now that instance,
so its proof is no longer duplicated.

**Status of the route.**  For the two prime polynomials the first moment on a vertical segment is bounded by an
expression explicit in `n, Δ, M, σ` and free of every defect diagnosed in this programme.  Combined with the Perron
identity for the triple convolution, the Euler bound for the third factor, the smoothing connector and the
recursion half, the chain from `(∑_{n ≤ N} f(n))·log N` to explicit constants is closed **except** for one step: the
Perron integrand is a *product* of three series, and the first-moment bound applies to one series at a time.  Two
ways to close that gap, both available:

* bound `‖L(a)L(b)‖` pointwise by `‖L(a)‖·(ℓ¹ mass of b)` and use the first moment for `L(a)` alone — cheap, loses
  the second saving;
* apply Cauchy–Schwarz to the pair and use the *mean square* (already in the corpus in both the Lorentzian and the
  truncated form) for each factor — keeps both savings.

The second is the GHS shape and the estimates for it are all present; the first is a fallback that still beats the
trivial bound if the coefficient masses are small enough.  Deciding between them is the next step, and it is a
choice about which bound to compose rather than a missing device.

## The product needs no Cauchy–Schwarz: it is a single series

Considering how to handle the product of the two prime polynomials settles the question in a way that removes a step
rather than adding one.  `L(a, s)·L(b, s) = L(a ⍟ b, s)` — mathlib's `LSeries_convolution'` — and `a ⍟ b` is again a
*finitely supported* sequence, carried by the products of two primes in `[1, M²]`.  So the general first-moment
bound `integral_norm_LSeries_le_largeValues`, which needs only finite support, applies to the product **directly**:

`∫_{|y| ≤ nΔ} ‖L(a,σ+iy)L(b,σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M²(1+log M²))(1/Δ + 2 log M²)·(ℓ² mass of a ⍟ b))`.

No Cauchy–Schwarz, no splitting into two mean squares, and no trivial size anywhere.  This is better than both
options recorded last round.

**The one missing brick is the `ℓ²` mass of the convolution.**  For prime-supported `a, b` the coefficients of
`a ⍟ b` are carried by `pq`, and

`∑_k ‖(a ⍟ b)(k)‖²k^{−2σ} ≤ 2·(∑_p ‖a_p‖²p^{−2σ})·(∑_q ‖b_q‖²q^{−2σ})`,

the factor `2` covering the two orderings of a product of distinct primes and the diagonal `p = q` contributing once.
Each factor is then the dyadic Chebyshev cap.  The inequality is Cauchy–Schwarz on the divisor sum followed by the
observation that a product of two primes has at most two such factorisations — elementary, and it is the last
estimate the route needs.

Recorded as the specification.  Note that this also retires the `dampedL1`/`truncSieveSum` pair from the truncated
step 4: with the product handled as one series, the two mean squares of that assembly are replaced by a single mass,
and the Euler factor multiplies nothing of length.

## The support of the convolution

`RHTower/Sieve/ConvolutionSupport.lean` (green, axiom-clean, wired).

* `convolution_mem_Icc_of_support` — a convolution of two sequences supported in `[1, M]` is supported in `[1, M²]`;
* `convolution_support_prime_mul` — a convolution of two prime-supported sequences is carried by products of two
  primes.

Both from `Finset.exists_ne_zero_of_sum_ne_zero` on the antidiagonal: a nonzero coefficient forces a factorisation
with both factors in the supports.

With these the product `L(a,s)L(b,s) = L(a ⍟ b, s)` is a single finitely supported Dirichlet series of length `M²`,
so `integral_norm_LSeries_le_largeValues` applies to it.  The remaining input is the `ℓ²` mass of `a ⍟ b`, for which
the route is:

* expand `(a ⍟ b)(k)` over the antidiagonal and apply `sq_sum_le_card_mul_sum_sq`, giving
  `‖(a ⍟ b)(k)‖² ≤ d(k)·∑_{de=k} ‖a_d‖²‖b_e‖²`;
* on the support `d(k) ≤ 4`, since `k` is a product of two primes (`convolution_support_prime_mul`);
* swap the double sum to a product of two single sums — the sigma-set swap in `RHTower/DirichletSummatorySwap.lean`
  does exactly this reindexing for the summatory function and is the model to follow;
* each factor is then the dyadic Chebyshev cap.

So `∑_k ‖(a ⍟ b)(k)‖²k^{−2σ} ≤ 4·cap(2σ)²·A_a²A_b²`, and the first moment of the product is explicit.

## Specification of the last estimate: the `ℓ²` mass of the convolution

```
theorem sum_normSq_convolution_le {a b : ℕ → ℂ} {M : ℕ}
    (ha : ∀ k, a k ≠ 0 → k ∈ Finset.Icc 1 M) (hb : ∀ k, b k ≠ 0 → k ∈ Finset.Icc 1 M)
    (hap : ∀ k, a k ≠ 0 → Nat.Prime k) (hbp : ∀ k, b k ≠ 0 → Nat.Prime k) {σ : ℝ} (hσ : 0 < σ) :
    ∑ k ∈ Finset.Icc 1 (M*M), ‖(a ⍟ b) k‖^2 * (k:ℝ)^(-(2*σ))
      ≤ 4 * (∑ d ∈ Finset.Icc 1 M, ‖a d‖^2 * (d:ℝ)^(-(2*σ)))
            * (∑ e ∈ Finset.Icc 1 M, ‖b e‖^2 * (e:ℝ)^(-(2*σ)))
```

Steps, with the one subtlety marked:

1. `‖(a ⍟ b) k‖ ≤ ∑_{x ∈ k.divisorsAntidiagonal} ‖a x.1‖‖b x.2‖` — `norm_sum_le`;
2. square and apply `sq_sum_le_card_mul_sum_sq`, giving the factor `#k.divisorsAntidiagonal = d(k)`;
3. **the divisor count is bounded only on the support**: if `(a ⍟ b) k ≠ 0` then `k = pq`
   (`convolution_support_prime_mul`) so `d(k) ≤ 4`, and if `(a ⍟ b) k = 0` the term is zero — so the bound
   `‖(a ⍟ b) k‖² ≤ 4·∑_x ‖a x.1‖²‖b x.2‖²` holds for *every* `k` by cases, which is what lets the sum be taken over
   the whole range;
4. `k^{−2σ} = x.1^{−2σ}·x.2^{−2σ}` on the antidiagonal (`Real.rpow_natCast`, `Real.rpow_add` on the product), so the
   double sum factorises; the pairs `(d,e)` with `de ≤ M²` that lie outside `[1,M]²` contribute zero by the support
   hypotheses, and all terms are nonnegative, so `Finset.sum_le_sum_of_subset_of_nonneg` finishes against the product
   of the two single sums.  `RHTower/DirichletSummatorySwap.lean` performs the same sigma-set reindexing for the
   summatory function and is the model for step 4.

With this the first moment of the product `L(a)L(b)` is explicit, and the analytic half of the Granville–Harper–
Soundararajan chain is complete with no estimate left unproved.

## The masses of a convolution — the last estimate, and an easier route than specified

`RHTower/Sieve/ConvolutionMasses.lean` (green, axiom-clean, wired).

* `sum_norm_convolution_mul_rpow_le` — the damped `ℓ¹` mass is submultiplicative:
  `∑_{k ≤ M²} ‖(a ⍟ b)(k)‖k^{−σ} ≤ (∑_d ‖a_d‖d^{−σ})(∑_e ‖b_e‖e^{−σ})`.  `Finset.sum_fiberwise_of_maps_to` groups the
  product set `[1,M]²` by the value of the product; each fibre dominates the corresponding coefficient because a
  nonzero antidiagonal term has both factors in the supports (`Finset.sum_filter_ne_zero` to drop the rest).
* `sum_sq_le_sq_sum_of_nonneg`, `sum_normSq_convolution_le` — a sum of squares is at most the square of the sum, so
  the `ℓ²` mass of the convolution is at most the square of that product.

**This replaces the estimate specified last round, and is both easier and sharper here.**  The specification called for
`4·(ℓ² mass)(ℓ² mass)` via a divisor-count case analysis; the `ℓ¹` route needs no case analysis, and for prime weights
with logarithmic coefficients it is the better bound: `(∑_p log p·p^{−σ})² ≍ (log N)²` against `4·cap(2σ)² ≍ (log N)⁴`
at `σ = 1 + 1/log N`.  The sharper-looking route was the worse one.

**The analytic half is now complete with no estimate unproved.**  For the product of the two prime polynomials,

`∫_{|y| ≤ nΔ} ‖L(a,σ+iy)L(b,σ+iy)‖ dy
    ≤ 2Δ·√(n·((2n+1)Δ + 4M²(1+log M²))(1/Δ + 2 log M²)·((ℓ¹a)(ℓ¹b))²)`,

every factor explicit.  What remains is the parameter choice — and the `ℓ¹` masses of the two weights are Mertens
sums, `∑_p log p·p^{−σ}`, which the corpus's Mertens layer bounds.

## The first moment of the product — the analytic half, closed

`RHTower/Sieve/ProductFirstMoment.lean` (green, axiom-clean, wired).

* `LSeriesSummable_of_support` — a finitely supported series is summable at **every** point
  (`summable_of_ne_finset_zero`), so `LSeries_convolution'` applies with no half-plane restriction;
* `integral_norm_LSeries_mul_le_largeValues` :

  `∫_{|y| ≤ nΔ} ‖L(a,σ+iy)L(b,σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M²(1+log M²))(1/Δ + 2 log M²)·((ℓ¹a)(ℓ¹b))²)`.

**The analytic half of the Granville–Harper–Soundararajan chain is closed.**  Every factor on the right is explicit in
`n, Δ, M, σ` and the two `ℓ¹` masses; no Cauchy–Schwarz splitting, no window, no measure, and no trivial size of any
factor appears.  Applied to the two prime weights, with `L(f)` bounded by its Euler product and the kernel by its
uniform size, the Perron integral is bounded by

`(Euler)·(kernel)·2Δ·√(n·(…)·((ℓ¹a)(ℓ¹b))²)`,

and the `ℓ¹` masses are Mertens sums `∑_p log p·p^{−σ}` (times `1/log 2` for the outer weight).

The remaining work is arithmetic in a single expression: choose `Δ`, `n` (equivalently the height `T = nΔ`), `σ`, `H`
and `N₀ = M`, and bound the two Mertens sums.  Every device the choice needs is in the corpus, and the shape now has
no term in which a trivial size multiplies a length — the property whose absence capped each of the three earlier
architectures.

## The `ℓ¹` masses: a bare geometric series

`RHTower/Sieve/PrimeLogL1Mass.lean` (green, axiom-clean, wired).

`sum_prime_log_rpow_neg_le` :

`∑_{p ≤ N} log p·p^{−w} ≤ 2 log 4·(1 − 2^{1−w})⁻¹`,   `w > 1`, uniformly in `N`.

Same dyadic architecture as the squared-logarithm cap, but **simpler**: a single power of the logarithm is absorbed by
Chebyshev's `θ` itself, so no polynomial factor in the block index survives and the block sum is a bare geometric
series `∑_j r^j = (1−r)⁻¹` with `r = 2^{1−w}`.  The squared cap needed `∑_j (j+1)r^j`.

At `w = σ = 1 + 1/log N` this is `≍ log N/log 2`, so each prime weight's `ℓ¹` mass is `O(log N)` — and the product of
the two, squared, is `O((log N)⁴)`, which is the mass that enters the first moment of the product.

**Every arithmetic input of the route is now proved.**  The chain, end to end:

`‖∑_{n ≤ N} f(n)‖·log N ≤ (recursion errors, O(N log log N))
    + (smoothing error, (H+1)(log⌊N+H⌋)⁴/(log 2)³)
    + (1/2π)·(Euler)·(kernel)·2Δ·√(n·((2n+1)Δ + 4M²(1+log M²))(1/Δ + 2 log M²)·((ℓ¹a)(ℓ¹b))²)`

with every quantity a named theorem.  The remaining step is the choice of `Δ, n, σ, H, M` — arithmetic in one
expression, with no device or estimate outstanding.

## Accounting first, this time: the uniform kernel bound is the wrong one, and `j = 0` is the right one

Following the lesson of the three earlier caps, the balance was computed *before* building anything on the assembled
first moment.  It rules out the kernel bound the truncated route uses.

With `Δ = 1/log N`, `M = N`, `T = nΔ`, `σ = 1 + 1/log N`, and the `ℓ¹` masses `O(log N)`:

`√(n·((2n+1)Δ + 4M²(1+log M²))(1/Δ + 2 log M²)·((ℓ¹a)(ℓ¹b))²) ≍ N√T·(log N)³`,

because the mean-value theorem's own `4M²(1 + log M²) ≍ N² log N` contributes `N` after the square root.  Multiplied
by the uniform kernel bound `Wsup ≍ N` this gives `≍ N²√T(log N)³` — catastrophically worse than `N log N`.

**The diagnosis.**  `|W| ≤ (N+H)^σ/σ` is the kernel's size *near `t = 0`*; using it across `[−T, T]` discards the
decay, and the first moment grows with `T`, so the product grows with `T` too.  The `T`-tension of the earlier
accountings reappears in the first-moment form, and no choice of `T` escapes it: small `T` fails the tail, large `T`
fails the main term.

**The resolution, and it is in the corpus.**  `exists_bound_mellin_smoothWeight` is stated for every `j`:

`‖s‖·∏_{i<j}‖s+1+i‖·‖mellin(w)(s)‖ ≤ C_j/H^{j+1}·(N+H+1)^{σmax+j}·|N+H+1−N/2|`.

* `j = 1` — quadratic decay, constant `≍ N^σ(N/H)²`: the penalty that capped the Lorentzian route;
* the uniform bound — no decay, and the first moment then grows linearly in `T`: the cap above;
* **`j = 0` — first-order decay `|W| ≤ N^σ(N/H)/|s|`, constant `≍ N^σ(N/H)`**.

At `H = N/(log N)^k` the cost of `j = 0` is `(N/H) = (log N)^k` — a logarithmic factor, not a power — and the
resulting integral `∫_{|t| ≤ T} |D(σ+it)|/|t| dt` grows only *logarithmically* in `T`, since the first moment over a
dyadic block `|t| ≍ 2^m` is divided by `2^m`.  That is the shape in which the height is finally free.

So the next brick is the dyadic-in-height decomposition of the vertical integral against the `1/|t|` kernel, with the
first moment applied on each block and the uniform bound used only on `|t| ≤ 1`.  Recorded before building: the
accounting says `j = 0` and dyadic blocks in `t`, not `j = 1` and not a uniform bound.

## The vertical integral against a first-order kernel is bounded independently of the height

`formal/GaloisForLFunctions/HTGeometry/VerticalKernelDyadicSplit.lean`:

- `integral_mul_kernel_le_sum_dyadic` — for `F ≥ 0` and a kernel `G t ≤ C/t` on `[t₀,∞)`,
  `∫_{t₀}^{t₀2^M} F·G ≤ ∑_{m<M} (C/(t₀2^m))·∫_{block m} F`, where block `m` is `[t₀2^m, t₀2^{m+1}]`.
- `dyadic_sqrt_term_eq` — if the block moment is `K·√(height)`, the `m`-th term equals
  `(C K √2/√t₀)·(√2/2)^m`.
- `integral_mul_kernel_le_of_sqrt_block_moment` — hence the whole integral is at most
  `C·K·√2·(1−√2/2)⁻¹/√t₀`, with no dependence on `M` and therefore none on the height of the range.
- `exists_bound_mellin_smoothWeight_first_order`, `exists_bound_mellin_smoothWeight_height` — the
  `j = 0` case of the corpus Mellin bound: `‖W(σ+iy)‖ ≤ C/√(σ²+y²) ≤ C/y`, constant `≍ N^σ(N/H)`.

The device is stated for a general nonnegative `F`, so it is the same lemma for a first moment of a
Dirichlet polynomial, of a full series, or of any product of them.  With `t₀ = 2Δ` every dyadic block
has length exactly `2·2^m·Δ`, i.e. exactly `2^m` cells of the cell-maximum discretisation, so the
shifted first moment applies to each block with `n = 2^m`.

Square-root growth of the block moment is the shape a mean-value estimate produces, and it is exactly
half the growth of the length: a kernel decaying like `1/t` therefore beats it by a factor `√2/2` per
block.  This is the mechanism that removes the `√T` growth diagnosed in the uniform-kernel accounting.

## Perron's lemma: the sharp cutoff without a smoothing penalty

`formal/GaloisForLFunctions/RHTower/Sieve/PerronLemma.lean`:

- `perronVertical σ T y = (1/2π)∫_{−T}^{T} y^{σ+it}/(σ+it) dt`.
- `norm_perronVertical_sub_one_le` — for `y > 1`, `σ > 0`, `T > 0`: `‖perronVertical σ T y − 1‖ ≤ y^σ/(πT log y)`.
- `norm_perronVertical_le` — for `0 < y < 1`: `‖perronVertical σ T y‖ ≤ y^σ/(πT|log y|)`.

The assembly the corpus was already carrying the parts for: `PerronKernelResidue.rectangleIntegral'_cpow_div_eq_one`
supplies the residue `1` at the origin, `PerronKernelSegments` the two horizontal edges and the far vertical
edge, and the shift `A → ∞` is taken along the integers with `ge_of_tendsto`.

Why this matters for the accounting, and why it changes the route.  The smoothed kernel's constant is
`N^σ·(N/H)`, and the window error `H(log N)^4` forces `H ≪ N/(log N)^5`, so the smoothing costs a factor
`(log N)^5` in every term of the vertical integral.  The sharp-cutoff kernel `x^s/s` has constant `x^σ`
and no window at all: its whole cost is the factor `1/(T|log(x/n)|)`, and at `T = N` the total truncation
error over a coefficient sequence of polylogarithmic size is `∑_n ‖c_n‖(x/n)^σ/(πT|log(x/n)|) ≍ (log N)^5`
— an additive polylog, not a multiplicative one.  Every smooth-weight device pays the multiplicative
`(N/H)`, including a Cesàro/`x^s/(s(s+1))` kernel followed by differencing, because the price is the
near-diagonal mass of the weight; only the sharp cutoff avoids it, and it avoids it because `|log(x/n)| ≥ c/N`
off the diagonal makes the harmonic sum converge to `O(log N)`.

Accounting recorded before the next brick: with the sharp kernel, first-order decay `1/|s|` and the dyadic
height split, the analytic term is `x^σ·sup|F|·(∑_m 2^{−m}·block moment)`.  Against the corpus's
prime-sieve mean square — whose leading term `∑_n n‖a_n n^{−σ}‖²/log Y` is *independent of `T`*
(`TruncatedPrimeSieveMeanSquare`, `TruncatedBlockMeanSquare`) — a block moment is
`√(length)·√(mean square) ≍ K√(height)`, exactly the hypothesis of
`integral_mul_kernel_le_of_sqrt_block_moment`.  The remaining loss is a single `log T` from using a
pointwise bound on the third factor on every block; that is what the large-values estimate is for.
