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
