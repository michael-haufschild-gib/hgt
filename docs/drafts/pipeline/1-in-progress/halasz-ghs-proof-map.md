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
