# The GHS route to sharp Halász, and Gallagher's lemma in the useful direction (2026-08-07)

## The proof map is now known and written down

`docs/drafts/pipeline/1-in-progress/halasz-ghs-proof-map.md` records the full skeleton of
Granville–Harper–Soundararajan, arXiv:1706.03755 (sharp Halász, "more intuitive proof"), with the
companion arXiv:1706.03749. Four steps: (1) the log recursion — DONE in the corpus as
`RHTower.Sieve.norm_sum_Icc_mul_log_sub_sum_primes_le'`; (2) a second application giving a triple
convolution; (3) a dyadic partition of the prime range into `P_k = (x^{1−e^{1−k}}, x^{1−e^{−k}}]` —
this is where Halász's `1+M` prefactor comes from, it is the *count of scales*; (4) truncated Perron +
Cauchy–Schwarz with a prime-supported mean square.

Their **Lemma 1** is the input my earlier no-go 3 named as missing:
`∫_{−T}^T |∑_{T²≤n≤x} a_n Λ(n) n^{−1−it}|² dt ≪ ∑ |a_n|² Λ(n)/n`.
GHS state explicitly that the standard Dirichlet mean value theorem cannot give this — it yields
`Λ(n)²`, not `Λ(n)`. The proof is a smooth weight plus Brun–Titchmarsh in short intervals.

## Built: Gallagher's lemma in the mean-value direction

`RHTower/Sieve/GallagherReverse.lean` (green, axiom-clean, wired):
`∫_{Icc (-W) W} ‖logPoly a s w‖² ≤ (5/(4δ²)) ∫_ℝ ‖logWindowSum a s δ u‖²` whenever `2πδW ≤ 1`.

The corpus's `gallagher_identity` is an *equality*, so the only missing piece was a lower bound for the
Fejér weight on the central range: `le_fejerWeightAt_re` (`≥ (4/5)T` for `|TL| ≤ 1`) and
`le_fourier_triC_re` (`≥ (4/5)δ²` for `|2πδw| ≤ 1`), both from `2 − 2cos θ ≥ (4/5)θ²`
(mathlib `Real.cos_bound`). Do not rebuild the Fejér/triangular layer: `TriangularKernel`,
`TriangularInversion`, `TriangularIntegralForm`, `FejerSymmBound`, `FejerBounds`, `GallagherLemma`,
`LogWindowKernel` already own the transform, its closed form `2(1−cos TL)/(TL²)`, nonnegativity, the
cap and the decay.

Next brick: GHS Lemma 1 = this + Cauchy–Schwarz per window + the corpus's Brun–Titchmarsh count
(`Sieve/BrunTitchmarsh`, `Sieve/PrimeWindowUpper.card_primes_Ioc_le_explicit`).

## Update: the arithmetic side of GHS Lemma 1 is built

`RHTower/Sieve/GallagherAlmostDiagonal.lean` — `logNeighbourCount s δ n = #{m ∈ s : |log n − log m| < δ}`,
`integral_normSq_logWindowSum_le_count` (no hypothesis on δ at all), and
`integral_Icc_normSq_logPoly_le_count` (the mean value theorem with the count as its only arithmetic).

`RHTower/Sieve/PrimeLogWindowCount.lean` — `logNeighbourCount_le_sieve` discharges the count for a prime
support using the corpus's `RHTower.Sieve.card_prime_Ioc_le` (Sieve/PrimeInterval; the clean
Brun–Titchmarsh shape with `selbergFibreError z Y + z`), and
`integral_Icc_normSq_logPoly_le_prime_sieve` assembles the prime-supported mean value theorem.

The δ cancels: Gallagher contributes `5/(4δ)` and the window length contributes `e^δ − e^{−δ} ≍ 2δ`.
With `log Y ≍ (log p)/3` the per-prime weight is `≍ (log p)/p` — GHS Lemma 1's `Λ(n)/n`, not `Λ(n)²/n`.
