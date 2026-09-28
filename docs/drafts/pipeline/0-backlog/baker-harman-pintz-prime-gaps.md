# Baker–Harman–Pintz: primes in [x, x + x^{0.525}] (formalization programme)

- **ID:** `PRIME-GAPS-BHP-0525`
- **Stage:** 0-backlog (scoped 2026-09-28; nothing built yet)
- **Consumer:** `PrimeDeletionGreedyConstruction.greedy_chebyshev_expansion`.
  - It takes any window bound `θ(y+L)−θ(y) ≥ (L−(y+L)^α)/c`.
  - With the corpus exponent (α > 0.701299) it already covers κ ∈ (½, 0.5974).
  - BHP (α = 0.525+ε) would extend it to κ < 0.95.
  - A count-form Huxley bound (7/12+ε) would extend it to κ < 5/6.
- **Target statement (count form, as in BHP p.562):** for large x, π(x + x^{0.525}) − π(x) ≥ (9/100)·x^{0.525}/log x. Chaining windows (as in `ShortIntervalThetaEveryWindow`) then gives the consumer's hypothesis.

## Proof map (BHP, Proc. LMS 83 (2001) 532–562)
| # | Item | Input | Corpus status |
|---|---|---|---|
| 1 | Lemma 1: Heath-Brown identity reduction of type-(2.4) polynomials | HB 1982 | `Sieve/HeathBrownIdentity` (owned) |
| 2 | Lemma 2: Watt's theorem ∫|M|²|K|⁴ ≪ U^{1+ε}(1+M²U^{−1/2}) | Watt 1995 ⇐ Deshouillers–Iwaniec (Kuznetsov formula, spectral large sieve for Kloosterman sums) + Titchmarsh 4.13 reflection | NOT owned (MT programme uses "mtWatt" envelopes only on covered ranges) |
| 3 | Lemmas 3–5: mean-value bounds for MN₁N₂K | mean value theorem; BHP97 Lemma 5 sup-norm ‖M‖∞ ≪ M^{1/2}L^{−A} for M ≥ x^ε on [T₀,T] | MVT owned (`Sieve/DirichletMVT`); the sup-norm lemma needs the Vinogradov–Korobov zero-free region (NOT owned) |
| 4 | Lemma 6: mean value ⇒ short-interval asymptotic | Perron | partly owned (`HeathBrownDyadicShortIntervalPerron`) |
| 5 | Lemma 7: Rankin tail bound | Mertens | easy |
| 6 | Lemma 8: fundamental-lemma asymptotic (2.2) | HB 1988 Lemma 15 | to build |
| 7 | Lemma 9: large-values variant of BHP97 Thm 4 (g = 5) | Huxley–Halász large values | Huxley large values owned (`Sieve/Huxley*`) |
| 8 | Lemmas 10–11: combinatorics of exponents | — | easy |
| 9 | Lemmas 12–13: Type I/II asymptotic formulae (1.3) with ν(α) | 1–8 | to build |
| 10 | Lemmas 14–17: two-dimensional sieve | 2, MVT | to build |
| 11 | Lemma 18: large-values case analysis (region where (5.1) holds) | BHP97 Lemma 1 | to build |
| 12 | §6: Buchstab decomposition, rôle reversals, regions A–F, certified bounds on 2–6-dimensional integrals of ω (losses 0.3, 0.06, 0.21, 0.34; margin 0.09) | numerics | Harman/Buchstab framework partly owned (`Sieve/HarmanMinorant`, `BuchstabIdentity`); certified multi-dimensional integration NOT owned |

## Critical path
1. Watt's theorem (DI/Kuznetsov). This is the deepest input.
2. Vinogradov–Korobov zero-free region: exponential sums for ζ near σ = 1.
3. Certified numerics of §6.

Items 5, 8 and parts of 4, 6, 9 are routine given the corpus sieve library.

## Intermediate milestones
- **M1: Huxley 7/12 (count form).** Huxley zero-density plugged into the corpus Ingham detector tower. It reuses the `Sieve/Huxley*` large values and must reproduce the tower's near-σ=1 handling. It extends κ to < 5/6.
- **M2: VK zero-free region.** This is standalone, and it is needed by item 3 and useful across the corpus.
- **M3: Watt's theorem.**
- **M4: BHP.**
