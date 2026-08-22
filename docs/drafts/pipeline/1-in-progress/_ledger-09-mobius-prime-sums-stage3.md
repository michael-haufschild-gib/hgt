# Ledger: stage-3 sweep of `09-mobius-prime-sums` (13 cards)

- **Opened:** 2026-08-22
- **Goal:** every card in
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/`
  carries an unconditional Lean certificate of its proved content, then moves to
  `docs/drafts/pipeline/3-formalized/`.
- **Rules:** unconditional Lean only (no hypotheses, no axioms, no sorry). Search corpus before
  building. `lake env lean <file>` for iteration; `lake build <module>` only for the final audit.

## Card status

| # | Card | Lean target | State |
|---|---|---|---|
| 1 | prime-square-mobius-fourier-complementary-record-law | §2–§6 finite Fourier / CRT | IN PROGRESS |
| 2 | localized-half-density-mobius-curvature-semiprime-fibre-law | (3)–(4), (14)–(15), (18)–(20), (23) | TODO |
| 3 | shifted-euler-error-floor-mobius-tail-coupling | Thm A (3), Thm B (8)–(9) | TODO |
| 4 | friable-moment-ladder-finite-dim | Thm A, Thm B | TODO |
| 5 | coupled-floor-mobius-complementary-shift-incidence-law | (8), (15), (18) | TODO |
| 6 | mertens-corona-shift-conormal | (5),(9),(10),(13),(15),(19) | TODO |
| 7 | baez-duarte-critical-mobius-beta-wavelet-law | (1)–(2),(5),(8)–(10),(7c)–(7f),(14c) | TODO |
| 8 | mertens-logarithmic-corona-differential-tower | (4),(7),(10),(13)–(15),(19)–(21),(27)–(29),(31) | TODO |
| 9 | kubalalika-unweighted-near-diagonal-tail | (1)–(5) incl. van der Corput | TODO |
| 10 | square-aperture-von-mangoldt-correlation-energy | reverse implication (Schoenfeld) | TODO |
| 11 | regular-variation-weighted-steinhaus-ldp | Gärtner–Ellis LDP + endpoints | TODO |
| 12 | kubalalika-parity-weighted-near-diagonal-tail | phase stability + parity reduction + tail | TODO |
| 13 | halasz-ghs-adaptive-coarea-completion | (H1)–(H2), Lemmas A–F, (MR1) | TODO |

## Corpus assets located (do not rebuild)

- `RHTower/PrimeSquareFourierStrata.lean` — `ZMod (p^2)` additive Fourier, valuation strata
  indicators, unnormalized compression entries, deformed occupation Gram.
- `HTGeometry/PrimeCollisionConvolution.lean` — two-prime collision orientation.
- `RHTower/SuzukiCoupledErrorCriticalDerivative.lean` — `suzukiShiftedCoefficient`, first jet.
- `RHTower/WeightedEulerCoefficientSpaces.lean`, `RHTower/MertensPrimeMeanReader.lean` —
  logarithmic Marcinkiewicz layer `M_log`, vanishing-tail layer `M_0`, Mertens mean coordinate.
- `RHTower/MertensPrimeWindowWeakConvergence.lean` — Mertens first theorem in prime form.
- `RHTower/MertensThirdTheorem.lean`, `RHTower/MertensSecondPrimeRecipSum.lean`.
- `RHTower/Sieve/SquarefreeDyadicDensity.lean` — squarefree dyadic density.
- `HTGeometry/SteinhausLaplaceProduct.lean` — Haar circle Laplace product.
- `RHTower/SqrtCarrierCertificate.lean` — `ζ(2z)⁻¹` square-dilated Möbius carrier.
- `RHTower/BaezDuarte*.lean` — BD distance / Gram / least squares (dilation form).

## Log

- 2026-08-22 — ledger opened; all 13 cards read; corpus audit started.
