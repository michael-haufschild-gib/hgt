# Missed opportunities: exact outstanding statements

- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-0911/fable.md`, §11.
- **Scope:** solve and unconditionally formalize every mathematical task in §11;
  existing criteria alone do not discharge their analytic inputs.

## Required results

| Item | Required result | Status |
|---|---|---|
| 11.6 | Width and two-sided log-square prime-window criteria; signed-deletion proof | Open; one-sided RH criterion exists |
| 11.6 | Quasi-RH ∨ AAL; quasi-RH iff tail abscissa < 1; consequences under ¬AAL | First two checked in `quasi-rh-is-a-tail-law.md`; heavy-return and Mertens consequences open |
| 11.6 | Exact simple near-line census alternatives at 70%, 75%, 80% | Complete: `near-line-census-at-seventy-seventy-five-eighty-percent.md`; existing 70% and 75%, new 80%, all audited |
| 11.1 | Halving descent connected to one-eigenform detection; precise remaining Shimura nonvanishing; static 2/3 boundary | Open assembly; halving descent and diagonal factorization exist separately |
| 11.2 | Precise fixed-part/isolation obstruction for twists and covers, with positive survivor | Scope and strongest justified theorem require audit |
| 11.3 | Compact-surface Selberg calibration with finitely many exceptional real zeros | Open; distinguish nontrivial zeros from other Selberg zeros |
| 11.4 | Short-interval multiplicative cancellation and averaged correlations | Open; published statements and proof dependencies require audit |
| 11.4 | Carlitz–Goss RH | Open; exact field and zeta statement require audit |
| 11.4 | Bilinear mollified-moment bounds past length T^(1/2) | Open; precise theorem and range require audit |
| 11.5 | Audit recommended route closures, retain exact positive survivors | Open; recommendations are not mathematical proofs |

## Existing anchors

- `SurfaceOfSpecZ/ScaleLocality/PrimeLogSquareWindows.lean`:
  `riemannHypothesis_iff_prime_logSquare_windows`.
- `RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean`:
  `critical_proportion_or_simple_offLine_near_line`.
- `RHTower/Zeta23SimpleOffLineNearLine.lean`:
  `three_quarters_or_simple_offLine_near_line`.
- `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean`:
  `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`.

No item is complete until its exact statement has a dependency-closed Lean proof,
direct `lake --old env lean` audit, and transitive axiom audit.

## Published inputs: precise targets

- [Matomäki–Radziwiłł, Theorem 1](https://arxiv.org/html/1501.04585):
  uniform comparison of short and long averages of real multiplicative
  functions bounded by one, for `2 ≤ h ≤ X`, with an explicit exceptional-set
  bound. The existing `matomaki-radziwill-moebius-short-interval-mean-square.md`
  proves a different, balanced-fibre statistic at
  `h = exp((log x)^(99/100))`; it explicitly leaves ordinary integer-start
  intervals open. This does not discharge §11.4.
- [Sheats](https://arxiv.org/abs/math/9801158): Goss zeta for `𝔽_q[T]`,
  for every prime power `q`; not the complex Hasse–Weil zeta of a curve.
- [Bettin–Chandee–Radziwiłł, Theorem 1](https://www.math.mcgill.ca/radziwill/BCR.pdf):
  the smoothed twisted second moment for arbitrary divisor-subpower
  coefficients of length `N = T^θ`, `θ < 17/33`, with error
  `O(T^(3/20+ε) N^(33/20) + T^(1/3+ε))`. Its Kloosterman-fraction estimate
  must be proved, not supplied as an assumption. Applicability to the fourth
  Gram moment is a further theorem, not a consequence of the shared word “bilinear”.
