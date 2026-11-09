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
| 11.6 | Exact simple near-line census alternatives at 70%, 75%, 80% | General theorem and 70% already exist; remaining specializations open |
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
- `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean`:
  `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`.

No item is complete until its exact statement has a dependency-closed Lean proof,
direct `lake --old env lean` audit, and transitive axiom audit.
