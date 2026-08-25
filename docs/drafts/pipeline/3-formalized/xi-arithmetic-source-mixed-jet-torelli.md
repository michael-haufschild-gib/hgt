# Arithmetic source mixed-jet Torelli

- **ID:** XI-SOURCE-MIXED-JET-TORELLI
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/rh-lean-corpus-study-log.md`
- **Statement:** Finite prime--arch contour moments reconstruct exact multiset of signed mixed Real defects; one defect vanishes exactly on critical line.

## Goal

Determine whether missing RH datum is absent from arithmetic source or merely lacks source-native annihilation law.

## Gates

- [x] 0 → 1  in-progress: exact composition identified
- [x] 1 → 2  fully-proven: power-sum Torelli composed with mixed-jet identity
- [x] 2 → 3  formalized: `xiArithmeticSourceRectangleMoment_mixedJet_torelli`; targeted build and axiom audit pass
- [ ] 3 → 4  publication-ready: no external novelty claim

## Approach

Map arithmetic source-moment reconstruction through `w ↦ -2 Im(w²)` and identify result with source-marked mixed Xi jet.

## No-go closure

- **Exact killing theorem/mechanism:** “Source lacks transverse defect information” is false: Torelli reconstructs full signed defect multiset.
- **Strongest positive survivor:** Missing producer is arithmetic law forcing reconstructed defect multiset to be zero, not further divisor reconstruction.
- **New insight:** Unorderedness does not obstruct RH test because “every defect is zero” is permutation invariant.
- **Status:** dependency-closed; formalized in `XiArithmeticSourceMixedJetTorelli.lean`.

## Log

- 2026-08-25 — paper proof, Lean proof, targeted build, axiom audit complete
