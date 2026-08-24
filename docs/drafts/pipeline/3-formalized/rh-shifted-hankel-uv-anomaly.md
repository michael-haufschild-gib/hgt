# Shifted-Hankel UV anomaly classification

- **ID:** RH-UV-ANOMALY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/rh-lean-corpus-study-log.md`
- **Statement:** False RH is exactly persistence of a shifted-Hankel defect above every eventually positive fixed cutoff; every fixed degree separately has finite exact outgoing source action.

## Goal

Formalize “off-line charge survives by escaping to unbounded resolution” as source-side theorem,
not metaphor or renamed open obligation.

## Gates

- [x] 0 → 1  in-progress: source-pure statement and dependency-closed proof identified
- [x] 1 → 2  fully-proven: combines fixed-cutoff far-right positivity, cofinal defect recession,
  and exact fixed-degree source-action integral law
- [x] 2 → 3  formalized: `xiShiftedHankelUVAnomaly_iff_not_riemannHypothesis` and
  `exists_fixedDegree_integrable_literalMassSourceAction_tail`; targeted build and axiom audit pass
- [ ] 3 → 4  publication-ready: novelty audit and standalone exposition

## Approach

Package simultaneous low-degree positivity and higher-degree failure as `XiShiftedHankelUVAnomaly`.
Prove equivalence with `¬ RiemannHypothesis`. Separately derive an unconditional mass threshold at
which each fixed positive degree has integrable full-tail source action equal to current flux.

## No-go closure

- **Exact killing theorem/mechanism:** Not applicable.
- **Strongest positive survivor:** Target theorem itself.
- **New insight:** Fixed-degree dissipation closes exactly; false-RH defect is exclusively a
  moving-degree completion anomaly.
- **Status:** Formalized in Lean; only standard axioms `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-08-24 — created directly in 1-in-progress after corpus synthesis and novelty search.
- 2026-08-24 — formalized anomaly equivalence and unconditional fixed-degree finite-action tail.
