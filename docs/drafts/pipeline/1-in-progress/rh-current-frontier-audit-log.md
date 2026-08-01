# RH Current-Frontier Corpus Audit

- **ID:** rh-current-frontier-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** user-requested exhaustive audit of `HTGeometry`, `HilbertMetric`, and `RHTower`
- **Statement:** Produce a declaration-grounded, literature-checked map of every identified RH proof/disproof route, dead route, obstacle, and unresolved leap hypothesis in the current corpus.

## Goal

Write a review paper whose route claims are traceable to exact Lean declarations and whose dead-end and open-core claims are reconciled against pipeline records and current primary literature.

## Gates

- [x] 0 → 1 in-progress: scope fixed; corpus-first method fixed; read-only area audits assigned; audit log opened
- [ ] Corpus inventory: all three umbrella import closures accounted for
- [ ] Declaration audit: every RH-facing endpoint classified as unconditional, equivalence, conditional reduction, obstruction, or interface
- [ ] Route audit: chains, endpoints, open cores, and circularity risks reconciled across areas
- [ ] Failed-route audit: all route-relevant failed cards checked for exact obstruction and positive survivor
- [ ] Literature audit: unresolved leap claims checked against primary sources
- [ ] Completeness audit: hostile reread finds no omitted or misclassified route
- [ ] Paper complete: standalone review with theorem-level traceability and explicit limitations

## Audit invariants

- Lean declarations and their explicit hypotheses determine corpus truth.
- Names, docstrings, pipeline stage, and narrative prose never override theorem signatures.
- Explicit hypotheses are not counted as established analytic inputs.
- Equivalences to RH are route endpoints, not RH proofs.
- Formal obstruction theorems kill only statements matching their exact quantifiers and hypotheses.
- Existing dirty worktree changes remain untouched.
- Read-only agents may inspect but not edit repository files.

## Log

- 2026-08-01 — Session initialized: read project instructions, `docs/meta/scientific-method.md`, formal guide, Serena project memories, `hgt-fields-medalist`, and `scientific-writing` workflows.
- 2026-08-01 — Git audit found pre-existing modified, deleted, and untracked research/Lean files. Scope restricted to new audit artifacts; working tree will not be normalized.
- 2026-08-01 — Initial inventory found three very large theorem areas. Full audit method fixed: umbrella import closure → generated declaration index → exact source signatures → pipeline and literature reconciliation.
- 2026-08-01 — Transitive import-graph audit (source, not generated prose) found complete area closure: HTGeometry 3,408/3,408 leaves; HilbertMetric 52/52; RHTower 4,029/4,029. Direct umbrella imports are smaller because many leaves enter transitively. Source volume: 679,119 + 19,737 + 1,000,910 leaf lines.
- 2026-08-01 — Generated indexes are not fully synchronized with current source: `LEAN_OVERVIEW.md` reports HTGeometry 3,404 and RHTower 4,027 modules, versus source closure 3,408 and 4,029. Treat indexes as discovery aids only; exact source remains authoritative.
- 2026-08-01 — Missing mandated `docs/support-extraction-log.md`; only a historical validation card refers to it. This is a corpus-completeness limitation requiring explicit paper disclosure.
- 2026-08-01 — Verified architecture exception: `HilbertMetric/FourthCurvatureMixture.lean:1` imports `HTGeometry.HalfLineSteinRobertson`, contrary to formal guide's source-independence rule. Mathematical use must be classified by actual hypotheses, not advertised area boundary.
