# Lean-verified quantum-recurrence manuscript

- **ID:** lean-verified-quantum-recurrence-manuscript
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `geometry-complexity-quantum-recurrence/main.tex` and imported appendices
- **Statement:** Every mathematical result asserted by the manuscript is an unconditional consequence of an exact, axiom-clean Lean declaration imported through the project theorem surface.

## Goal

Replace the mixed paper/bridge/literature theorem surface with a proof-carrying manuscript. Every
numbered theorem, corollary, lemma, displayed law presented as a result, and prose-level mathematical
conclusion must have an exact Lean certificate. A statement with an unformalized premise, bridge, or
composition is excluded from the manuscript until that premise and composition are proved in Lean.

## Gates

- [x] 0 → 1  in-progress: requirement is well posed; current `claim-trace.md` identifies mixed-status claims
- [ ] 1 → 2  fully-proven: manuscript theorem ledger contains no status except `[LEAN-PROVED]`
- [ ] 2 → 3  formalized: exact declaration map complete, target modules build, `#print axioms` clean, formal lint passes
- [ ] 3 → 4  publication-ready: standalone PDF states only mapped results and includes Lean certificate appendix

## Approach

1. Inventory every result-bearing manuscript sentence and environment.
2. Match it to the exact Lean declaration, including every premise used by a composition.
3. Formalize small missing compositions whose dependencies already exist.
4. Remove or demote all remaining paper-only, bridge-only, or literature-only mathematical claims.
5. Rewrite scope and universality language to describe the exact formal domain, not an aspirational one.
6. Verify narrow modules, umbrella reachability, axioms, formal lint, LaTeX build, and rendered PDF.

## Open core at creation

- Haar-on-orbit-hull occupation and finite target-union capacity are marked `[BRIDGE]`.
- Heterogeneous connected-network thermodynamic rate is only paper-proved.
- Several static-local complexity compositions and computable-witness claims are only paper-proved.
- Autonomous reflection, Markovian recovery, and onset/dimension independence are only paper-proved.
- Exact full-channel recurrence rigidity is only literature/bridge-backed.
- Imported appendices require declaration-level matching, not family-level citations.

## Log

- 2026-08-14 — created in Stage 1 after user imposed exact unconditional Lean coverage as publication boundary.
