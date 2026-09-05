## The research pipeline (Kanban)
Card template: docs/drafts/pipeline/_card-template.md
1. Backlog → docs/drafts/pipeline/0-backlog
2. In progress → docs/drafts/pipeline/1-in-progress
3. Fully proven on paper → docs/drafts/pipeline/2-fully-proven
4. Formalised in Lean 4 → docs/drafts/pipeline/3-formalized
5. Publication-ready pre-prints → docs/drafts/pipeline/4-publication-ready
6. Failed/retired → docs/drafts/pipeline/5-failed

## Check prior research before any new topic
- Current ledger of the major routes and route candidates: docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md
- Always use `scripts/formal_tools.py research "<query>"` to search in the lean corpus.

## Lean discipline
- Verify every mathlib name against THIS toolchain in a /tmp scratch file
  (`lake env lean /tmp/x.lean` with `have := @Name` lines). Never trust a recalled name.
- `#print axioms` via a /tmp scratch file, never by editing the tree.
- The formal lint gate is authoritative: run `scripts/formal_tools.py lint`; currently no active
  `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is allowed.
- Always use `scripts/formal_tools.py research "<query>"` for reusable lean code and avoiding duplicating existing work.

## No-go closure discipline
- A no-go is not finished when only its negative statement is proved.
- Before retiring a route, extract and audit the strongest non-trivial positive statement exposed by
  the obstruction: a sharp boundary, classification, rigidity law, exact decomposition, replacement
  hypothesis, or new invariant.
- Record the exact new insight and the survivor's paper-proof and Lean status on the failed-route
  card.
- Once the positive survivor has a dependency-closed paper proof, formalise that exact theorem in
  Lean. Treat stronger statements forced or exposed by Lean as new conjectures and send them back
  through the paper and novelty audits.
- If no positive survivor remains after a serious second pass, record what was tried and label it
  `NO POSITIVE SALVAGE FOUND`.

## Session & compaction management
- Long tasks survive compaction via files, not memory. Before a hard problem, write the card in the
  pipeline; check progress back to it.
- Do not stop a task early over token budget.
