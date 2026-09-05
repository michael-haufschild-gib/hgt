## The research pipeline (Kanban)
Card template: docs/drafts/pipeline/_card-template.md
1. Backlog → docs/drafts/pipeline/0-backlog
2. In progress → docs/drafts/pipeline/1-in-progress
3. Fully proven on paper → docs/drafts/pipeline/2-fully-proven
4. Formalised in Lean 4 → docs/drafts/pipeline/3-formalized
5. Publication-ready pre-prints → docs/drafts/pipeline/4-publication-ready
6. Failed/retired → docs/drafts/pipeline/5-failed

## Check prior research before any new topic or writing new lean code
- Current ledger of the major RH proof routes and route candidates: docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md (ignore if you are not working on RH)
- High level facts about things the RH proof must or can not be like: docs/drafts/pipeline/1-in-progress/universal-law-field/STATUS.md (ignore if not working on RH)
- Search: `scripts/formal_tools.py research "clock inverse"`. Spaces mean AND; `--any` means OR.
- Use inner quotes for phrases: `research '"critical line" zero'`. `--exact` disables prefix expansion.
- Default: 20 hits, at most 2 per module, plus 5 exploration hits matching the same query.
  Use `--per-module 0` to remove the cap, `--explore 0` to hide extras, `--offset 20` for the next page.
- Filter with `--module <substring>` or `--exclude-module <substring>`; `--json` gives structured results.
- Searches own-tree names, module names, full docstrings, and gap markers. Use `rg` for statements,
  proof bodies, mathlib, or pipeline text. `--no-refresh` searches the cached index without updating it.

## Lean discipline
- Verify every mathlib name against THIS toolchain in a /tmp scratch file
  (`lake env lean /tmp/x.lean` with `have := @Name` lines). Never trust a recalled name.
- `#print axioms` via a /tmp scratch file, never by editing the tree.
- The formal lint gate is authoritative: run `scripts/formal_tools.py lint`; currently no active
  `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is allowed.

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
