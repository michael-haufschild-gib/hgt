# RH Workspace — Working Rules


## Mission
Do science toward publications/hgt.

## Session init
1. Read fully line by line: docs/drafts/00-core-vision.md
2. Read fully line by line: docs/drafts/00-charter-wall-and-door.md
3. Read fully line by line: docs/drafts/door/00-index.md

## The pipeline (Kanban style)
Use docs/drafts/pipeline/_card-template.md
1. Backlog: docs/drafts/pipeline/0-backlog
2. In progress: docs/drafts/pipeline/1-in-progress
3. Fully proven (on paper): docs/drafts/pipeline/2-fully-proven
4. Formalized (in lean 4): docs/drafts/pipeline/3-formalized
5. Fully written pre-prints: docs/drafts/pipeline/4-publication-ready

## Workmode
1. Always work in the pipeline when advancing scientific research: docs/drafts/pipeline
2. Computations are to avoid. If run their results must be archived in computations/.
3. Keep your own working log in logs/. Do not pollute the pipeline with logging that adds nothing to the research.
4. Keep updates in the pipeline concise, clear to read, no history or folklore, just factual and complete.
5. Updates to docs/drafts/door/00-index.md and docs/drafts/door/00-status.md must be filed as an informal ticket in docs/drafts/pipeline/library-backlog/ - an agent will handle the updates to prevent edit races.

## Lean discipline
- Verify names against THIS toolchain by scratch file
  (`lake env lean /tmp/x.lean` with `have := @Name` lines) — never trust
  recalled mathlib names (2025-11 Sorted-refactor lesson).
- `#print axioms` via /tmp scratch file, never by editing the tree.
- The tree carries exactly the intended sorries: currently ZERO.
- Numerically pre-certify formalization plans (mpmath) before writing Lean.

## Append-Only File Edits
- For append-only operations, append at EOF with a shell here-doc (`cat >> file <<'EOF' ... EOF`) or an equivalent append primitive.
- Do not use `apply_patch` for append-only operations.
- Use targeted edit tools only for inserting, replacing, moving, or deleting existing content.
