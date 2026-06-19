# Task Completion

- For Lean/formal changes: run `cd formal && lake build`; then `bash scripts/check_axioms.sh` from root. Report both outcomes.
- For Lean theorem additions: ensure theorem is imported by `formal/GaloisForLFunctions.lean` if it is part of the library/audit surface, and add it to `scripts/check_axioms.sh` when it becomes a ledgered theorem.
- For conjecture statements in Lean: use `def ... : Prop`; do not assert conjectures as axioms/theorems.
- For research pipeline changes: move card to correct stage, update its `Stage:` line, add a dated `## Log` line, and keep `docs/drafts/door/00-status.md` plus relevant bucket/index entries consistent.
- For computations: archive inputs/results under `computations/` and summarize only durable results in the appropriate card/status entry.
- Always inspect `git status --short` before edits and preserve unrelated dirty work. Existing uncommitted docs/backlog cards may belong to the user or another agent.