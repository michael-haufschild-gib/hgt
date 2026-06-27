# Conventions

- Lean ledger discipline: no `sorry`, no new axioms; verify mathlib names in `/tmp` scratch files before using them.
- Keep append-only documentation updates as true appends, not patches. Use targeted edits for existing Lean code changes.
- Preserve unrelated dirty worktree changes; inspect before editing modified files.
- Böttcher files use theorem-rich small modules with descriptive docstrings and explicit hypotheses when analytic infrastructure is missing from mathlib.
- Formal docs are instruction-oriented: keep `formal/CLAUDE.md` and `formal/AGENTS.md` short and synchronized; put generated maps in `LEAN_OVERVIEW.md`, `LEAN_API.md`, and `LEAN_GAPS.md`.
- Existing potential-theory scaffolding is conditional/algebraic where mathlib lacks Riesz/subharmonic/Laplacian measure APIs.
