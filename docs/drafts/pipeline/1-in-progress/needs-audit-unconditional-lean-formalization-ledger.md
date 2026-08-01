# Needs-audit unconditional Lean formalization ledger

- **Kind:** operational audit ledger; not a mathematical claim card
- **Scope:** every tracked card in `../2-fully-proven/needs-audit/` as of 2026-08-01
- **Goal:** map every dependency-closed paper theorem to an exact unconditional Lean theorem, prove missing infrastructure, wire area umbrellas, check axioms/lint/build, then promote its card to Stage 3.
- **Constraints:** no numerical/computational evidence; no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe`; search corpus before new Lean; `lake env lean <file>` during development; `lake build <module>` only at final audit; one foreground Lean process owned by this task; preserve unrelated dirty worktree changes.

## Promotion gate

A source card leaves `needs-audit` only after:

1. every dependency-closed theorem stated as proved in that card is represented exactly, without added route hypotheses or weakened conclusion;
2. every new declaration is unconditional and kernel-checked;
3. `#print axioms` reports only accepted logical foundations;
4. leaf file passes `lake env lean <file>`;
5. area umbrella imports the leaf and final `lake build <module>` passes;
6. formal lint and generated-index checks pass;
7. card records exact theorem/module and `[LEAN-PROVED]` status.

## Worktree isolation

Pre-existing edits exist in `formal/GaloisForLFunctions/HTGeometry.lean`,
`formal/GaloisForLFunctions/RHTower.lean`, `formal/LEAN_API.md`, `formal/lakefile.toml`, and several
untracked Lean modules. Other foreground Lean/Lake jobs were active at task start. Do not overwrite,
revert, or attribute those changes to this ledger. Re-inspect before touching shared umbrellas.

## Card manifest and audit state

Legend: `UNREAD` → `AUDITED` → `LEAN` → `GATED` → `PROMOTED`; `DEMOTE` means inherited Stage 2 evidence is not dependency-closed.

<!-- Entries are appended as card audits close. The canonical 79-file scope is the tracked contents of ../2-fully-proven/needs-audit/. -->

## Log

- 2026-08-01 — ledger created; 79 tracked cards, 38,432 total lines. Required project, formal, scientific-method, skill, and Serena memory guidance read. No task-owned Lean process started.
