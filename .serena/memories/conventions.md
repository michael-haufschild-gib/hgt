# Conventions

- Follow AGENTS/CLAUDE session init before research work: read core vision, charter/wall-door, and door index fully.
- Research advances through pipeline cards; keep `docs/drafts/door/00-status.md` and relevant bucket/index files consistent when status changes.
- Door discipline: every mathematical item is graded as NATIVE, CONJECTURE/native, BRIDGE, IMPORT, EMBASSY/META/etc. Door-2 is decisive: if parent fields prove it after stripping multi-`q` language, grade BRIDGE/IMPORT, not NATIVE.
- Current C5 criterion: native candidates must use the `σ_p` jointly and irreducibly; axis-mode/prime-decoupled objects usually become BRIDGE. Combination modes with Baker/small-divisor control are the live route.
- Lean two-channel rule: conjectures become `def ... : Prop`, never `axiom` or placeholder theorem. The Lean tree is expected to have zero real `sorry` tokens.
- Lean name discipline: verify names against this toolchain via scratch Lean files; do not trust recalled mathlib names.
- Axiom discipline: allowed audit subset is `[propext, Classical.choice, Quot.sound]`; `scripts/check_axioms.sh` is the ground truth.
- Append-only edits: append at EOF using a here-doc or equivalent append primitive; do not use `apply_patch` for append-only changes. Use targeted edit tools for insert/replace/move/delete.
- Computations should be avoided unless needed; archive results in `computations/`. Do not leave research logging in pipeline cards; use `logs/` for working logs.