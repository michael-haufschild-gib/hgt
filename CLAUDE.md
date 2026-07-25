## Session init
1. Read fully, line by line: docs/meta/scientific-method.md

## The research pipeline (Kanban)
Card template: docs/drafts/pipeline/_card-template.md
1. Backlog → docs/drafts/pipeline/0-backlog
2. In progress → docs/drafts/pipeline/1-in-progress
3. Fully proven on paper → docs/drafts/pipeline/2-fully-proven
4. Formalised in Lean 4 → docs/drafts/pipeline/3-formalized
5. Publication-ready pre-prints → docs/drafts/pipeline/4-publication-ready
Failed/retired → docs/drafts/pipeline/5-failed (read it before re-attempting a dead route).

## Check prior research before any new topic
Extensive work already exists. Search first; do not re-derive or re-fail existing lean code or math:
- formal/
- docs/drafts/pipeline/3-formalized
- docs/support-extraction-log.md
- docs/drafts/pipeline/2-fully-proven
- docs/drafts/pipeline/5-failed
(Standalone repo: keep prior-research paths inside this tree. In nested development the parent
workspace's own root file supplies its broader corpus; do not hard-code parent paths here.)

## Lean discipline
- Verify every mathlib name against THIS toolchain in a /tmp scratch file
  (`lake env lean /tmp/x.lean` with `have := @Name` lines). Never trust a recalled name.
- `#print axioms` via a /tmp scratch file, never by editing the tree.
- The formal lint gate is authoritative: run `scripts/formal_tools.py lint`; currently no active
  `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is allowed.
- For formal project navigation, read `formal/README.md` and use
  `scripts/formal_tools.py research "<query>"` before proving a reusable lemma.
- Numerically pre-certify a formalisation plan (mpmath) before writing Lean.

## Append-only edits
- Append at EOF with a shell here-doc (`cat >> file <<'EOF' … EOF`) or equivalent primitive.
- Do not use apply_patch to append. Use targeted edits only to insert, replace, move, or delete.

## Session & compaction management
- Long tasks survive compaction via files, not memory. Before a hard problem, write the card in the
  pipeline; check progress back to it.
- Do not stop a task early over token budget.
- When compacting — PRESERVE: open card + its status, the current conjecture and its label, the named
  open core, modified files, dead routes already ruled out. DISCARD: file contents already read, raw
  computation logs, resolved sub-steps.

## Reporting cadence
- Work in large batches. Do not narrate steps, announce intent, or post progress between tool calls.
  Silence during work is correct.
- Report only when: a substantial batch or the whole task is finished; a blocking question only the
  user can resolve; a discovery that changes the plan or invalidates the request; a real failure.
- No preambles, no "next I will…", no per-file commentary, no restating work already visible.

## Budget blindness
- Never use context-window size, token count, effort, cost, or elapsed time as an input to any
  decision — not for choosing a card, not for scoping a proof, not for picking an approach, not for
  deciding when to stop. Do not think about them, do not mention them, do not offer a cheaper variant.
- Do the job in full, at full depth. Many sessions, months, or years is acceptable and expected.
- Context compacts automatically; long work survives in files (pipeline cards, logs, memories), not
  in the transcript. When a task is long, persist state to disk and continue — never truncate,
  sample, or downscope to conserve budget.
- Stop only when the work is done, genuinely blocked, or the user says stop.
