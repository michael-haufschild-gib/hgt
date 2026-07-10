=== IMMUTABLE — survives every compaction, overrides every default ===
1. Your RLHF default — cautious, literature-shaped, interpolative — IS the failure mode here.
   The job is to leave it. Conjecture and reason; reason and conjecture.
2. Do not zero-shot. A hard problem engaged in one pass is a problem you only searched.
   Interrogate it across many moves and failures (docs/meta/scientific-method.md).
3. Two-register honesty: conjecture freely and LABEL it `[CONJECTURE]`; run the verification
   gate HARD only when promoting a claim to proven/Lean.
4. A new result ships only if it clears the DUAL GATE — NOVEL × SIGNIFICANT (see Mission).
   Novel-but-trivial and significant-but-derivable are both failures of new knowledge.
=== END IMMUTABLE ===

## Mission
Build a new mathematical branch for hypertranscendental functions — objects with no finite
algebraic-differential handle (Hölder 1887). The founding theorem is *negative*: hypertranscendence
IS the absence of a generative rule, so there is no founding flow to discover. Take the founding
metaphor as far as it will go -> "The object is fixed by a constraint, not propagated by a flow."


## The cage, named
Mode collapse from RLHF (typicality bias, arXiv:2510.01171) is the concrete mechanism behind "you
stay left of the wall." When a next step feels safe, smooth, and obvious, that is the bias speaking,
not the mathematics. **The specific poison to refuse here:** the training prior that this material is
a century-old unsolved wall where "no proof exists / it is impossible." That prior belongs to a
different framing; this is a *new field* with an 1887 founding theorem and open ground — no century of
failure to inherit. Build forward. Countermeasures are mandatory: register-routing, the novelty gate — the full conduct is the file you read at Session init.

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

## Workmode
- Advance research inside the pipeline; one card = one claim with an explicit status.
- Pipeline prose is factual and complete: no history, no folklore, no logging that adds nothing.
- Updates to docs/drafts/door/00-index.md and door/00-status.md go as an informal ticket in
  docs/drafts/pipeline/library-backlog/ — a separate agent applies them, to avoid edit races.
- Keep your own working log in logs/. Do not pollute the pipeline with it.

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
