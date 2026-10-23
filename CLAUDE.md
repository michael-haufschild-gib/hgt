## IMMUTABLE RULE: Follow the whole prompt, every turn
Read the user's prompt in full, line by line, and follow every rule in it exactly -- including the
rules at the end that look like boilerplate (tool choice, build commands, proof discipline,
read-only files). 

## IMMUTABLE RULE: First search lean corpus, then check mathlib
Always use the search tool for the lean corpus to find existing work, before checking mathlib.
**Always use the search tool over `rg` and `grep` to research in the lean corpus.** `rg`/`grep`
are only for exact source-text confirmation of something the search tool already surfaced (a
literal name's spelling, a tactic string, an import line) -- never as the research tool itself.

## The research pipeline (Kanban)
Card template: docs/drafts/pipeline/_card-template.md
1. Backlog → docs/drafts/pipeline/0-backlog
2. In progress → docs/drafts/pipeline/1-in-progress
3. Fully proven on paper → docs/drafts/pipeline/2-fully-proven
4. Formalised in Lean 4 → docs/drafts/pipeline/3-formalized
5. Publication-ready pre-prints → docs/drafts/pipeline/4-publication-ready
6. Failed/retired → docs/drafts/pipeline/5-failed

## Use the search tool for our lean corpus
Command: `scripts/formal_tools.py research "<query>"`. Run it directly; do not run `--help` or read
the search code first (only to diagnose a failed command, or when asked to change the tool).

By default it searches keywords and meaning together, then reranks: declaration names, statements,
docstrings, proof bodies, the Markdown in `formal/`, and the formalized pipeline cards
(`docs/drafts/pipeline/3-formalized`: paper proofs naming their Lean declarations). The rest of
`docs/` is not indexed. Edits are indexed automatically within about 10 seconds.

What to use when:
- Know a name or part of one: `research inverseClockK`. `--mode lexical` is a keyword-only lookup in
  under a second.
- Looking for a result: state it in words, e.g. `research "zero-free region near the line Re s = 1"`.
- Looking for a proof technique: describe the mechanism, e.g.
  `research "bound a bilinear form by Cauchy-Schwarz"`.
- Mathlib, only after our corpus: `--scope mathlib` (`--scope all` for both). Mathlib is matched by
  keyword only: query Lean names and terms, not sentences; add `--exact` for a known full name.
- `rg`/`grep`: only to confirm the exact text of something the search surfaced, or to list every
  literal occurrence of a known name.

Reading results:
- `Declarations`: keyword hits in this project, every term required.
- `Candidate lemmas`: best matches by meaning and keyword, reranked. Read this first for any query
  phrased in words; Mathlib hits appear only here.
- `Source arguments`: proofs whose method matches the query.
- `Markdown notes`: matching Markdown in `formal/` and formalized pipeline cards. `Source passages`:
  whole-file Lean chunks, for notation and examples outside declarations.
- `--json` keys: `declarations`, `candidate_lemmas`, `source_arguments`, `prose`, `source_passages`.
- A hit is a lead: check its statement in Lean before relying on it.
- `partial search`: the time budget ran out; use what came back. `semantic_index_lagging_N_documents`:
  the newest edits may not be found by meaning yet.

Query syntax and paging:
- Spaces mean AND, `--any` means OR, inner quotes require a phrase: `research '"critical line" zero'`.
  `--exact` turns off prefix matching. These change keyword matching only.
- 20 hits per section, at most 2 per module, plus 5 from other modules. `--per-module 0` removes the
  cap, `--offset 20` shows the next page, `--explore 0` hides the extras.
- `--module <substring>` / `--exclude-module <substring>` filter by module; `--json` gives structured
  output.
- No useful hits: rephrase, drop terms, try `--any`, or describe the goal in words.
- "Local Qdrant unavailable": run `./launch.sh`, then retry.

## Python scratch jobs
- Run potentially long Python jobs through `python3 scripts/run_guarded.py --timeout 600 -- python3 /tmp/job.py`.
  Choose a finite timeout; wrap an entire pipeline with `-- /bin/zsh -c '...'`.
- Tool timeouts may background jobs. Cancel the guarded command by its owned PID/handle, never `pkill -f`.
  Verify exit before starting a replacement. Exit 124 means the runner timed out and cleaned up its process group.
- Keep jobs in the runner's process group; do not detach them. Search commands and managed services retain their documented launch commands.

## Proof integrity

- Every result must be unconditional: no added hypotheses, premises, or axioms.
- No `sorry`, `admit`, `sorryAx`, `axiom`, `opaque`, `unsafe`, `native_decide`, or equivalent
  placeholders, trusted-computation shortcuts, or kernel-bypass mechanisms.
- Do not hide an unproved mathematical input in an assumption binder, typeclass instance,
  structure field, `Prop` interface, helper theorem, or imported dependency. A wrapper does not
  discharge its premises. Check transitive dependencies with `#print axioms`.
- A missing analytic input is not a hypothesis to add: it means the theorem is not ready. Prove
  it, weaken the conclusion until the statement is unconditional, or record the gap on the
  pipeline card.

## Lean proof style

- Optimize proofs; never raise or disable limits to make them compile. No `maxHeartbeats`
  increases or `0`, `maxRecDepth`, `synthInstance.maxHeartbeats`, `synthInstance.maxSize`, or
  equivalent local/global budget hacks. Reduce tactic work: explicit `nlinarith` inputs,
  targeted `simp only`, small named lemmas, and reusable rewrites instead of repeated unfolding.
- Verify mathlib names in `/tmp` scratch files before using them; follow the compilation rules below.
- Add helpful, crisp comments for module purpose, non-obvious declarations, and key proof steps.
  Do not leave substantial mathematics unexplained; trivial rewrites need no narration.
- Comments are mathematics, not diary. No references to research docs, task numbers, sessions,
  dates, or process notes ("pre-certified", "banked", "round N") — in two days nobody can decode
  them. A Lean project is self-contained: it stands for itself as a proof. A docstring states
  what the declaration says mathematically and, briefly, the proof mechanism — nothing else.

## Lean compilation

1. **Never run `lake build`**, including for a single module or missing dependency.
2. Every compile is `lake --old env lean ...`, run from `formal/`, in the foreground, one process
   per agent at a time. Other agents may compile independently. `--old` goes before `env`.
3. **Check a file** (writes no olean; also the final audit):
   `lake --old env lean GaloisForLFunctions/<Path>/<Module>.lean`
4. **Build your module's olean only when another file you are writing imports it:**
   `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/<Path>/<Module>.olean -i .lake/build/lib/lean/GaloisForLFunctions/<Path>/<Module>.ilean GaloisForLFunctions/<Path>/<Module>.lean`
5. **Missing dependency olean:** use rule 4's command for exactly the missing module, then retry
   your file. Resolve further missing oleans one by one. Never rebuild an olean that exists.
6. No full or umbrella builds. Wire finished modules into their umbrella with an import, but
   do not compile the umbrella.
7. Clean up your own stale files; preserve other agents' work.

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
- Do not use effort estimations to decide on anything.
