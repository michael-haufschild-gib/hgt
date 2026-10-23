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

## A proof must be unconditional
Lean proofs must be unconditional, no hypotheses or premises. Anything that is based on something that is not proven is not a proof.

## Lean rules
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. **NEVER run `lake build`.** Not for a module, not for an umbrella, not for "just one file",
   not for a dependency. It recompiles thousands of modules and blocks the whole machine.
3. Every compile is `lake --old env lean ...`, run from `formal/`, in the foreground, one process
   at a time (other agents build in parallel to you). `--old` goes before `env`; it makes lake
   reuse every existing olean instead of rebuilding it.
4. **Check a file** (writes no olean; this is also the final audit):
   `lake --old env lean GaloisForLFunctions/<Path>/<Module>.lean`
5. **Build the olean of your own file** — only when another file you are writing imports it:
   `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/<Path>/<Module>.olean -i .lake/build/lib/lean/GaloisForLFunctions/<Path>/<Module>.ilean GaloisForLFunctions/<Path>/<Module>.lean`
6. **Missing dependency olean** (error `object file '.../GaloisForLFunctions/X/Y/Z.olean' ... does
   not exist`): build exactly that one olean with the command of rule 5 for
   `GaloisForLFunctions/X/Y/Z`, then retry your file. If the retry names another missing olean,
   build that one, and so on — one by one. Build nothing else. Never rebuild an olean that exists.
7. Do not run full or umbrella builds. Wire finished modules into their umbrella with an import
   line, but do not compile the umbrella.
8. Make sure you don't leave stale files; clean up after yourself.
9. Optimize lean code. No raising heartbeat hacks.
10. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

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