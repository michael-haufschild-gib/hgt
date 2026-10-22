## IMMUTABLE RULE: Follow the whole prompt, every turn
Read the user's prompt in full, line by line, and follow every rule in it exactly -- including the
rules at the end that look like boilerplate (tool choice, build commands, proof discipline,
read-only files). The rules hold for the whole session, not for the first few minutes. Re-read this
file and the user's prompt at the start of every turn, and before each tool call name the rule that
governs it and confirm the call matches. A rule is never superseded by convenience, by a plan formed
earlier in the session, or by default habits. If a rule appears to block the task, say so in one
sentence and ask -- never route around it silently.

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

## Check prior research before any new topic or writing new lean code
- Current ledger of the major RH proof routes and route candidates: docs/reports/rh-current-frontier-map.md (ignore if you are not working on RH)
- High level facts about things the RH proof must or can not be like: docs/reports/STATUS.md (ignore if not working on RH)

## Use the search tool for our lean corpus
- Run the documented search command directly. Do not run `research --help` or read the search Python
  implementation as preparation. Consult help/source only to diagnose a command execution failure
  or when explicitly tasked with changing the search tool.
- With partial results, use the available hits and reported coverage. With no useful hits, broaden
  or rephrase the query, try `--any`, or switch search mode.
- Search: `scripts/formal_tools.py research "clock inverse"`. Default hybrid searches declaration
  names, docstrings, statements, proof bodies and research notes, lexically and semantically.
- Scope defaults to this project. `--scope mathlib` searches installed Mathlib instead, `--scope all`
  searches both. Only our corpus has semantic vectors; Mathlib results are lexical.
- Describe the goal or proof mechanism in the query: docstrings and statements are embedded, so a
  natural-language goal matches. `--budget-seconds 300` sets the request budget (default: 300).
- Lexical matching: spaces mean AND; `--any` means OR. Use inner quotes for phrases:
  `research '"critical line" zero'`. `--exact` disables prefix expansion; `--mode lexical` uses only lexical search.
- Default: 20 hits per ranked section, at most 2 per module, plus 5 lexical exploration hits.
  Use `--per-module 0` to remove the cap, `--explore 0` to hide extras, `--offset 20` for the next page.
- Filter with `--module <substring>` or `--exclude-module <substring>`; `--json` gives structured results.
- In JSON, inspect `candidate_lemmas` and `prose` alongside `declarations`.
- Check `partial` and coverage; verify candidate applicability in Lean before relying on a hit.
- `--no-refresh` searches the cached index without refreshing it. Use `rg` for exhaustive source-text searches.

## Python scratch jobs
- Run potentially long Python jobs through `python3 scripts/run_guarded.py --timeout 600 -- python3 /tmp/job.py`.
  Choose a finite timeout; wrap an entire pipeline with `-- /bin/zsh -c '...'`.
- Tool timeouts may background jobs. Cancel the guarded command by its owned PID/handle, never `pkill -f`.
  Verify exit before starting a replacement. Exit 124 means the runner timed out and cleaned up its process group.
- Keep jobs in the runner's process group; do not detach them. Search commands and managed services retain their documented launch commands.

## Lean discipline
1. **ALL LEAN PROOFS MUST BE UNCONDITIONAL, WITHOUT ADDED HYPOTHESES OR PREMISES.** No extra
   assumption binder, no `variable` constraint smuggled in, no `axiom`, `sorry`, `admit`,
   `opaque`, `unsafe`, `native_decide`, and no `Prop`-valued interface standing in for an
   analytic input the proof actually needs. Only the genuine typing side-conditions of the
   objects involved may appear in a statement. If the proof needs an input that is not
   available, the contribution is not ready: prove the input, or weaken the conclusion until
   it is unconditional, or record the gap on the pipeline card -- never in the Lean statement.
2. **Never run `lake build`.** The only compile/audit command is
   `lake --old env lean GaloisForLFunctions/<Path>/<Module>.lean`, run from `formal/`.
   `--old` is a *lake* flag and goes before `env`; `lean` itself rejects it. It avoids
   rebuilding unchanged modules. If a file's imports are not yet compiled, this one command
   compiles them -- never use `lake build` to "prepare" them.
3. Always build in the foreground -- never backgrounded -- and exactly one build process per
   agent/chat session at a time (other agents can also build in parallel to you).
   **If a build reports a missing `.olean`, build exactly that one module** --
   `lake --old env lean GaloisForLFunctions/A/B/C.lean` for the module it names, plain command,
   **never with `-o`/`-i`** -- then retry the original file, repeating per missing olean. Never
   widen this to `lake build`, an umbrella target, or a full build, and never stop to ask: the
   error names the next target.
4. No computations
5. No full builds, no umbrella builds, no large aggregate targets. Wire finished modules into
   their umbrella with an import line, but do not build the umbrella to check it.
6. make sure you don't leave staleclean up after yourself.
7. **Optimize lean code. NEVER use raising-maxHeartbeat hacks.** No
   `set_option maxHeartbeats <bigger>` or `0`, no `maxRecDepth` bump, no
   `synthInstance.maxHeartbeats`/`maxSize` bump, no other option raised to make an
   elaboration finish. A proof that needs a raised budget is written wrong: feed `nlinarith`
   exactly the products it needs, use `simp only [...]`, split monolithic proofs into cheap
   named lemmas, prove a rewrite lemma once instead of unfolding repeatedly.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

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
