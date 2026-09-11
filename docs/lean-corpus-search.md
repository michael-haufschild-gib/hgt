# Lean corpus search

`research` keeps the existing name/docstring search and adds local searches for
mathematical statements, proof arguments and groups of premises. Normal searches
and incremental enrichment keep corpus text, queries and descriptions local.
An explicitly authorized GPU bootstrap can export corpus chunks for batch
embedding; see [B200/B300 batch operation](../scripts/research_batch/README.md).

```sh
python3 scripts/formal_tools.py research 'uniform bound forces a growing parameter to vanish' --mode deep
python3 scripts/formal_tools.py research 'entropy' --mode hybrid --json
python3 scripts/formal_tools.py research 'clock inverse' --mode lexical --exact
```

## Modes and output

- `lexical`: existing AND query semantics; `--any` means OR, inner quotes mean a
  phrase, and `--exact` disables prefix expansion. No model dependencies needed.
- `hybrid`: additional statement, structural-expression and proof-source
  retrieval, using local embeddings and reranking when available.
- `deep`: hybrid retrieval followed by up to three rounds of premise and method
  discovery, with at most eight distinct queries in a round. Long goals also
  start with short literal keyword pairs, recorded as `keyword_relaxation` in
  `query_trace`, so candidate retrieval can proceed while models are busy.

`--budget-seconds` defaults to 300. The parent command supervises the search
process and returns its latest snapshot on deadline or cancellation. Models
never download during queries. An unavailable model/index is reported as an
unfinished stage, alongside the available lexical results.
Completed lexical lanes and semantic matches are retained before reranking or
reasoning. Empty `ingredient_sets` means no validated grouping was produced;
it does not establish that the corpus lacks the required premises.
Deep search reserves up to 60 seconds (one third of the remaining request budget)
for judging retrieved sources before starting more query expansions. Expansions
skipped to preserve that time are listed in `unfinished_stages`.

Existing JSON fields (`declarations`, `exploration`, counts, `markers`, `match`,
`options`, `backend`) retain their lexical meaning. Additional fields are:

| Field | Meaning |
| --- | --- |
| `candidate_lemmas` | Ranked declarations with full source/available compiled statements, hypotheses and provenance |
| `source_arguments` | Independently ranked proof sources and any stored method descriptions |
| `proof_ideas` | Generated transfer proposals, exact source evidence and remaining obligations |
| `ingredient_sets` | Proposed steps with candidate IDs and unresolved obligations |
| `prose` | Research documentation, kept distinct from declarations |
| `source_passages` | Whole-file Lean passages, including syntax outside provisional declaration extraction |
| `query_trace` | Actual original and generated queries, rounds and lexical semantics |
| `coverage`, `semantic_coverage` | File outcomes and how much enrichment is available |
| `partial`, `unfinished_stages`, `errors` | Work not completed within this request |
| `index_warnings` | Index coverage or freshness limitations, separate from unfinished retrieval |
| `active_stage`, `stage_seconds`, `first_candidate_seconds` | Stage interrupted or completed, stage durations, and time to the first candidate snapshot |

`partial: false` means the requested search finished against the available index;
it does not mean every source has embeddings or compiler metadata. Background
indexing alone does not make a search partial. Use returned hits even when
`index_warnings` reports pending enrichment. Actual deadlines, cancellation and
failed search stages still set `partial: true` and name `unfinished_stages`.

Coverage statistics do not block retrieval. `coverage.status: snapshot` labels
the indexer's recorded counts and exposes their generation separately from the
current generation. Optional live counts share a one-second reporting allowance;
`semantic_coverage.complete: null` with `status: not_measured` means counts were
not obtained, not zero coverage. Missing counts never suppress semantic search.

Module filters, exclusions and module diversity apply to the additional lanes.
Exact identifiers remain prominent. `--offset` and `--limit` select each ranked
declaration/argument lane independently. Cached completed results are keyed by
query, options, corpus generation, engine and model versions.

An imported compiler snapshot and a current source file are distinct records of
evidence. A successful import does not establish that a changed source file was
compiled. Inspect `compiler_status`, `compiler_metadata` and `file_status` before
using a compiled statement. Generated descriptions, dependency references and
retrieval assessments do not establish theorem applicability or completion.

## Installation and indexing

```sh
python3 scripts/formal_tools.py research-setup
python3 scripts/formal_tools.py research-setup --verify
python3 scripts/formal_tools.py research-setup --status
python3 scripts/formal_tools.py search-index --corpus --budget-seconds 120
python3 scripts/formal_tools.py search-index --compiler --budget-seconds 120
python3 scripts/formal_tools.py search-index --vectors --budget-seconds 120
python3 scripts/formal_tools.py search-index --methods --budget-seconds 120
python3 scripts/formal_tools.py search-index --vectors --compact --budget-seconds 120
```

Setup explicitly creates a locked Python 3.12 environment and downloads pinned
model snapshots. The runtime uses one shared local supervisor and one inference
child; concurrent agents queue instead of loading separate model copies.
Interactive inference has priority over enrichment. Runtime details, limits,
model provenance and smoke checks are in
[`scripts/research_runtime/README.md`](../scripts/research_runtime/README.md).

Index commands are bounded and resumable. Repeat them to continue pending work.
Source inventory covers project Lean files, installed Lake package sources and
repository research prose. Every inventoried file has an outcome, including
pending and failed files. Complete source chunks preserve material not recognized
by provisional declaration extraction. Model enrichment is additional coverage;
it does not block lexical access to pending sources.

### Progressive operation

```sh
python3 scripts/formal_tools.py research-indexer start
python3 scripts/formal_tools.py research-indexer status
python3 scripts/formal_tools.py research-indexer stop
```

Starting the indexer enables progressive hybrid as the ordinary `research`
default once the source database exists. Available statement, proof-body and
research-note matches work immediately; completed embeddings join retrieval
without waiting for full coverage. `--mode lexical` retains the old behavior.
`--mode deep` explicitly requests the reasoning loop; its automatic promotion
still requires measured retrieval acceptance.

One local Python worker persists independently of the requesting terminal. It
runs bounded source, embedding and method-description batches, with no Codex
subagents or remote inference. Work order is **RHTower, then HTGeometry, then
the rest**, across sources, vectors and method descriptions. It sleeps between
cycles, preempted inference remains pending, and interactive searches take
priority in the shared model worker. Restart it after reboot; no login service
or automatic system startup is installed. `status` shows phase, latest completed
coverage and errors. `stop` cancels/reaps its owned maintenance child.

Search retrieval uses read-only SQLite connections. Optional result-cache writes
skip a busy writer. While the background indexer runs, searches leave source
refresh to it; otherwise refresh runs in an owned process capped at three
seconds (less for short budgets). `--no-refresh` uses committed records without
requesting refresh. Size/mtime changes or an extractor-version
change enqueue source extraction. Each changed file publishes its replacement
records transactionally. Content hashes reuse identical embeddings across
renames, line shifts and edits to neighboring declarations. Changed/deleted
records disappear from active vector mappings; cached vector values remain
reusable but cannot produce stale search hits. Source/dependency changes
invalidate descriptions; concurrent evidence changes reject pending generated
descriptions. Model/prompt versions control enrichment reuse. The worker resumes
pending batches rather than rebuilding the corpus on every cycle.

Compiler extraction remains an explicit foreground operation. The background
indexer never starts Lean, builds modules or downloads models. Pending and stale
compiler evidence stays labeled in results.

Compiler extraction uses cached oleans and foreground `lake env lean` scratch
checks. It neither imports the project root umbrella nor builds missing modules.
Private/generated declarations and all binder kinds remain in extracted data;
unavailable proof values/axioms are represented explicitly. Source changes and
dependency changes invalidate affected descriptions and vectors.

The discovery database lives under
`formal/.lake/hgt-research/discovery-1/`. It is disposable derived data. SQLite
transactions publish file updates and vector references atomically. FAISS shards
are immutable and bounded; compaction preserves old files for active readers.
The existing `.lean_search-*.db` lexical database remains independent.

## Evaluation and rollout

The versioned benchmark contains actual declarations and source-anchored proof
analogies, with held-out theorem families. Run the evaluator's `--help` for
fixture validation and mode comparisons:

```sh
python3 scripts/lean_research_benchmark.py --help
python3 -m unittest discover -s scripts/tests -p 'test_research_search.py'
scripts/research_runtime/.venv/bin/python scripts/research_runtime/audit.py
```

The intended final default is deep search. It is activated only after the
recorded release gates pass; progressive hybrid can run during enrichment. The
lexical mode remains available for immediate rollback. Benchmark labels measure
retrieval on those cases, not completeness of the mathematical corpus or proof
of a research conjecture. Quality and throughput must be reported from actual
runs rather than inferred from upstream benchmark results.

The audit isolates test modules in foreground processes because the macOS Torch
and FAISS wheels use conflicting OpenMP libraries. Production already isolates
inference from vector retrieval; the audit follows that separation.

### Initial measurements, 2026-09-09

Current extracted source corpus: about 639,000 declarations and 1.30 million
embedding-eligible chunks. Full-file Lean chunks remain searchable lexically and
are excluded from redundant embedding work. Exact hash deduplication removes
about 39,000 source embeddings at this snapshot; it is not a tenfold reduction.

Fixed real-corpus probe, 32 records per group on this M3 Pro:

| Representation | Torch MPS records/s | MLX float32 records/s |
| --- | ---: | ---: |
| Statements | 11.03 | 19.31 |
| Proof chunks | 5.88 | 10.48 |
| Long proof chunks | 0.66 | 1.16 |

MLX uses the original 0.6B weights and shape-aware compilation. Across the 96
saved documents and four queries, minimum cosine against CPU reference exceeded
0.9999998 and maximum coordinate error was below 0.000001. These small probe
groups are throughput evidence, not a corpus-wide quality audit or a guaranteed
completion ETA. Compiler-derived embeddings and generated method descriptions
add work beyond this source count. Progressive operation avoids making search
availability depend on full enrichment.
