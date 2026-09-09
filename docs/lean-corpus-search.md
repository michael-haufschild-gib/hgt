# Lean corpus search

`research` keeps the existing name/docstring search and adds local searches for
mathematical statements, proof arguments and groups of premises. Corpus text,
queries and generated descriptions stay on this machine.

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
  discovery, with at most eight distinct queries in a round.

`--budget-seconds` defaults to 120. The parent command supervises the search
process and returns its latest snapshot on deadline or cancellation. Models
never download during queries. An unavailable model/index is reported as an
unfinished stage, alongside the available lexical results.

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
scripts/research_runtime/.venv/bin/python -m unittest discover -s scripts/tests -p 'test_lean_research_*.py'
```

The intended production default is deep search. It is activated only after the
recorded release gates pass; until then, select `--mode deep` explicitly. The
lexical mode remains available for immediate rollback. Benchmark labels measure
retrieval on those cases, not completeness of the mathematical corpus or proof
of a research conjecture. Quality and throughput must be reported from actual
runs rather than inferred from upstream benchmark results.
