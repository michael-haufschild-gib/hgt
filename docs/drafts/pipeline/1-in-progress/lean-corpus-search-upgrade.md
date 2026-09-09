# Lean corpus search upgrade

- **ID:** lean-corpus-search-upgrade
- **Stage:** 1-in-progress
- **Type:** Engineering implementation
- **Statement:** Discover reusable Lean results, proof methods, and premise groups across the local corpus without exact naming.

## Accepted specification

Upgrade `scripts/formal_tools.py research`; preserve lexical JSON fields and AND/OR semantics. Add `--mode deep|hybrid|lexical` (deep after acceptance), a 120-second budget, full corpus source/type/proof indexing, local embeddings/reranking, and three-round reasoning with up to eight queries per round. Use SQLite plus bounded FAISS shards. All inference local; one shared worker. Return evidence-linked ideas, obligations, freshness, and partial results. No full Lean builds; one foreground Lean process per agent.

## Implementation work

- [x] Compatibility and versioned real-corpus benchmark fixtures.
- [x] Source inventory/chunks, general compiler extraction and incremental index implementation.
- [x] Local Qwen embedding/reranking and MLX generation runtime, explicit setup, offline worker.
- [x] Hybrid retrieval, method enrichment, iterative premise search, caching and deadlines.
- [x] Existing command integration and operator documentation.
- [ ] Regression, integration, offline, cancellation and retrieval acceptance audits.
- [ ] Publish measured report and switch default only after release gates pass.

## Working ownership

Main agent: `scripts/lean_research_corpus.py`, `scripts/lean_research_engine.py`, existing CLI integration, corresponding tests and operator documentation.
Initial delegated scopes: compiler exporter, runtime/setup, benchmark fixtures/evaluator. All subagents stopped at user's request; continue with one agent only.

## Evidence and decisions

- Existing lexical schema indexes names/modules/docs, not statements or proof bodies.
- RH frontier exporter excludes explicit data and unnamed proposition binders; a general exporter must not reuse those exclusions.
- LeanExplore reviewed revision: `6b25f8632cc3387cf85f7730375a690a1f1dfb79` (Apache-2.0).
- LeanSearch v2 reviewed revision: `94f4888cbaf9f4322535755f86cbac690ec18080` (Apache-2.0).
- Target: M3 Pro, 18 GiB RAM; Python runtime via uv; Qwen 0.6B embedding/reranker, MLX Qwen3-4B-Instruct-2507 4-bit generation.
- No performance improvement claimed before benchmarks. Selberg proof remains a separate unfinished mathematical goal.

## Log

- 2026-09-09 — implementation authorized; read current search schema, callers, tests and exporter before changes.
- 2026-09-09 — user selected progressive operation rather than waiting for complete embeddings. `research-indexer start/status/stop` controls one persistent local Python worker, with no Codex subagents. Starting it enables progressive hybrid default; `--mode lexical` preserves rollback. Deep default remains behind measured acceptance gates.
- Priority explicitly requested: RHTower → HTGeometry → rest, across source extraction, embeddings, method descriptions and explicit foreground compiler extraction. Compiler work never runs in background.
- Source snapshot: 55,873 inventoried files, 639,243 declarations, 1,419,921 text chunks; 1,302,085 eligible for embeddings. Source extractor migration is still filling; old records remain searchable with stale status. Model/description enrichment remains incomplete.
- MLX float32 embedding adapter verified against CPU on 96 real corpus inputs plus four queries: minimum cosine >0.9999998, maximum coordinate error <0.000001. Measured 19.31 statements/s, 10.48 ordinary proof chunks/s, 1.16 long chunks/s in small fixed probe groups. No whole-corpus ETA or quality gate inferred from these probes.
- Exact content cache survives deletion/recreation of source rows, so edits to neighboring declarations and line shifts reuse unchanged vectors. Changed dependency evidence rejects pending descriptions. Immutable vector shards and SQLite transactions retain committed progress.
- Initial combined unittest process (Python PID 15548) aborted from conflicting Torch/FAISS OpenMP libraries on macOS. User supplied matching crash report. Added isolated audit runner and pre-import guard; no `KMP_DUPLICATE_LIB_OK` workaround. Production already isolates inference from FAISS.
- Isolated audit passed 167 tests before final guard addition; targeted vector suite then passed 7 tests including guard (168 current research tests total). Existing lexical tests passed 17 CLI + 24 index cases. Exporter audit included 37 tests with foreground Lean checks, no full builds.
- Live progressive `entropy` query: 16.05 seconds, 20 candidates + 20 source arguments, no stage errors. Live vector-backed `bounded amplification` query: 22.88 seconds, 20 candidates + 15 source arguments, 256 available vectors, no stage errors. Both explicitly reported incomplete corpus/vector coverage; these are operational smoke tests, not retrieval quality acceptance.

## Remaining rollout work

- Background source migration, embeddings and validated method descriptions continue incrementally. First published vectors verified entirely under RHTower. Use `python3 scripts/formal_tools.py research-indexer status` for current progress rather than this snapshot.
- Full measured five-way held-out benchmark and default-deep release gates remain pending. Do not claim quality improvement or proof applicability from these smoke tests.
- General compiler export is implemented and tested, but bulk extraction of available artifacts remains explicit foreground work. Missing/stale artifacts remain labeled; no source recompilation is implicit.
- Long proof descriptions save completed chunk summaries and resume them after interruptions. Malformed/unanchored descriptions remain failed and excluded. Monitor coverage/errors during enrichment.

## Indexing error repair, 2026-09-09

- Reproduced source batches stuck in `_invalidate_dependents` while re-extracting unchanged files. Content hashes now skip this traversal for unchanged sources; real-edit traversal is bounded with conservative description invalidation as fallback. A repaired foreground source batch completed 655 files within its work budget.
- Shorter JSON generation uses numbered code-line citations resolved to exact source text. Comments are excluded from model input/citation eligibility; one comment-only generated description was requeued. Prompt version `method-3-code-lines` retries earlier prompt-version failures automatically. Generated interpretations remain unverified, despite valid source citations.
- `method_chunks` stores completed summaries across deadline/preemption retries and invalidates them with source/dependency changes.
- Reproduced immediate runtime expiry from system Python 3.9 (`time.monotonic()` near zero) talking to Python 3.12 (clock near system uptime). Protocol 2 sends remaining duration and rebases it in worker; original client deadline still governs cancellation. Live system-Python embedding request passed in 2.00 seconds, 1024 dimensions.
- Status retains per-phase errors and distinguishes normal budget/preemption deferrals. The resumed worker remains RHTower → HTGeometry → rest. No new agents or background Lean processes.
- Targeted checks: corpus 16, engine 15, runtime 32, background 2, vector 7 tests passed (72 total). Live repaired methods and source batches passed; historical failures remain queued for the new prompt. No full Lean builds or instruction-file changes in this repair.

## Concurrent search and timeout repair, 2026-09-09

- Reproduced `database is locked` when search opened the corpus with schema writes during another writer's transaction. Search now opens read-only; optional cache publication uses a separate zero-wait connection and skips contention. Regression holds an uncommitted declaration deletion while a real search child reads the last committed result.
- Search leaves refresh to the active background indexer. Without that worker, an owned refresh process has a hard maximum of three seconds. Completed lexical lanes, semantic matches and dependency candidates publish before later work; coverage counts occur after initial retrieval. Reranking and reasoning have stage budgets. Timeout output identifies the active stage and retains prior snapshots.
- Long deep goals first run explicit keyword relaxations, recorded in `query_trace`; the original lexical fields and AND semantics remain unchanged. Malformed generated queries no longer discard later valid queries. Ranked visible sources feed the judge, using compact source IDs resolved back to corpus evidence. Truncated outer JSON cannot be mistaken for a completed inner step. Scalar obligation/evidence strings normalize to singleton lists before source validation.
- Live hybrid `entropy`: 14.95 seconds, 20 candidates and 20 source arguments, no errors while indexing continued. Live deep natural-language goal: first candidates at 2.48 seconds, 20 candidates and 20 arguments retained, 89.24 seconds overall; later decomposition timed out. Separate real local grouping probe produced one source-linked ingredient set, with two steps after schema normalization; generated proof quotations failed evidence validation and remained excluded. These are operational checks, not relevance/applicability acceptance.
- Targeted checks passed: engine 24, CLI supervision 6, corpus 16, vectors 7, legacy index 24 and legacy CLI 17 (94 tests). Legacy CLI fixtures now isolate the project root so production progressive settings cannot trigger model inference from unit tests. No Lean builds, subagents or instruction-file edits. Background RHTower → HTGeometry → rest indexing remains active.
- Forced five-second deep deadline returned in 5.005 seconds with 20 candidates and 20 arguments; first candidates at 2.33 seconds. Output identified unfinished decomposition and retained retrieval interruption errors. Operational audit: `formal/.lake/hgt-research/discovery-1/benchmarks/timeout-lock-repair-2026-09-09.json`.
