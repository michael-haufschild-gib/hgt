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
- Long proof descriptions can exhaust a bounded batch and remain pending; malformed/unanchored descriptions are recorded as failed and excluded. Monitor coverage/errors during enrichment.
