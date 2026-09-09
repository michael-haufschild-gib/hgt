# Lean corpus search upgrade

- **ID:** lean-corpus-search-upgrade
- **Stage:** 1-in-progress
- **Type:** Engineering implementation
- **Statement:** Discover reusable Lean results, proof methods, and premise groups across the local corpus without exact naming.

## Accepted specification

Upgrade `scripts/formal_tools.py research`; preserve lexical JSON fields and AND/OR semantics. Add `--mode deep|hybrid|lexical` (deep after acceptance), a 120-second budget, full corpus source/type/proof indexing, local embeddings/reranking, and three-round reasoning with up to eight queries per round. Use SQLite plus bounded FAISS shards. All inference local; one shared worker. Return evidence-linked ideas, obligations, freshness, and partial results. No full Lean builds; one foreground Lean process per agent.

## Implementation work

- [ ] Compatibility and versioned real-corpus benchmark fixtures.
- [ ] Full source inventory, source chunks, compiler extraction, provenance, incremental index.
- [ ] Local Qwen embedding/reranking and MLX generation runtime, explicit setup, offline worker.
- [ ] Hybrid retrieval, method enrichment, iterative premise search, caching and deadlines.
- [ ] Existing command integration and operator documentation.
- [ ] Regression, integration, offline, cancellation and retrieval acceptance audits.
- [ ] Publish measured report and switch default only after release gates pass.

## Working ownership

Main agent: `scripts/lean_research_corpus.py`, `scripts/lean_research_engine.py`, existing CLI integration, corresponding tests and operator documentation.
Delegated scopes recorded in agent assignments: compiler exporter, runtime/setup, benchmark fixtures/evaluator. No overlapping writes.

## Evidence and decisions

- Existing lexical schema indexes names/modules/docs, not statements or proof bodies.
- RH frontier exporter excludes explicit data and unnamed proposition binders; a general exporter must not reuse those exclusions.
- LeanExplore reviewed revision: `6b25f8632cc3387cf85f7730375a690a1f1dfb79` (Apache-2.0).
- LeanSearch v2 reviewed revision: `94f4888cbaf9f4322535755f86cbac690ec18080` (Apache-2.0).
- Target: M3 Pro, 18 GiB RAM; Python runtime via uv; Qwen 0.6B embedding/reranker, MLX Qwen3-4B-Instruct-2507 4-bit generation.
- No performance improvement claimed before benchmarks. Selberg proof remains a separate unfinished mathematical goal.

## Log

- 2026-09-09 — implementation authorized; read current search schema, callers, tests and exporter before changes.
