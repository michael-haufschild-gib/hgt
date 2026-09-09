# Attribution and changes

LeanExplore, Copyright 2025 LeanExplore Contributors, Apache License 2.0.
Repository: https://github.com/justincasher/lean-explore
Reviewed revision: `6b25f8632cc3387cf85f7730375a690a1f1dfb79`.
Original license retained verbatim in `LeanExplore.LICENSE`.

This project's local inference adapters reuse LeanExplore's small batch adapter
structure and distinction between query instructions and plain documents.
Changes: lazy/offline loading, pinned local snapshots, private Unix IPC, bounded
serialized execution, process cancellation, explicit MPS float32/CPU selection,
and Qwen's official yes/no reranker wrapper and last-position logit scoring.
LeanExplore's reviewed reranker uses true/false logits, lacks that wrapper, and
selects CUDA/CPU only. Those behaviors are not carried into this adapter.
The main research engine adapts LeanExplore's reciprocal-rank fusion scoring
formula to local candidate sets and chunk deduplication. Full upstream runtime,
hosted search, plugin, extraction stack, and dependencies are not installed.

LeanSearch v2, FrenzyMath / upstream contributors, Apache License 2.0.
Repository: https://github.com/frenzymath/LeanSearch-v2
Reviewed revision: `94f4888cbaf9f4322535755f86cbac690ec18080`.
Original license retained verbatim in `LeanSearch-v2.LICENSE`; its copyright
appendix contains placeholders, retained without inventing a copyright year.
The main research engine adapts `src/leansearchv2/reasoning/run.py`'s iterative
decompose/retrieve/filter/judge design, with local models, deadlines, explicit
unfinished stages, and evidence-linked candidates. LeanSearch v2's ranking there
uses discounted-rank aggregation; the project's RRF formula is attributed to
LeanExplore separately. No full upstream package or hosted inference is used.
No benchmark datasets or separately licensed submodules are copied here.

`upstreams.json` records exact revisions, URLs, SPDX IDs, original license
SHA-256 digests, and SHA-256 digests of inspected source references. No upstream
NOTICE file was present in either pinned repository tree. Non-executable `.txt`
copies under `../upstream/` preserve the inspected references for audits.

Qwen3-Embedding-0.6B and Qwen3-Reranker-0.6B: Qwen, Apache-2.0 as declared in
both pinned model cards. Qwen3-4B-Instruct-2507 MLX 4-bit conversion:
mlx-community, based on Qwen/Qwen3-4B-Instruct-2507, Apache-2.0 as declared in
its pinned model card. Exact model repository IDs and immutable revisions are
in `../models.json`. The setup manifest records every root runtime artifact's SHA-256.
Model cards ship with each local snapshot; no model weights are committed.

Dependencies remain upstream packages installed from the hash-locked `uv.lock`.
Their distributions retain their own license files. PyTorch: BSD-3-Clause;
Transformers/Hugging Face Hub: Apache-2.0; MLX/MLX-LM: MIT; NumPy: BSD-3-Clause;
FAISS: MIT. See installed distribution metadata for their full notices and
transitive dependency licenses.

RRF reference: LeanExplore `src/lean_explore/search/scoring.py`, function
`reciprocal_rank_fusion` at the pinned revision. Reference source is included
as `../upstream/LeanExplore-scoring.py.txt` with its recorded digest.
