# Local Lean research runtime

One supervisor per canonical corpus cache, one inference child, no hosted API.
Target: Apple M3 Pro / 18 GiB. Setup is explicit; all calls are offline. The
runtime serves retrieval: an embedder and a reranker, warm together in one
child. No text-generation model is pinned. The main corpus/engine/CLI can import the public client without
installing any inference dependencies in their parent Python.

## Start, restart and stop

From the repository root:

```sh
./launch.sh
./launch.sh --restart
./launch.sh --stop
```

These manage Qdrant, the shared inference worker, automatic corpus indexing and
unfinished local GPU-result receivers. New/edited/deleted sources are handled
incrementally, in RHTower → HTGeometry → remaining-corpus order. Remote GPU jobs
continue independently. Services continue after closing Codex while the Mac is awake.

SQLite holds source metadata, lexical search and a durable Qdrant update queue.
Qdrant serves vector queries. Bounded FAISS files remain as the audited vector
archive for reuse, interrupted imports and recovery; searches do not scan them.
Qdrant is bound to localhost, capped at 5 GiB, with cold original vectors and
pinned int8 vectors. Its image is pinned in `scripts/lean_research_qdrant.py`.

## Setup and verification

From repository root:

```sh
python3 scripts/lean_research_setup.py
scripts/research_runtime/.venv/bin/python scripts/lean_research_setup.py --verify
scripts/research_runtime/.venv/bin/python scripts/lean_research_setup.py --smoke
scripts/research_runtime/.venv/bin/python scripts/lean_research_setup.py --embedding-smoke
python3 scripts/lean_research_setup.py --status
scripts/research_runtime/.venv/bin/python -m unittest scripts.tests.test_lean_research_runtime -q
```

Setup runs `uv sync --project scripts/research_runtime --python 3.12 --locked`,
then downloads the immutable model revisions in `models.json` with two
file transfers at most. All subprocesses remain foreground-owned; interruption
terminates/reaps only the spawned setup process group. It never runs Lean.
`--env-only` installs just Python/dependencies. `--verify` hashes every manifested
root model/tokenizer artifact offline. Unused SentenceTransformers submodules
are excluded. `--smoke` runs actual embeddings, ordered relevance scores, and
generation when a model is pinned, without downloads. Missing installation is an error, not an
implicit setup trigger. Model/runtime libraries are imported only in the
inference child (or the explicitly selected setup/smoke commands).

Python: `scripts/research_runtime/.venv/bin/python` (3.12).
Default corpus cache: `formal/.lake/hgt-research/discovery-1`.
Model snapshots and installation manifest: `<corpus-cache>/runtime/`.
Use `--cache-dir PATH` consistently for a custom corpus cache. All agents must
use the same resolved corpus cache to share its worker. `runtime_python(root)`
returns the dedicated interpreter path without installing/starting anything.
Neither `uv run` nor an install-capable launcher occurs on the inference path.

The cache manifest contains snapshot file hashes and the runtime fingerprint.
A missing/truncated snapshot or changed pins makes status unavailable. Cheap
status checks file sizes and required artifacts; `--verify` detects same-size
corruption. Rerun explicit setup after updating pins or an incomplete download.
`uv.lock` is committed; environment and model weights are ignored/generated.

## Integration API

```python
from pathlib import Path
import time
from lean_research_runtime import (
    RuntimeClient, RuntimeDeadline, RuntimeUnavailable, runtime_python,
)

root = Path('/path/to/hgt')
python = runtime_python(root)  # use for CLI child engine and FAISS
cache_dir = root / 'formal/.lake/hgt-research/discovery-1'
with RuntimeClient(cache_dir) as client:
    status = client.status()  # bounded probe; never starts/downloads models
    deadline = time.monotonic() + 120
    queries = client.embed(['a spectral gap implies coercivity'], query=True,
                           deadline=deadline)
    documents = client.embed(['theorem ...'], deadline=deadline)
    scores = client.rerank('spectral gap', ['theorem ...'], deadline=deadline)
    explanation = client.generate('Explain this Lean proof: ...',
                                  deadline=deadline, max_tokens=1024)
    enriched = client.embed(['proof mechanism ...'], deadline=deadline,
                            priority='enrichment')
```

Signatures:

```python
RuntimeClient(cache_dir: Path)
.status() -> dict
.embed(texts: list[str], *, query: bool = False, deadline: float,
       priority: str = 'interactive') -> list[list[float]]
.rerank(query: str, documents: list[str], *, deadline: float,
        priority: str = 'interactive') -> list[float]
.generate(prompt: str, *, deadline: float, max_tokens: int = 1024,
          priority: str = 'interactive') -> str
.close() -> None
runtime_python(root: Path) -> Path
```

`deadline` is absolute `time.monotonic()`, shared across all stages; never a
relative timeout or wall clock. Invalid/beyond-limit arguments raise ValueError.
The client keeps this end-to-end deadline locally and sends the remaining duration
over the socket. Protocol 2 rebases it onto the worker's clock: macOS Python 3.9
can use a process-local clock origin, unlike the dedicated Python 3.12 worker.
`RuntimeDeadline` means the request expired. `RuntimeUnavailable` means missing
setup, queue saturation, cancellation, transport failure, or a model failure.
`generate` raises it unconditionally unless a generation model is pinned, which
it is not by default: this runtime serves retrieval. Empty embed/rerank batches
return `[]` after validation. Results preserve input order; embeddings are
768-dimensional L2-normalized float lists; reranker scores are yes probabilities
in [0,1]. No silent partial batches are returned.

`status()` exposes `available`/`ready` (verified installation, not GPU execution
proof), `running`, interpreter, per-role pinned repo/revision, installed/loaded,
actual `device`, `dtype`, and `fallback_reason` after inference. Before first use,
device is null. `last_devices` is explicitly historical after child replacement.
One `<role>_model_version` per pinned role is a stable repo@revision plus
configuration/lock fingerprint string, suitable for embedding cache validity. `fingerprints.models` and
`fingerprints.runtime` expose separate hashes. Do not hash the entire status for
cache keys: PID, queue, loaded models and devices are operational fields.

## Bounds, scheduling and cancellation

- 32 accepted connections; bounded 2 MiB framed JSON; 64 texts per request;
  32768 characters per text and 262144 characters total. At most 600 seconds
  until deadline. Admission saturation raises RuntimeUnavailable promptly.
- Embedding batches are length-sorted under a padded-token budget, right padded,
  and mean pooled over the attention mask: EmbeddingGemma pools the mean, so the
  mask is load-bearing. Query and document sides take different task prefixes.
  Only the text tower is loaded (271M of 740M); the audio tower has no SDPA
  kernel, so building it fails the load outright.
  Reranking: one text on MPS, four on CPU, left padding. Both cap at
  2048 tokens per text/pair. Truncation applies
  to embedding text or reranker body; reranker prefix/suffix always survive.
- Generation, only if a model is pinned: 8192 tokens including chat template and requested output;
  1–2048 output tokens; 256-token prefill chunks; deterministic greedy sampling.
- Interactive work precedes enrichment in the queue and never cancels it:
  killing indexing to serve a query starved indexing outright once several
  agents searched continuously. Indexing requests are small, so a query waits
  well under a second behind one. Interactive calls do not preempt each other.
- Supervisor I/O (including child IPC) is nonblocking, polled every 20ms.
  Client deadlines include startup, queueing, tokenization, loading and compute.
  Closing a request socket cancels it. `client.close()` cancels only that
  client's calls, including from another thread. KeyboardInterrupt unwinds the
  owning socket; other clients stay connected. Client waits do not wait for
  model loading or a stuck kernel after deadline.
- The search child holds the embedder and reranker together and stays warm for
  the life of the supervisor. Cancellation kills/reaps only the supervisor's
  current inference child, before starting another. No process-name searches or unrelated PID kills.
  SIGTERM/SIGINT of supervisor reaps its child; a child watches its parent's
  lifetime. A shared supervisor outlives clients and exits after five idle
  minutes.
- Socket paths are shortened hashes under a private, owned `/tmp` directory;
  socket permissions 0600, directory 0700. A lifetime flock prevents duplicate
  supervisors and protects stale-socket cleanup. No TCP listener, remote plugin,
  telemetry, cloud key, or remote inference provider is configured.

## Model and runtime sources

These are primary sources inspected for the implemented APIs; installed versions
are pinned in `pyproject.toml` and transitively locked in `uv.lock`.

- [EmbeddingGemma 2 card](https://huggingface.co/google/embeddinggemma-2/blob/914f7f89142e33e77833254d9c9b90c3cef7303b/README.md):
  asymmetric task prefixes (`task: search result | query:` against
  `title: none | text:`), mean pooling with the prompt included, 768 dimensions
  via Matryoshka, L2 norm, bfloat16 recommended and float16 warned against.
- [EmbeddingGemma 2 text model](https://github.com/huggingface/transformers/blob/v5.20.2/src/transformers/models/embedding_gemma2/modeling_embedding_gemma2.py):
  `EmbeddingGemma2TextModel` applies `embedding_projection` per token, which
  upstream notes is equivalent to projecting after the mean pool, and returns
  the projected state as `last_hidden_state`.
- [Qwen reranker card](https://huggingface.co/Qwen/Qwen3-Reranker-0.6B/blob/e61197ed45024b0ed8a2d74b80b4d909f1255473/README.md):
  exact system/user/assistant/closed-think wrapper, separate prefix/body/suffix
  tokenization, final-position no/yes logits, normalized yes probability.
- [Transformers Qwen3 implementation](https://github.com/huggingface/transformers/blob/v5.20.2/src/transformers/models/qwen3/modeling_qwen3.py):
  `logits_to_keep=1` avoids allocating vocabulary logits for every input token.
- [PyTorch MPS](https://docs.pytorch.org/docs/stable/notes/mps.html):
  explicit availability check and device transfer. Search uses float32 on MPS:
  target-machine probes found non-finite mixed-length left-padded batches in
  float16, bfloat16 and float32. The embedder additionally uses eager attention
  on MPS, because SDPA there returns non-finite values for this model whenever a
  batch carries real padding; the probe needs MPS and padding and sdpa together
  to reproduce, and CPU is unaffected, so sdpa stays where it is correct.
  Unpadded per-text reranking avoids the same kernel path. CPU float32 fallback
  is explicit and reported; automatic hidden per-operator MPS fallback is
  disabled. Finite output is checked.
- [Transformers offline mode](https://huggingface.co/docs/transformers/v5.20.2/installation#offline-mode):
  forced offline flags before imports plus `local_files_only=True`. The child
  additionally denies INET socket creation, DNS resolution, and subprocess
  launch through an audit hook.
- [uv locking/sync](https://docs.astral.sh/uv/concepts/projects/sync/):
  dedicated project, Python 3.12, locked dependency installation.

Both upstream repository licenses, adaptation notices, revisions and source
hashes are in `licenses/`. No corpus, engine, CLI, or Lean source is modified by
this runtime implementation.

## Verified 2026-10-22

Retrieval-only: `models.json` pins an embedder and a reranker. No generation
model is installed, so `generate` raises RuntimeUnavailable by design.

Offline snapshot hashes verified for both roles. The smoke returned normalized
768-D embeddings and correct relevance ordering (0.9921975 versus 0.00004685);
both models ran on MPS float32 with no fallback. 367 tests pass.

The text tower loads at 271M parameters of the checkpoint's 740M: vision and
audio tower configs are nulled before loading, which is required rather than
merely economical, because `Gemma4AudioModel` has no SDPA kernel and building it
fails the load. A Lean statement against a natural-language goal, with the
asymmetric prefixes applied, scored cosine 0.82.

The isolated CPU/MPS probe passes at max absolute difference 1.94e-7 and
minimum cosine 0.9999998 on mixed-length 5000-character inputs, at 2.22
documents/second on MPS. The comparable Qwen figure on this probe was
0.66-1.15 documents/second.

Source extraction measures 50 files/second after batching the ~20 source
reference rows per declaration into one statement per file, which projects to
roughly 25 minutes for 75,595 files. Parsing alone accounts for 4.4 minutes of
that. No full-corpus retrieval-quality acceptance is claimed.
