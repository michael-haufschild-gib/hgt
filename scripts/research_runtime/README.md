# Local Lean research runtime

One supervisor per canonical corpus cache, one inference child, no hosted API.
Target: Apple M3 Pro / 18 GiB. Setup is explicit; all search and generation calls
are offline. The main corpus/engine/CLI can import the public client without
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
then downloads the three immutable model revisions in `models.json` with two
file transfers at most. All subprocesses remain foreground-owned; interruption
terminates/reaps only the spawned setup process group. It never runs Lean.
`--env-only` installs just Python/dependencies. `--verify` hashes every manifested
root model/tokenizer artifact offline. Unused SentenceTransformers submodules
are excluded. `--smoke` runs actual embeddings, ordered relevance scores, and
MLX generation without downloads. Missing installation is an error, not an
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
setup, queue saturation, cancellation, preempted enrichment, transport failure,
or a model failure. Empty embed/rerank batches return `[]` after validation.
Results preserve input order; embeddings are 1024-dimensional L2-normalized
float lists; reranker scores are yes probabilities in [0,1]. No silent partial
batches or partial generation are returned.

`status()` exposes `available`/`ready` (verified installation, not GPU execution
proof), `running`, interpreter, per-role pinned repo/revision, installed/loaded,
actual `device`, `dtype`, and `fallback_reason` after inference. Before first use,
device is null. `last_devices` is explicitly historical after child replacement.
`embedding_model_version`, `reranker_model_version`, `generation_model_version`
are stable repo@revision plus configuration/lock fingerprint strings, suitable
for embedding/method cache validity. `fingerprints.models` and
`fingerprints.runtime` expose separate hashes. Do not hash the entire status for
cache keys: PID, queue, loaded models and devices are operational fields.

## Bounds, scheduling and cancellation

- 32 accepted connections; bounded 2 MiB framed JSON; 64 texts per request;
  32768 characters per text and 262144 characters total. At most 600 seconds
  until deadline. Admission saturation raises RuntimeUnavailable promptly.
- Embedding microbatches: four texts, right padding and explicit last-nonpad
  pooling. Reranking: one text on MPS, four on CPU, left padding. Both cap at
  2048 tokens per text/pair. Truncation applies
  to embedding text or reranker body; reranker prefix/suffix always survive.
- Generation: 8192 tokens including chat template and requested output;
  1–2048 output tokens; 256-token prefill chunks; deterministic greedy sampling.
- Interactive work precedes enrichment in the queue. Interactive arrival
  preempts active enrichment, returning RuntimeUnavailable to that enrichment
  caller so it can retry later. Interactive calls do not preempt each other.
- Supervisor I/O (including child IPC) is nonblocking, polled every 20ms.
  Client deadlines include startup, queueing, tokenization, loading and compute.
  Closing a request socket cancels it. `client.close()` cancels only that
  client's calls, including from another thread. KeyboardInterrupt unwinds the
  owning socket; other clients stay connected. Client waits do not wait for
  model loading or a stuck kernel after deadline.
- Cancellation kills/reaps only the supervisor's current inference child,
  before starting another. No process-name searches or unrelated PID kills.
  SIGTERM/SIGINT of supervisor reaps its child; a child watches its parent's
  lifetime. A shared supervisor outlives clients and exits after five idle
  minutes. Torch search and MLX generation use different child lifetimes,
  releasing model/framework allocations on switching. Search models remain
  warm together inside the search child.
- Socket paths are shortened hashes under a private, owned `/tmp` directory;
  socket permissions 0600, directory 0700. A lifetime flock prevents duplicate
  supervisors and protects stale-socket cleanup. No TCP listener, remote plugin,
  telemetry, cloud key, or remote inference provider is configured.

## Model and runtime sources

These are primary sources inspected for the implemented APIs; installed versions
are pinned in `pyproject.toml` and transitively locked in `uv.lock`.

- [Qwen embedding card](https://huggingface.co/Qwen/Qwen3-Embedding-0.6B/blob/97b0c614be4d77ee51c0cef4e5f07c00f9eb65b3/README.md):
  query instruction, plain documents, last-token/nonpad pooling, L2 norm.
- [Qwen reranker card](https://huggingface.co/Qwen/Qwen3-Reranker-0.6B/blob/e61197ed45024b0ed8a2d74b80b4d909f1255473/README.md):
  exact system/user/assistant/closed-think wrapper, separate prefix/body/suffix
  tokenization, final-position no/yes logits, normalized yes probability.
- [Transformers Qwen3 4.56.2 implementation](https://github.com/huggingface/transformers/blob/v4.56.2/src/transformers/models/qwen3/modeling_qwen3.py):
  `logits_to_keep=1` avoids allocating vocabulary logits for every input token.
- [PyTorch MPS](https://docs.pytorch.org/docs/stable/notes/mps.html):
  explicit availability check and device transfer. Search uses float32 on MPS:
  target-machine probes found non-finite mixed-length left-padded batches in
  float16, bfloat16 and float32. Right-padded embedding batches and unpadded
  per-text reranking avoid that kernel path. CPU float32 fallback is explicit
  and reported; automatic
  hidden per-operator MPS fallback is disabled. Finite output is checked.
- [MLX model card](https://huggingface.co/mlx-community/Qwen3-4B-Instruct-2507-4bit/blob/50d427756c6b1b2fe0c0a10f67fbda1fc8e82c1b/README.md),
  [MLX-LM load](https://github.com/ml-explore/mlx-lm/blob/v0.28.2/mlx_lm/utils.py),
  [stream generation](https://github.com/ml-explore/mlx-lm/blob/v0.28.2/mlx_lm/generate.py):
  existing local path, local tokenizer settings, tokenized chat template,
  `stream_generate` and greedy `make_sampler(temp=0.0)`.
- [Transformers offline mode](https://huggingface.co/docs/transformers/v4.56.2/installation#offline-mode):
  forced offline flags before imports plus `local_files_only=True`. MLX only
  receives an existing verified absolute path. Child additionally denies INET
  socket creation, DNS resolution, and subprocess launch through an audit hook.
- [uv locking/sync](https://docs.astral.sh/uv/concepts/projects/sync/):
  dedicated project, Python 3.12, locked dependency installation.

Both upstream repository licenses, adaptation notices, revisions and source
hashes are in `licenses/`. No corpus, engine, CLI, or Lean source is modified by
this runtime implementation.

## Verified 2026-09-09

26 runtime tests passed, including actual local-tokenizer parity with Qwen's
published reranker procedure. The three-model smoke returned normalized 1024-D
embeddings, correct relevance ordering (0.992197 versus 0.00004685), and MLX
output `local`. Embedding/reranker ran on MPS float32 with no fallback;
generation ran on Metal. Dependency lock and downloaded weight hashes passed.

Right-padded batches of four passed CPU reference parity on mixed-length,
roughly 5000-character inputs: max absolute difference 3.50e-7, minimum cosine
0.99999988. The 32-document shared-client probe processed 153424 characters in
48.27 seconds including startup/loading (0.663 documents/second). Warm direct
probes ranged 27.79–43.29 seconds (0.74–1.15 documents/second). These synthetic
Lean-like texts are capped at 2048 tokens; real chunk lengths and contention
change throughput. At comparable lengths, 919k chunks imply roughly 9–16 days
of serial embedding, before interruptions or other index work. Use resumable
batches; no full-corpus performance/quality acceptance is claimed.

Machine-readable evidence is in `validation.json`. Reproduce the isolated,
180-second bounded CPU/MPS parity probe with:

```sh
PYTHONPATH=scripts scripts/research_runtime/.venv/bin/python -m research_runtime.probe_embedding
```

Only run that explicit probe when no other model work is planned: it owns an
additional temporary model process for comparison. Normal searches/enrichment
always use the shared worker. The client throughput probe uses the worker:

```sh
scripts/research_runtime/.venv/bin/python scripts/lean_research_setup.py --embedding-smoke
```
