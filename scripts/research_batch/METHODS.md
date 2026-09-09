# GPU proof-method bootstrap

This opt-in batch runs after the initial embedding bootstrap. Normal research
search stays local. One GPU pipeline generates method descriptions, then embeds
their exact local search representation with the audited embedding runtime.
The Mac imports completed output incrementally. No Lean execution is involved.

## Prepared job

- Local job: `formal/.lake/hgt-research/discovery-1/runpod/blackwell-methods`.
- Pod: `/workspace/lean-methods`; vectors: `/workspace/lean-method-vectors`.
- Generation: `Qwen/Qwen3-4B-Instruct-2507`, revision
  `cdbee75f17c01a7cc42f958dc650907174af0554`, BF16, vLLM 0.29.0.
- Exact installed packages: `method-requirements.txt`. Model files were checked
  against the pinned Hugging Face Git/LFS hashes; `model-files.json` records SHA256.
- Generation virtualenv: `/workspace/lean-methods/.venv`. It includes CUDA 13
  wheels and a compiler supporting B300. The runner selects that compiler and
  its `ninja`; it must not pick `/usr/local/cuda` from the 12.8 container image.
- Embedding virtualenv: existing `/workspace/lean-embedding/.venv`, kept separate.

Explicit setup installs the pinned requirements and downloads the pinned model
to `model/`. Generation forces Hugging Face offline mode and disables usage
telemetry. No external model endpoint is used. No runtime/model download occurs
in the local search command.

## Prepare, pilot, resume

```sh
scripts/research_runtime/.venv/bin/python scripts/lean_research_method_batch.py prepare \
  --directory formal/.lake/hgt-research/discovery-1/runpod/blackwell-methods \
  --model-files formal/.lake/hgt-research/discovery-1/runpod/blackwell-methods/model-files.json
```

Transfer `bundle/` into `/workspace/lean-methods` using the existing verified SSH
endpoint. It contains source records, source-file outcomes, code checksums and a
manifest. The corpus database, keys and Mac virtualenv are not transferred.

On the pod, from `/workspace/lean-methods`:

```sh
.venv/bin/python -u -m research_batch.method_runner --bundle . --output results --max-shards 4
bash method-pipeline.sh
```

The pilot produces real reusable shards. Check every pilot output mechanically
with `checked_output`, inspect validation failures, and measure throughput before
the full run. Once outputs exist, preserve the manifest and referenced code.
Each declaration and every code-containing proof chunk has an explicit outcome.
Masking covers the entire proof before splitting, including comments crossing
chunk boundaries. JSON/citation failures receive one retry. Failed descriptions
are retained as failed records, never silently accepted.

The pipeline resumes completed generation shards, builds deduplicated method
embedding inputs, then runs the existing embedding runner and compatibility
audit. The existing CUDA embedding environment and model remain unchanged.
Use an owned process group and save its PID as `pipeline.pid` for detached runs.
`pipeline.json`, `results/progress.json`, and `results/run.json` report progress.

## Local transfer and publication

`connection.json` supplies `host`, `port`, `user`, `identity_file`,
`remote_directory`, and `remote_vector_directory`. Keep strict SSH host-key
checking enabled. Run the dedicated Python by its virtualenv path; resolving
that executable symlink selects the base interpreter instead.

```sh
scripts/research_runtime/.venv/bin/python scripts/lean_research_method_sync.py \
  --root "$PWD" \
  --directory formal/.lake/hgt-research/discovery-1/runpod/blackwell-methods
```

The finite worker downloads/imports every two minutes and exits after both
descriptions and their vectors are verified locally. It retries maintenance and
transport contention, and fails explicitly on corrupt artifacts or a failed GPU
pipeline. Restarting retains published descriptions and completed shard receipts.
The Mac must be awake for import; the GPU pipeline can continue independently.

Publication revalidates source hashes, full chunk coverage, JSON and citation
lines. Changed/deleted source files and their transitive import dependents are
excluded; unindexed disk edits are checked too. Imported descriptions retain the
GPU producer identity, and local indexing recognizes valid descriptions from
that producer without regenerating them solely due to a different runtime.
Changed sources still invalidate them normally.

Descriptions become keyword-searchable when imported. Their vector stage makes
the same descriptions semantically searchable. Generated interpretations and
transfer suggestions are not Lean-derived facts or evidence of applicability.
The held-out retrieval-quality release gates remain separate from this bootstrap.

Sources: [vLLM offline batches](https://docs.vllm.ai/en/latest/getting_started/quickstart/#offline-batched-inference),
[Qwen model](https://huggingface.co/Qwen/Qwen3-4B-Instruct-2507),
[NVIDIA CUDA installation](https://docs.nvidia.com/cuda/cuda-installation-guide-linux/).
