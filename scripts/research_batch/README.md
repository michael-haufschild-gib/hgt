# Explicit B200 embedding bootstrap

This directory is copied into a self-contained corpus bundle. Upload that bundle,
not the repository, live SQLite database, SSH private key, or local virtualenv.
Normal `research` and background indexing continue locally.

## Pod settings

- One B200; public IP with TCP port 22 exposed.
- Runpod PyTorch image
  `runpod/pytorch:2.8.0-py3.11-cuda12.8.1-cudnn-devel-ubuntu22.04`.
  Verified linux/amd64 image digest:
  `sha256:cb154fcca15d1d6ce858cfa672b76505e30861ef981d28ec94bd44168767d853`.
- 30 GB container disk; 100 GB volume mounted at `/workspace`.
- Prefer at least 16 CPU threads for tokenization, 64 GB system RAM, fast upload/download.

Use Runpod's **SSH over exposed TCP** connection. Its basic proxy SSH does not
support SCP/SFTP. Add your public key to Runpod settings before creation, or
append it to `/root/.ssh/authorized_keys` in the web terminal (directory mode 700,
file mode 600). Preserve existing keys. No private key belongs on the pod.

## Prepare locally

From the repository, using the dedicated research Python:

```sh
scripts/research_runtime/.venv/bin/python scripts/lean_research_batch.py prepare --directory formal/.lake/hgt-research/discovery-1/runpod/b200-initial
scripts/research_runtime/.venv/bin/python scripts/lean_research_batch.py verify --bundle formal/.lake/hgt-research/discovery-1/runpod/b200-initial/bundle
```

Preparation saves one committed source snapshot outside the transferable bundle,
deduplicates exact text hashes, excludes hashes already cached by this model,
and writes compressed shards in RHTower → HTGeometry → rest order. All inventoried
file outcomes are included, including stale/pending/failed extraction. Full-file
Lean passages stay lexical; all other existing representations are eligible.
An incomplete snapshot read restarts; completed snapshots and input shards are
reused on retry. New source records after the snapshot remain local queue work,
or can be included in a later bundle. Source/compiler extraction and generated
method descriptions are separate work, not part of this GPU embedding job.

## Transfer and run

After setting `POD_HOST` and `POD_PORT` to the actual direct SSH endpoint:

```sh
ssh -p "$POD_PORT" -i ~/.ssh/id_ed25519 "root@$POD_HOST" 'mkdir -p /workspace/lean-embedding'
rsync -a --partial --progress -e "ssh -p $POD_PORT -i $HOME/.ssh/id_ed25519" formal/.lake/hgt-research/discovery-1/runpod/b200-initial/bundle/ "root@$POD_HOST:/workspace/lean-embedding/"
```

Keep SSH host-key verification enabled. On the pod:

```sh
cd /workspace/lean-embedding
bash setup.sh
bash run.sh --max-shards 3
```

Setup is the only package-download step; model weights are already bundled and
all inference is offline. The pilot first compares 96 real-source vectors and
four queries against saved local float32 results. It checks unit norms, cosine
agreement, and top-20 overlap with both local and CUDA queries. This is numerical
compatibility, not a claim of retrieval quality. If BF16 fails, use a new output
directory with `bash run.sh --dtype float32 --output results-f32 --max-shards 3`.
Do not bypass the compatibility gate or mix output directories/dtypes.

Each completed pilot shard is part of the full run. Resume without repeating it:

```sh
nohup bash run.sh > embedding.log 2>&1 < /dev/null &
echo $! > embedding.pid
```

One Python GPU process owns `results/runner.lock`. Length-based batching defaults
to 65,536 padded tokens and at most 256 texts. OOM halves batch size and retries;
single-input OOM fails explicitly. Increase `--token-budget` / `--max-batch` only
after measuring actual pilot VRAM and throughput. Reported ETA extrapolates the
completed mix; different lengths in later folders can change it.

`results/progress.json` reports vectors, tokens, latency and peak VRAM.
`results/run.json` reports completion. Stop using the recorded owned PID; restart
the same command to resume. A corrupt completed shard fails checksum validation;
remove only that shard's `.done.json` marker after diagnosis to regenerate it.

## Download and import incrementally

On the Mac, while the GPU can continue writing other shards:

```sh
rsync -a --partial --progress -e "ssh -p $POD_PORT -i $HOME/.ssh/id_ed25519" "root@$POD_HOST:/workspace/lean-embedding/results/" formal/.lake/hgt-research/discovery-1/runpod/b200-initial/results/
scripts/research_runtime/.venv/bin/python scripts/lean_research_batch.py import --bundle formal/.lake/hgt-research/discovery-1/runpod/b200-initial/bundle --output formal/.lake/hgt-research/discovery-1/runpod/b200-initial/results --budget-seconds 600
```

Download again if a completion marker arrived before its data. Import verifies
the reference audit itself, model/preprocessing identity, source order and file
checksums. It joins hashes to current local documents, rechecks them in each
publication transaction, and skips edited/deleted/already-published records.
Unchanged content survives moved document IDs. Only completed shards publish;
reruns are idempotent. Import briefly reserves local maintenance locks; searches
keep reading committed generations. If another maintenance job holds the locks,
retry when it finishes. No workers are killed.

Local FAISS is isolated from Torch to avoid the known macOS OpenMP crash.
Keep the pod until all result files are downloaded and the local import is
verified. New and changed content continues through the existing local indexer.

Sources: [Runpod image](https://hub.docker.com/r/runpod/pytorch/tags),
[Runpod full SSH](https://docs.runpod.io/pods/configuration/use-ssh),
[Qwen embedding reference](https://huggingface.co/Qwen/Qwen3-Embedding-0.6B).
