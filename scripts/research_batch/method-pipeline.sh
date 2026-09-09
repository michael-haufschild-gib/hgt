#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mark() { printf '{"status":"%s"}\n' "$1" > pipeline.json.tmp; mv pipeline.json.tmp pipeline.json; }
trap 'mark failed' ERR
mkdir -p /workspace/lean-method-vectors
mark generation
.venv/bin/python -u -m research_batch.method_runner --bundle . --output results
mark embedding
/workspace/lean-embedding/.venv/bin/python -u -m research_batch.method_vectors \
  --method-bundle /workspace/lean-methods --method-results /workspace/lean-methods/results \
  --embedding-template /workspace/lean-embedding --destination /workspace/lean-method-vectors
mark complete
