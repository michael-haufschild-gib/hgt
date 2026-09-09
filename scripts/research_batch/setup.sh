#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python - <<'PY'
import sys
assert sys.version_info[:2] == (3, 12), 'Prepared runtime targets the actual pod Python 3.12'
PY
# The selected Runpod template may have CUDA 12.8.1. Install the complete pinned
# CUDA 12.9 wheel runtime in isolation; never replace the template's environment.
python -m venv .venv
case "${1:-}" in
  '') LEAN_BATCH_PIP_FLAGS=(--no-index) ;;
  --download-runtime) LEAN_BATCH_PIP_FLAGS=(--extra-index-url https://download.pytorch.org/whl/cu129) ;;
  *) printf '%s\n' 'Usage: bash setup.sh [--download-runtime]' >&2; exit 2 ;;
esac
.venv/bin/python -m pip install "${LEAN_BATCH_PIP_FLAGS[@]}" --only-binary=:all: --find-links wheelhouse --require-hashes -r requirements-linux.lock
.venv/bin/python -m pip check
.venv/bin/python -m pip freeze > installed-packages.txt
.venv/bin/python - <<'PY'
import torch
from research_batch.runner import validate_cuda
assert torch.__version__ == '2.8.0+cu129', torch.__version__
validate_cuda(torch)
print(torch.cuda.get_device_name(0), torch.cuda.get_device_properties(0).total_memory)
# Execute a kernel: a nominally CUDA-enabled wheel is not sufficient.
x = torch.ones((32, 32), device='cuda', dtype=torch.bfloat16)
assert (x @ x).sum().item() == 32768
PY
printf '%s\n' 'Setup ready. bash run.sh --max-shards 3 runs the compatibility gate and resumable pilot.'
