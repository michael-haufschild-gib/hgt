#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python - <<'PY'
import torch
assert torch.__version__.split('+')[0] == '2.8.0', torch.__version__
assert torch.version.cuda == '12.8', torch.version.cuda
assert torch.cuda.is_available(), 'CUDA unavailable'
assert torch.cuda.device_count() == 1, 'Select exactly one GPU'
assert torch.cuda.get_device_capability(0) >= (10, 0), 'Expected B200'
print(torch.cuda.get_device_name(0), torch.cuda.get_device_properties(0).total_memory)
# Execute a kernel: a nominally CUDA-enabled wheel is not sufficient.
x = torch.ones((32, 32), device='cuda', dtype=torch.bfloat16)
assert (x @ x).sum().item() == 32768
PY
python -m venv --system-site-packages .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -m pip check
.venv/bin/python -m pip freeze > installed-packages.txt
printf '%s\n' 'Setup ready. bash run.sh --max-shards 3 runs the compatibility gate and resumable pilot.'
