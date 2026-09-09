#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export CUDA_VISIBLE_DEVICES=0
export HF_HUB_OFFLINE=1 TRANSFORMERS_OFFLINE=1 HF_HUB_DISABLE_TELEMETRY=1
export TOKENIZERS_PARALLELISM=true
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-8}"
exec .venv/bin/python -u -m research_batch.runner --bundle . --output results "$@"
