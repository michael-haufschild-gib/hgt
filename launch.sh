#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
PYTHON="$ROOT/scripts/research_runtime/.venv/bin/python"
if [[ ! -x "$PYTHON" ]]; then
  echo 'Research runtime missing. Run scripts/formal_tools.py research-setup first.' >&2
  exit 1
fi
exec "$PYTHON" "$ROOT/scripts/lean_research_services.py" "$@"
