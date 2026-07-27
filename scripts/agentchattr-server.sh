#!/usr/bin/env sh
set -eu

AGENTCHATTR_SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export AGENTCHATTR_SCRIPT_DIR
. "$AGENTCHATTR_SCRIPT_DIR/agentchattr-env.sh"

agentchattr_ensure_venv

cd "$AGENTCHATTR_APP_ROOT"
printf '%s\n' "Starting agentchattr for this project:"
printf '  Web UI: %s\n' "http://127.0.0.1:$AGENTCHATTR_PORT"
printf '  MCP:    %s\n' "http://127.0.0.1:$AGENTCHATTR_MCP_HTTP_PORT/mcp"
printf '  Data:   %s\n' "$AGENTCHATTR_DATA_DIR"

exec .venv/bin/python run.py \
  --data-dir "$AGENTCHATTR_DATA_DIR" \
  --upload-dir "$AGENTCHATTR_UPLOAD_DIR" \
  --port "$AGENTCHATTR_PORT" \
  --mcp-http-port "$AGENTCHATTR_MCP_HTTP_PORT" \
  --mcp-sse-port "$AGENTCHATTR_MCP_SSE_PORT" \
  "$@"
