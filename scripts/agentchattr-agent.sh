#!/usr/bin/env sh
set -eu

if [ "$#" -lt 1 ]; then
  printf '%s\n' "Usage: scripts/agentchattr-agent.sh <agent> [agent-args...]" >&2
  exit 1
fi

AGENT_NAME="$1"
shift

. "$(dirname "$0")/agentchattr-env.sh"

agentchattr_start_server_background

cd "$AGENTCHATTR_APP_ROOT"
printf 'Launching %s with project-local agentchattr at %s\n' "$AGENT_NAME" "http://127.0.0.1:$AGENTCHATTR_PORT"

if [ "$#" -gt 0 ]; then
  exec .venv/bin/python wrapper.py "$AGENT_NAME" \
    --data-dir "$AGENTCHATTR_DATA_DIR" \
    --upload-dir "$AGENTCHATTR_UPLOAD_DIR" \
    --port "$AGENTCHATTR_PORT" \
    --mcp-http-port "$AGENTCHATTR_MCP_HTTP_PORT" \
    --mcp-sse-port "$AGENTCHATTR_MCP_SSE_PORT" \
    -- "$@"
fi

exec .venv/bin/python wrapper.py "$AGENT_NAME" \
  --data-dir "$AGENTCHATTR_DATA_DIR" \
  --upload-dir "$AGENTCHATTR_UPLOAD_DIR" \
  --port "$AGENTCHATTR_PORT" \
  --mcp-http-port "$AGENTCHATTR_MCP_HTTP_PORT" \
  --mcp-sse-port "$AGENTCHATTR_MCP_SSE_PORT"
