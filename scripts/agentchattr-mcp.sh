#!/usr/bin/env sh
# MCP stdio entry point for agentchattr, used by .mcp.json.
#
# Guarantees the project-local agentchattr server is listening, then relays
# JSON-RPC between the MCP client (stdin/stdout) and the server's
# streamable-HTTP endpoint.
#
# stdout is reserved for protocol frames — every message here goes to stderr.
set -eu

AGENTCHATTR_SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export AGENTCHATTR_SCRIPT_DIR
. "$AGENTCHATTR_SCRIPT_DIR/agentchattr-env.sh"

# Bootstrap the venv and start the server if it is not already up.
# Both are idempotent, so concurrent sessions are safe.
agentchattr_start_server_background >&2

AGENTCHATTR_MCP_URL="${AGENTCHATTR_MCP_URL:-http://127.0.0.1:$AGENTCHATTR_MCP_HTTP_PORT/mcp}"
export AGENTCHATTR_MCP_URL

exec "$AGENTCHATTR_APP_ROOT/.venv/bin/python" \
  "$AGENTCHATTR_SCRIPT_DIR/agentchattr_mcp_stdio.py"
