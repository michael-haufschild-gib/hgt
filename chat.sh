#!/usr/bin/env sh
# Start the project-local agentchattr server (web UI + MCP endpoints).
# Works from any current working directory.
set -eu

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
exec "$SCRIPT_DIR/scripts/agentchattr-server.sh" "$@"
