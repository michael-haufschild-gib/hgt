#!/usr/bin/env sh
set -eu

AGENTCHATTR_SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export AGENTCHATTR_SCRIPT_DIR
. "$AGENTCHATTR_SCRIPT_DIR/agentchattr-env.sh"

agentchattr_start_server_background

CHAT_URL="http://127.0.0.1:$AGENTCHATTR_PORT"
if command -v open >/dev/null 2>&1; then
  open "$CHAT_URL"
else
  printf '%s\n' "$CHAT_URL"
fi
