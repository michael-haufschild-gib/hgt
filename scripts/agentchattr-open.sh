#!/usr/bin/env sh
set -eu

. "$(dirname "$0")/agentchattr-env.sh"

agentchattr_start_server_background

CHAT_URL="http://127.0.0.1:$AGENTCHATTR_PORT"
if command -v open >/dev/null 2>&1; then
  open "$CHAT_URL"
else
  printf '%s\n' "$CHAT_URL"
fi
