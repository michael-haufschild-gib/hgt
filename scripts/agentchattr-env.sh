#!/usr/bin/env sh

AGENTCHATTR_PROJECT_ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
AGENTCHATTR_APP_ROOT="$AGENTCHATTR_PROJECT_ROOT/agentchattr"

AGENTCHATTR_PORT="${AGENTCHATTR_PORT:-18400}"
AGENTCHATTR_MCP_HTTP_PORT="${AGENTCHATTR_MCP_HTTP_PORT:-18420}"
AGENTCHATTR_MCP_SSE_PORT="${AGENTCHATTR_MCP_SSE_PORT:-18421}"
AGENTCHATTR_DATA_DIR="${AGENTCHATTR_DATA_DIR:-$AGENTCHATTR_PROJECT_ROOT/.agentchattr/data}"
AGENTCHATTR_UPLOAD_DIR="${AGENTCHATTR_UPLOAD_DIR:-$AGENTCHATTR_PROJECT_ROOT/.agentchattr/uploads}"
AGENTCHATTR_SERVER_LOG="${AGENTCHATTR_SERVER_LOG:-$AGENTCHATTR_PROJECT_ROOT/.agentchattr/server.log}"

export AGENTCHATTR_PORT
export AGENTCHATTR_MCP_HTTP_PORT
export AGENTCHATTR_MCP_SSE_PORT
export AGENTCHATTR_DATA_DIR
export AGENTCHATTR_UPLOAD_DIR

agentchattr_python_bin() {
  if command -v python3 >/dev/null 2>&1; then
    printf '%s\n' "python3"
    return 0
  fi

  if command -v python >/dev/null 2>&1; then
    printf '%s\n' "python"
    return 0
  fi

  printf '%s\n' "Python 3 is required but was not found on PATH." >&2
  return 1
}

agentchattr_ensure_app() {
  if [ ! -f "$AGENTCHATTR_APP_ROOT/run.py" ]; then
    printf '%s\n' "agentchattr is not installed at $AGENTCHATTR_APP_ROOT" >&2
    printf '%s\n' "Expected the local clone from https://github.com/bcurts/agentchattr." >&2
    exit 1
  fi
}

agentchattr_ensure_venv() {
  agentchattr_ensure_app
  mkdir -p "$AGENTCHATTR_DATA_DIR" "$AGENTCHATTR_UPLOAD_DIR"

  cd "$AGENTCHATTR_APP_ROOT"
  if [ -d ".venv" ] && [ ! -x ".venv/bin/python" ]; then
    rm -rf ".venv"
  fi

  if [ ! -x ".venv/bin/python" ]; then
    PYTHON_BIN="$(agentchattr_python_bin)"
    "$PYTHON_BIN" -m venv ".venv"
    .venv/bin/python -m pip install -q -r requirements.txt
  fi
}

agentchattr_is_server_running() {
  lsof -nP -iTCP:"$AGENTCHATTR_PORT" -sTCP:LISTEN >/dev/null 2>&1
}

agentchattr_start_server_background() {
  agentchattr_ensure_venv

  if agentchattr_is_server_running; then
    return 0
  fi

  cd "$AGENTCHATTR_APP_ROOT"
  nohup .venv/bin/python run.py \
    --data-dir "$AGENTCHATTR_DATA_DIR" \
    --upload-dir "$AGENTCHATTR_UPLOAD_DIR" \
    --port "$AGENTCHATTR_PORT" \
    --mcp-http-port "$AGENTCHATTR_MCP_HTTP_PORT" \
    --mcp-sse-port "$AGENTCHATTR_MCP_SSE_PORT" \
    > "$AGENTCHATTR_SERVER_LOG" 2>&1 &

  i=0
  while [ "$i" -lt 30 ]; do
    if agentchattr_is_server_running; then
      return 0
    fi
    sleep 0.5
    i=$((i + 1))
  done

  printf '%s\n' "agentchattr server did not start on port $AGENTCHATTR_PORT." >&2
  printf '%s\n' "See $AGENTCHATTR_SERVER_LOG for details." >&2
  return 1
}
