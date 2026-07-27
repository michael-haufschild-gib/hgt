#!/usr/bin/env sh
# Shared environment + venv bootstrap for the project-local agentchattr install.
#
# Sourced by agentchattr-server.sh / -agent.sh / -open.sh.
#
# agentchattr needs Python 3.11+ (it imports `tomllib`, and uses PEP 604
# `X | None` annotations that are evaluated at import time). macOS ships
# /usr/bin/python3 3.9, so a bare `python3` lookup is not good enough — we
# probe candidate interpreters and pick the first one that is new enough.

# Entry scripts export AGENTCHATTR_SCRIPT_DIR (absolute) before sourcing this
# file; fall back to $0 for direct/legacy invocations.
AGENTCHATTR_SCRIPT_DIR="${AGENTCHATTR_SCRIPT_DIR:-$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)}"
AGENTCHATTR_PROJECT_ROOT="$(CDPATH= cd -- "$AGENTCHATTR_SCRIPT_DIR/.." && pwd)"
AGENTCHATTR_APP_ROOT="$AGENTCHATTR_PROJECT_ROOT/agentchattr"

AGENTCHATTR_PORT="${AGENTCHATTR_PORT:-18600}"
AGENTCHATTR_MCP_HTTP_PORT="${AGENTCHATTR_MCP_HTTP_PORT:-18620}"
AGENTCHATTR_MCP_SSE_PORT="${AGENTCHATTR_MCP_SSE_PORT:-18621}"
AGENTCHATTR_DATA_DIR="${AGENTCHATTR_DATA_DIR:-$AGENTCHATTR_PROJECT_ROOT/.agentchattr/data}"
AGENTCHATTR_UPLOAD_DIR="${AGENTCHATTR_UPLOAD_DIR:-$AGENTCHATTR_PROJECT_ROOT/.agentchattr/uploads}"
AGENTCHATTR_SERVER_LOG="${AGENTCHATTR_SERVER_LOG:-$AGENTCHATTR_PROJECT_ROOT/.agentchattr/server.log}"

# Minimum interpreter agentchattr supports.
AGENTCHATTR_PY_MIN_MAJOR=3
AGENTCHATTR_PY_MIN_MINOR=11

export AGENTCHATTR_PORT
export AGENTCHATTR_MCP_HTTP_PORT
export AGENTCHATTR_MCP_SSE_PORT
export AGENTCHATTR_DATA_DIR
export AGENTCHATTR_UPLOAD_DIR

# True if "$1" is an interpreter of at least the required version.
agentchattr_python_ok() {
  [ -n "${1:-}" ] || return 1
  "$1" -c "import sys; sys.exit(0 if sys.version_info[:2] >= ($AGENTCHATTR_PY_MIN_MAJOR, $AGENTCHATTR_PY_MIN_MINOR) else 1)" >/dev/null 2>&1
}

# Print the path of a usable interpreter, or fail with a helpful message.
agentchattr_python_bin() {
  # 1. Explicit override wins.
  if [ -n "${AGENTCHATTR_PYTHON:-}" ]; then
    if agentchattr_python_ok "$AGENTCHATTR_PYTHON"; then
      printf '%s\n' "$AGENTCHATTR_PYTHON"
      return 0
    fi
    printf '%s\n' "AGENTCHATTR_PYTHON=$AGENTCHATTR_PYTHON is not Python ${AGENTCHATTR_PY_MIN_MAJOR}.${AGENTCHATTR_PY_MIN_MINOR}+." >&2
    return 1
  fi

  # 2. Newest-first named versions, then the generic names.
  for candidate in python3.14 python3.13 python3.12 python3.11 python3 python; do
    resolved="$(command -v "$candidate" 2>/dev/null)" || continue
    if agentchattr_python_ok "$resolved"; then
      printf '%s\n' "$resolved"
      return 0
    fi
  done

  # 3. Common Homebrew locations that may not be on PATH.
  for candidate in \
    /opt/homebrew/bin/python3.14 /opt/homebrew/bin/python3.13 \
    /opt/homebrew/bin/python3.12 /opt/homebrew/bin/python3.11 \
    /usr/local/bin/python3.14 /usr/local/bin/python3.13 \
    /usr/local/bin/python3.12 /usr/local/bin/python3.11
  do
    if [ -x "$candidate" ] && agentchattr_python_ok "$candidate"; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done

  printf '%s\n' "agentchattr needs Python ${AGENTCHATTR_PY_MIN_MAJOR}.${AGENTCHATTR_PY_MIN_MINOR}+ (it imports 'tomllib'), but none was found." >&2
  printf '%s\n' "macOS ships Python 3.9 at /usr/bin/python3, which is too old." >&2
  printf '%s\n' "Install one, e.g.:  brew install python@3.12" >&2
  printf '%s\n' "Or point AGENTCHATTR_PYTHON at an existing 3.11+ interpreter." >&2
  return 1
}

agentchattr_ensure_app() {
  if [ ! -f "$AGENTCHATTR_APP_ROOT/run.py" ]; then
    printf '%s\n' "agentchattr is not installed at $AGENTCHATTR_APP_ROOT" >&2
    printf '%s\n' "Expected the local clone from https://github.com/bcurts/agentchattr." >&2
    exit 1
  fi
}

# Recreate .venv when it is missing, broken, or built on too old an interpreter,
# and (re)install requirements whenever requirements.txt changes.
agentchattr_ensure_venv() {
  agentchattr_ensure_app
  mkdir -p "$AGENTCHATTR_DATA_DIR" "$AGENTCHATTR_UPLOAD_DIR" "$(dirname -- "$AGENTCHATTR_SERVER_LOG")"

  cd "$AGENTCHATTR_APP_ROOT"

  # Drop a venv that is unusable or built on a too-old Python.
  if [ -d ".venv" ]; then
    if [ ! -x ".venv/bin/python" ] || ! agentchattr_python_ok ".venv/bin/python"; then
      printf '%s\n' "Rebuilding agentchattr venv (missing, broken, or Python < ${AGENTCHATTR_PY_MIN_MAJOR}.${AGENTCHATTR_PY_MIN_MINOR})..." >&2
      rm -rf ".venv"
    fi
  fi

  if [ ! -x ".venv/bin/python" ]; then
    PYTHON_BIN="$(agentchattr_python_bin)" || exit 1
    printf 'Creating agentchattr venv with %s\n' "$PYTHON_BIN" >&2
    if ! "$PYTHON_BIN" -m venv ".venv"; then
      printf '%s\n' "Failed to create virtualenv at $AGENTCHATTR_APP_ROOT/.venv" >&2
      exit 1
    fi
    rm -f ".venv/.requirements-stamp"
  fi

  # Reinstall deps when requirements.txt changed, when the stamp is absent, or
  # when a core import is missing (e.g. a previous install died halfway).
  _req_hash="$(cksum requirements.txt | awk '{print $1"-"$2}')"
  _stamp_file=".venv/.requirements-stamp"
  _stamp_val=""
  [ -f "$_stamp_file" ] && _stamp_val="$(cat "$_stamp_file")"

  if [ "$_stamp_val" != "$_req_hash" ] || ! .venv/bin/python -c "import fastapi, uvicorn, mcp" >/dev/null 2>&1; then
    printf '%s\n' "Installing agentchattr dependencies..." >&2
    .venv/bin/python -m pip install --upgrade pip >/dev/null 2>&1 || true
    if ! .venv/bin/python -m pip install -r requirements.txt; then
      printf '%s\n' "Failed to install agentchattr dependencies from requirements.txt" >&2
      exit 1
    fi
    if ! .venv/bin/python -c "import fastapi, uvicorn, mcp" >/dev/null 2>&1; then
      printf '%s\n' "Dependencies installed but fastapi/uvicorn/mcp are still not importable." >&2
      exit 1
    fi
    printf '%s\n' "$_req_hash" > "$_stamp_file"
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
    < /dev/null > "$AGENTCHATTR_SERVER_LOG" 2>&1 &

  i=0
  while [ "$i" -lt 60 ]; do
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
