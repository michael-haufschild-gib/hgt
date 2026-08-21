#!/usr/bin/env bash
# lean-check: run `lake env lean` on a path relative to the repo root, from formal/
set -uo pipefail
cd /Users/michael/Documents/code/hgt/formal
exec timeout 3600 lake env lean "$@"
