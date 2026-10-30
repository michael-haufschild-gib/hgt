#!/usr/bin/env python3
"""PreToolUse(Bash|Grep) hook: remind the agent to use the Lean corpus search tool.

Fires on the Grep tool and on shell commands that invoke grep or rg, and
injects a short reminder into the agent's context. It never blocks the call.

Fail-open: if the payload cannot be parsed, the hook exits silently.
"""

import json
import re
import sys

REMINDER = (
    "For searching in the lean corpus use the search tool for the lean corpus. "
    "Check lean corpus before checking mathlib."
)

# grep-family and ripgrep executables. `git grep` decomposes into `git`, `grep`.
SEARCH_COMMANDS = {"grep", "egrep", "fgrep", "rg"}

# Split on whitespace and shell metacharacters so `a | grep x`, `a;rg x`
# and `$(grep x)` all decompose into plain words.
WORD_SPLIT = re.compile(r"[\s;&|()<>{}`\n\r\t]+")


def invokes_search(command):
    """True if any word of the command is a grep-family or rg executable."""
    for raw in WORD_SPLIT.split(command):
        w = raw.strip("\"'")
        if w.rsplit("/", 1)[-1] in SEARCH_COMMANDS:
            return True
    return False


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        sys.exit(0)

    tool = payload.get("tool_name")
    if tool == "Grep":
        hit = True
    elif tool == "Bash":
        hit = invokes_search(payload.get("tool_input", {}).get("command") or "")
    else:
        hit = False

    if hit:
        json.dump(
            {
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "additionalContext": REMINDER,
                }
            },
            sys.stdout,
        )
        sys.stdout.write("\n")
    sys.exit(0)


if __name__ == "__main__":
    main()
