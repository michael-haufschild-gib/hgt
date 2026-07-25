#!/usr/bin/env python3
"""PreToolUse(Bash) hook: refuse `git stash` and `git revert`.

Reads the hook payload on stdin, scans the proposed shell command for an
invocation of `git stash` (other than the read-only `list`/`show`
subcommands) or `git revert`, and emits a structured `deny` decision when
one is found.

Fail-closed: if the payload cannot be parsed or the scan raises, the call
is denied rather than allowed.
"""

import json
import re
import sys

# git subcommands that are blocked outright.
BLOCKED = {"revert"}

# `git stash <sub>` is blocked unless <sub> is read-only. A bare `git stash`
# means `git stash push`, so it is blocked too.
STASH_READ_ONLY = {"list", "show"}

# Global git options that take a separate value argument, e.g. `git -C /repo stash`.
OPTS_WITH_VALUE = {"-C", "-c", "--git-dir", "--work-tree", "--namespace", "--exec-path"}

# Split on whitespace and shell metacharacters so `a && git stash`, `a;git revert`
# and `$(git stash)` all decompose into plain words.
WORD_SPLIT = re.compile(r"[\s;&|()<>{}`\n\r\t]+")


def words(command):
    """Return the command's words with surrounding quotes stripped."""
    out = []
    for raw in WORD_SPLIT.split(command):
        w = raw.strip("\"'")
        if w:
            out.append(w)
    return out


def find_violation(command):
    """Return a human-readable reason string, or None if the command is fine."""
    toks = words(command)
    i = 0
    while i < len(toks):
        tok = toks[i]
        # `git`, `/usr/bin/git`, `git.exe` ...
        if tok == "git" or tok.endswith("/git"):
            j = i + 1
            # Skip git's global options to reach the subcommand.
            while j < len(toks) and toks[j].startswith("-"):
                if toks[j] in OPTS_WITH_VALUE:
                    j += 2
                else:
                    j += 1
            if j < len(toks):
                sub = toks[j]
                if sub in BLOCKED:
                    return "`git %s` is blocked by a project hook." % sub
                if sub == "stash":
                    nxt = toks[j + 1] if j + 1 < len(toks) else ""
                    if nxt not in STASH_READ_ONLY:
                        return (
                            "`git stash%s` is blocked by a project hook."
                            % (" " + nxt if nxt else "")
                        )
            i = j
        i += 1
    return None


def deny(reason):
    json.dump(
        {
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "deny",
                "permissionDecisionReason": reason,
            }
        },
        sys.stdout,
    )
    sys.stdout.write("\n")
    sys.exit(0)


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception as exc:  # unparseable payload -> cannot verify -> refuse
        deny("git-stash/revert guard could not read the hook payload (%s)." % exc)

    if payload.get("tool_name") != "Bash":
        sys.exit(0)

    command = payload.get("tool_input", {}).get("command") or ""

    try:
        reason = find_violation(command)
    except Exception as exc:  # scan failed -> cannot verify -> refuse
        deny("git-stash/revert guard failed while scanning the command (%s)." % exc)

    if reason:
        deny(
            reason + " These commands can silently discard or rewrite the user's "
            "work, so Claude may not run them. Ask the user to run it themselves "
            "if it is genuinely wanted. Read-only `git stash list` and "
            "`git stash show` are allowed. Note: the guard matches the literal "
            "text of the command, so quoting or documenting these commands in a "
            "shell string also trips it — use the Write/Edit tools for that."
        )

    sys.exit(0)


if __name__ == "__main__":
    main()
