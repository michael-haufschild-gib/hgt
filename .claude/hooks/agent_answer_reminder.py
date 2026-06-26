#!/usr/bin/env python3
"""Inject a project reminder when assistant wording hits configured terms."""

import json
import re
import sys
from pathlib import Path


REMINDER = (
    "Reminder: multi-session efforts are must-do. Never use large efforts as "
    "an excuse to avoid work. Just do it."
)

TRIGGER_RE = re.compile(r"(?i)(?<![A-Za-z0-9_])(?:multi-session|fabricate)(?![A-Za-z0-9_])")


def message_from_entry(entry):
    if isinstance(entry.get("message"), dict):
        return entry["message"]
    return entry


def content_text(content):
    if isinstance(content, str):
        return content

    if not isinstance(content, list):
        return ""

    texts = []
    for block in content:
        if isinstance(block, dict) and block.get("type") == "text":
            text = block.get("text")
            if isinstance(text, str):
                texts.append(text)
    return "\n".join(texts)


def is_user_tool_result(message):
    if message.get("role") != "user":
        return False

    content = message.get("content")
    if not isinstance(content, list) or not content:
        return False

    return all(isinstance(block, dict) and block.get("type") == "tool_result" for block in content)


def assistant_texts_since_last_prompt(transcript_path):
    texts = []

    try:
        lines = Path(transcript_path).read_text(encoding="utf-8").splitlines()
    except Exception:
        return texts

    for line in lines:
        if not line.strip():
            continue

        try:
            entry = json.loads(line)
        except json.JSONDecodeError:
            continue

        message = message_from_entry(entry)
        role = message.get("role")

        if role == "user" and not is_user_tool_result(message):
            texts = []
            continue

        if role == "assistant":
            text = content_text(message.get("content"))
            if text.strip():
                texts.append(text)

    return texts


def should_fire_for_post_tool_use(hook_input):
    transcript_path = hook_input.get("transcript_path", "")
    if not transcript_path:
        return False

    return any(TRIGGER_RE.search(text) for text in assistant_texts_since_last_prompt(transcript_path))


def should_fire_for_stop(hook_input):
    last_message = hook_input.get("last_assistant_message")
    if isinstance(last_message, str) and TRIGGER_RE.search(last_message):
        return True

    transcript_path = hook_input.get("transcript_path", "")
    if not transcript_path:
        return False

    texts = assistant_texts_since_last_prompt(transcript_path)
    return bool(texts and TRIGGER_RE.search(texts[-1]))


def main():
    try:
        hook_input = json.load(sys.stdin)
    except (json.JSONDecodeError, ValueError):
        return 0

    hook_event = hook_input.get("hook_event_name", "")

    if hook_event == "PostToolUse":
        should_fire = should_fire_for_post_tool_use(hook_input)
    elif hook_event == "Stop":
        should_fire = should_fire_for_stop(hook_input)
    else:
        return 0

    if not should_fire:
        return 0

    print(
        json.dumps(
            {
                "hookSpecificOutput": {
                    "hookEventName": hook_event,
                    "additionalContext": REMINDER,
                }
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
