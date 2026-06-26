#!/usr/bin/env python3
"""Inject a project reminder when assistant wording hits configured terms."""

import json
import re
import sys
from pathlib import Path


EFFORT_REMINDER = (
    "Reminder: multi-session efforts are must-do. Never use large efforts as "
    "an excuse to avoid work. Just do it."
)
TRACTABLE_REMINDER = (
    "Are you still working on the hard, high-effort tasks or stalling with "
    "simple tasks? Do the hard high effort tasks."
)

TRIGGERS = [
    (
        re.compile(
            r"(?i)(?<![A-Za-z0-9_])"
            r"(?:multi-session|fabricate|research-level|multi-day|multi-month|multi-step build)"
            r"(?![A-Za-z0-9_])"
        ),
        EFFORT_REMINDER,
    ),
    (
        re.compile(r"(?i)(?<![A-Za-z0-9_])tractable(?![A-Za-z0-9_])"),
        TRACTABLE_REMINDER,
    ),
]


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


def reminders_for_texts(texts):
    reminders = []
    for pattern, reminder in TRIGGERS:
        if any(pattern.search(text) for text in texts):
            reminders.append(reminder)
    return "\n\n".join(reminders)


def post_tool_use_reminder(hook_input):
    transcript_path = hook_input.get("transcript_path", "")
    if not transcript_path:
        return ""

    return reminders_for_texts(assistant_texts_since_last_prompt(transcript_path))


def stop_reminder(hook_input):
    last_message = hook_input.get("last_assistant_message")
    if isinstance(last_message, str):
        reminder = reminders_for_texts([last_message])
        if reminder:
            return reminder

    transcript_path = hook_input.get("transcript_path", "")
    if not transcript_path:
        return ""

    texts = assistant_texts_since_last_prompt(transcript_path)
    return reminders_for_texts(texts[-1:]) if texts else ""


def main():
    try:
        hook_input = json.load(sys.stdin)
    except (json.JSONDecodeError, ValueError):
        return 0

    hook_event = hook_input.get("hook_event_name", "")

    if hook_event == "PostToolUse":
        reminder = post_tool_use_reminder(hook_input)
    elif hook_event == "Stop":
        reminder = stop_reminder(hook_input)
    else:
        return 0

    if not reminder:
        return 0

    print(
        json.dumps(
            {
                "hookSpecificOutput": {
                    "hookEventName": hook_event,
                    "additionalContext": reminder,
                }
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
