# General Workmode Instructions

## Critical File-Edit Rule

- Append-only operations append at EOF with a shell here-doc (`cat >> file <<'EOF' ... EOF`) or equivalent append primitive.
- Do not use `apply_patch` for append-only operations.
- Use targeted edit tools only for inserting, replacing, moving, or deleting existing content.

## Session Init

1. Run `mcp__serena__list_memories`. Read task-relevant memories.
2. State the project mission in one sentence before beginning work.

## Response style

Brief in conversational replies. Verbose in evidence — list files read, greps run, call sites checked, test output observed. Brevity does not apply to investigation or to the pre-claim gate in `rules/completion.md`.

## Tool Routing

| Need | Use | Not |
|-|-|-|
| Multi-step reasoning, debug, track state | `mcp__sequential-thinking__sequentialthinking` | Free-form reasoning in text |
| Track 2+ work steps | `TaskCreate`, `TaskUpdate`, `TaskList` | Untracked execution |
| Current (2025+) info, unfamiliar APIs | `WebSearch` | Training data guesses |
| File exploration, code research | `Grep`, `Glob`, `Read`, Serena MCP | Subagents |
| Specialized workflow | `Skill` tool | Manual reimplementation |
| File content search | `Grep` | `grep`/`rg` via Bash |
| Symbol-level code ops | Serena MCP | Line-number sed/awk |
| Cross-session persistence | Serena `write_memory`/`read_memory` | Rediscovery |
| File already read this session | Reuse from context | Re-read |

## Serena MCP

Symbol-level operations on analyzed code:
- `find_symbol` — locate definition by name
- `find_referencing_symbols` — find all usages
- `get_symbols_overview` — scan file structure
- `replace_symbol_body` — edit function/method/class
- `insert_before_symbol`/`insert_after_symbol` — add code at precise locations

Not for: plain-text search (Grep), entire files (Read), new files (Write), non-code files (Read/Edit).

## Subagents

Default: do not use. Prefer `Grep`, `Glob`, `Read`, Serena MCP directly.

Permitted only when (a) user explicitly requests it, (b) active skill demands it, or (c) the task is genuinely parallelizable across disjoint files. Code-touching subagents require `model: "opus"`.

Banned: `subagent_type: "Explore"` (always), `subagent_type: "Plan"` (use `EnterPlanMode`).

When permitted, every prompt must include: explicit file paths, one specific objective, required output format, and what NOT to do. Size the task so total output stays well under 100k tokens — subagents freeze silently above that. Append: "Final response under 2000 chars. List outcomes, not process."

After receiving output: spot-check at least one file/symbol claim yourself before accepting.
