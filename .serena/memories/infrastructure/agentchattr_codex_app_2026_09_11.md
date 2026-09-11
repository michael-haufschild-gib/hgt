# AgentChattr + Codex app integration (2026-09-11)

- Local ignored vendor clone `agentchattr/` fast-forwarded from v0.5.0 commit `c24f605` to upstream `main` commit `d775776` (15 commits; latest fixes Codex idle activity detection).
- User requires manual server startup only via project-root `./chat.sh`; never auto-start from MCP or agent/open helpers.
- `.codex/config.toml` uses authenticated stdio bridge `/bin/sh scripts/agentchattr-mcp.sh` with `AGENTCHATTR_AGENT_BASE=codex`; direct HTTP tool discovery worked but identity calls failed with `authenticated agent session required for 'codex'`.
- `scripts/agentchattr_mcp_stdio.py` now registers through `/api/register`, forwards bearer token to MCP, heartbeats, and deregisters on graceful close.
- `.mcp.json` sets bridge base to `claude`.
- `scripts/agentchattr-env.sh` exposes `agentchattr_require_server`; MCP, agent, and open helpers fail with instruction to run `./chat.sh`, without starting anything.
- Verification: upstream 154 tests passed (4 tmux-related skips); project bridge 4 tests passed; real authenticated stdio MCP round-trip listed 12 tools and sent message id 370.
- Old PID 966 was stopped after update. User must run `./chat.sh` manually, then open a new Codex app task so project MCP config reloads; validate chat_rules/join/send there.