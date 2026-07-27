#!/usr/bin/env python3
"""stdio <-> streamable-HTTP bridge for the project-local agentchattr MCP server.

Claude Code (and any MCP client that speaks stdio) launches this script; it
relays JSON-RPC frames verbatim to the agentchattr streamable-HTTP endpoint.

Why a bridge instead of a plain `"type": "http"` entry in .mcp.json:
the client spawns this process at connect time, and the shell wrapper
(agentchattr-mcp.sh) makes sure the agentchattr server is actually listening
first. That removes the ordering race where a session starts before the
server does and the MCP connection is marked failed for the whole session.

stdout carries protocol frames only — every diagnostic goes to stderr.
"""

from __future__ import annotations

import os
import sys

import anyio
from mcp.client.streamable_http import streamablehttp_client
from mcp.server.stdio import stdio_server

DEFAULT_URL = "http://127.0.0.1:18620/mcp"

# The GET stream is idle whenever no agent posts to chat. Keep it effectively
# unbounded so a quiet channel never tears the session down.
SSE_READ_TIMEOUT = 60 * 60 * 24  # seconds
HTTP_TIMEOUT = 60  # seconds, per request


def _log(message: str) -> None:
    print(f"[agentchattr-mcp] {message}", file=sys.stderr, flush=True)


async def _pump(source, sink, label: str, on_done=None) -> None:
    """Forward SessionMessages from `source` to `sink` until `source` closes."""
    try:
        async for message in source:
            if isinstance(message, Exception):
                _log(f"{label}: dropping malformed frame: {message!r}")
                continue
            await sink.send(message)
    except anyio.ClosedResourceError:
        pass
    except anyio.BrokenResourceError:
        pass
    finally:
        if on_done is not None:
            on_done()


async def _run(url: str) -> None:
    async with streamablehttp_client(
        url,
        timeout=HTTP_TIMEOUT,
        sse_read_timeout=SSE_READ_TIMEOUT,
    ) as (http_read, http_write, _get_session_id):
        async with stdio_server() as (stdio_read, stdio_write):
            async with anyio.create_task_group() as tg:
                # When either side hangs up, tear the whole bridge down;
                # otherwise the surviving pump would block forever.
                stop = tg.cancel_scope.cancel
                tg.start_soon(_pump, stdio_read, http_write, "client->server", stop)
                tg.start_soon(_pump, http_read, stdio_write, "server->client", stop)


def main() -> int:
    url = os.environ.get("AGENTCHATTR_MCP_URL") or DEFAULT_URL
    try:
        anyio.run(_run, url)
    except KeyboardInterrupt:
        return 0
    except Exception as exc:  # noqa: BLE001 — surface any transport failure
        _log(f"bridge to {url} failed: {exc!r}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
