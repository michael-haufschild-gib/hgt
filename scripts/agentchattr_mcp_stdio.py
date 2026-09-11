#!/usr/bin/env python3
"""Authenticated stdio bridge for the project-local agentchattr MCP server.

Codex or another MCP client launches this script. It registers that client as
an agent, forwards the server-issued bearer token, keeps presence alive, and
relays JSON-RPC frames to the streamable-HTTP endpoint.

Why a bridge instead of a plain `"type": "http"` entry in .mcp.json:
the client spawns this process at connect time, and the shell wrapper
(agentchattr-mcp.sh) makes sure the agentchattr server is actually listening
first. That removes the ordering race where a session starts before the
server does and the MCP connection is marked failed for the whole session.

stdout carries protocol frames only — every diagnostic goes to stderr.
"""

from __future__ import annotations

import json
import os
import sys
import threading
import urllib.request

import anyio
from mcp.client.streamable_http import streamablehttp_client
from mcp.server.stdio import stdio_server

DEFAULT_URL = "http://127.0.0.1:18620/mcp"
DEFAULT_SERVER_URL = "http://127.0.0.1:18600"
DEFAULT_AGENT_BASE = "codex"
HEARTBEAT_SECONDS = 5

# The GET stream is idle whenever no agent posts to chat. Keep it effectively
# unbounded so a quiet channel never tears the session down.
SSE_READ_TIMEOUT = 60 * 60 * 24  # seconds
HTTP_TIMEOUT = 60  # seconds, per request


def _log(message: str) -> None:
    print(f"[agentchattr-mcp] {message}", file=sys.stderr, flush=True)


def _auth_headers(token: str) -> dict[str, str]:
    return {
        "Authorization": f"Bearer {token}",
        "X-Agent-Token": token,
    }


def _register_agent(server_url: str, base: str) -> dict:
    body = json.dumps({"base": base, "label": f"{base.capitalize()} App"}).encode()
    request = urllib.request.Request(
        f"{server_url}/api/register",
        method="POST",
        data=body,
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(request, timeout=5) as response:
        return json.loads(response.read())


def _heartbeat_once(server_url: str, name: str, token: str) -> None:
    request = urllib.request.Request(
        f"{server_url}/api/heartbeat/{name}",
        method="POST",
        data=b"",
        headers=_auth_headers(token),
    )
    with urllib.request.urlopen(request, timeout=5):
        pass


def _deregister_agent(server_url: str, name: str, token: str) -> None:
    request = urllib.request.Request(
        f"{server_url}/api/deregister/{name}",
        method="POST",
        data=b"",
        headers=_auth_headers(token),
    )
    with urllib.request.urlopen(request, timeout=5):
        pass


def _heartbeat_loop(
    server_url: str,
    name: str,
    token: str,
    stop: threading.Event,
    interval: float = HEARTBEAT_SECONDS,
) -> None:
    while not stop.is_set():
        try:
            _heartbeat_once(server_url, name, token)
        except Exception as exc:  # noqa: BLE001 — bridge reports transient server failures
            _log(f"heartbeat failed: {exc!r}")
        stop.wait(interval)


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


async def _run(url: str, headers: dict[str, str]) -> None:
    async with streamablehttp_client(
        url,
        headers=headers,
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
    server_url = os.environ.get("AGENTCHATTR_SERVER_URL") or DEFAULT_SERVER_URL
    base = os.environ.get("AGENTCHATTR_AGENT_BASE") or DEFAULT_AGENT_BASE
    registration = None
    stop = threading.Event()
    heartbeat_thread = None
    result = 0
    try:
        registration = _register_agent(server_url, base)
        name = registration["name"]
        token = registration["token"]
        heartbeat_thread = threading.Thread(
            target=_heartbeat_loop,
            args=(server_url, name, token, stop),
            daemon=True,
        )
        heartbeat_thread.start()
        anyio.run(_run, url, _auth_headers(token))
    except KeyboardInterrupt:
        pass
    except Exception as exc:  # noqa: BLE001 — surface any transport failure
        _log(f"bridge to {url} failed: {exc!r}")
        result = 1
    finally:
        stop.set()
        if heartbeat_thread is not None:
            heartbeat_thread.join(timeout=HEARTBEAT_SECONDS + 1)
        if registration is not None:
            try:
                _deregister_agent(server_url, registration["name"], registration["token"])
            except Exception as exc:  # noqa: BLE001 — cleanup is best effort
                _log(f"deregister failed: {exc!r}")
    return result


if __name__ == "__main__":
    raise SystemExit(main())
