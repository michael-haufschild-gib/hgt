import json
import sys
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import agentchattr_mcp_stdio as bridge


class _RecordingHandler(BaseHTTPRequestHandler):
    requests = []

    def log_message(self, _format, *_args):
        pass

    def do_POST(self):
        size = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(size)
        type(self).requests.append((self.path, dict(self.headers), body))
        payload = {"name": "codex-2", "token": "test-token", "slot": 2}
        encoded = json.dumps(payload).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(encoded)))
        self.end_headers()
        self.wfile.write(encoded)


class AgentChattrMcpIdentityTests(unittest.TestCase):
    def setUp(self):
        _RecordingHandler.requests = []
        self.server = ThreadingHTTPServer(("127.0.0.1", 0), _RecordingHandler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.server_url = f"http://127.0.0.1:{self.server.server_port}"

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(timeout=2)

    def test_registers_codex_and_returns_server_identity(self):
        register = getattr(bridge, "_register_agent", lambda *_args: None)

        result = register(self.server_url, "codex")

        self.assertIsNotNone(result)
        self.assertEqual(result["name"], "codex-2")
        path, headers, body = _RecordingHandler.requests[-1]
        self.assertEqual(path, "/api/register")
        self.assertEqual(headers["Content-Type"], "application/json")
        self.assertEqual(json.loads(body), {"base": "codex", "label": "Codex App"})

    def test_authenticated_requests_send_registered_token(self):
        auth_headers = getattr(bridge, "_auth_headers", lambda *_args: {})

        headers = auth_headers("test-token")

        self.assertIn("Authorization", headers)
        self.assertIn("X-Agent-Token", headers)
        self.assertEqual(headers["Authorization"], "Bearer test-token")
        self.assertEqual(headers["X-Agent-Token"], "test-token")

    def test_registration_label_matches_configured_agent_family(self):
        bridge._register_agent(self.server_url, "claude")

        _path, _headers, body = _RecordingHandler.requests[-1]
        self.assertEqual(json.loads(body), {"base": "claude", "label": "Claude App"})

    def test_heartbeat_and_deregister_use_registered_identity(self):
        heartbeat = getattr(bridge, "_heartbeat_once", lambda *_args: None)
        deregister = getattr(bridge, "_deregister_agent", lambda *_args: None)

        heartbeat(self.server_url, "codex-2", "test-token")
        deregister(self.server_url, "codex-2", "test-token")

        self.assertEqual(
            [request[0] for request in _RecordingHandler.requests],
            ["/api/heartbeat/codex-2", "/api/deregister/codex-2"],
        )
        for _path, headers, _body in _RecordingHandler.requests:
            self.assertEqual(headers["Authorization"], "Bearer test-token")

    def test_heartbeat_loop_stops_when_bridge_closes(self):
        heartbeat_loop = getattr(bridge, "_heartbeat_loop", lambda *_args: None)
        stop = threading.Event()

        thread = threading.Thread(
            target=heartbeat_loop,
            args=(self.server_url, "codex-2", "test-token", stop, 0.01),
        )
        thread.start()
        stop.wait(0.05)
        stop.set()
        thread.join(timeout=1)

        self.assertFalse(thread.is_alive())
        self.assertTrue(
            any(path == "/api/heartbeat/codex-2" for path, _headers, _body in _RecordingHandler.requests)
        )


if __name__ == "__main__":
    unittest.main()
