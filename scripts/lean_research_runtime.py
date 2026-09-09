"""Dependency-free client for one shared, entirely local inference worker.

API: RuntimeClient(cache_dir: Path).status(), .embed(texts, query=False,
deadline=...), .rerank(query, documents, deadline=...), .generate(prompt,
deadline=..., max_tokens=1024). Deadlines are absolute time.monotonic values.
Inference methods accept priority='interactive' or 'enrichment'. See
research_runtime/README.md for bounded inputs, cancellation, and setup.
"""
from __future__ import annotations

import fcntl
from pathlib import Path
import socket
import subprocess
import threading
import time

try:
    from .research_runtime.config import (DEFAULT_CACHE_DIR, PROTOCOL_VERSION,
        PYTHON, RUNTIME_HOME, installation_status, offline_environment)
    from .research_runtime.protocol import (RuntimeDeadline, RuntimeUnavailable, frame,
                                           pop_frame, remaining, validate)
    from .research_runtime.worker import secure_directory, socket_directory
except ImportError:
    from research_runtime.config import (DEFAULT_CACHE_DIR, PROTOCOL_VERSION,
        PYTHON, RUNTIME_HOME, installation_status, offline_environment)
    from research_runtime.protocol import (RuntimeDeadline, RuntimeUnavailable, frame,
                                          pop_frame, remaining, validate)
    from research_runtime.worker import secure_directory, socket_directory

__all__ = ['RuntimeClient', 'RuntimeDeadline', 'RuntimeUnavailable', 'DEFAULT_CACHE_DIR', 'runtime_python']


def runtime_python(root: Path) -> Path:
    """Dedicated Python for CLI child engine/FAISS; does not install or start it."""
    return Path(root).resolve() / 'scripts' / 'research_runtime' / '.venv' / 'bin' / 'python'


class RuntimeClient:
    """Thread-safe; each call owns a socket. close() cancels this client's calls.

Use the SAME resolved cache_dir across agents to share one worker and weights.
Construction and status never start the worker, import ML, or download anything.
"""
    def __init__(self, cache_dir: Path):
        self.cache_dir = Path(cache_dir).expanduser().resolve()
        self.directory = socket_directory(self.cache_dir)
        self._guard = threading.Lock()
        self._sockets = set()
        self._closed = False

    def close(self) -> None:
        """Cancel only calls on this client, preserving other clients' requests."""
        with self._guard:
            self._closed = True
            for sock in self._sockets:
                try:
                    sock.shutdown(socket.SHUT_RDWR)
                except OSError:
                    pass

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def _connect(self, deadline):
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            sock.settimeout(remaining(deadline))
            sock.connect(str(self.directory / 'worker.sock'))
            return sock
        except BaseException:
            sock.close()
            raise

    def _ensure_worker(self, deadline):
        if not installation_status(self.cache_dir)['ready']:
            raise RuntimeUnavailable('local runtime not installed; run scripts/lean_research_setup.py with this cache-dir')
        secure_directory(self.directory)
        lock = (self.directory / 'startup.lock').open('a')
        try:
            while True:
                remaining(deadline)
                if self._closed:
                    raise RuntimeUnavailable('client closed during startup')
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    time.sleep(min(0.02, remaining(deadline)))
            try:
                return self._connect(deadline)
            except OSError:
                pass
            env = offline_environment()
            with (self.directory / 'worker.log').open('ab') as log:
                child = subprocess.Popen([str(PYTHON), '-m', 'research_runtime.worker',
                    '--cache-dir', str(self.cache_dir)], cwd=str(RUNTIME_HOME.parent), env=env,
                    stdin=subprocess.DEVNULL, stdout=log, stderr=log, start_new_session=True)
            # Broker is intentionally shared, outlives requesting clients, exits when idle.
            # Reap our own startup child; never terminate a shared broker on client cancellation.
            threading.Thread(target=child.wait, daemon=True).start()
            while True:
                remaining(deadline)
                if self._closed:
                    raise RuntimeUnavailable('client closed during startup')
                if child.poll() is not None:
                    try:
                        return self._connect(deadline)
                    except OSError:
                        raise RuntimeUnavailable('local worker startup failed; see private worker.log') from None
                try:
                    return self._connect(deadline)
                except OSError:
                    time.sleep(min(0.02, remaining(deadline)))
        finally:
            lock.close()

    def _request(self, request, deadline, *, start=True):
        remaining(deadline)
        frame(request)  # Validate serialization/size before starting a worker.
        with self._guard:
            if self._closed:
                raise RuntimeUnavailable('client closed')
        try:
            try:
                sock = self._connect(deadline)
            except OSError:
                if not start:
                    raise RuntimeUnavailable('worker not running') from None
                sock = self._ensure_worker(deadline)
            with sock:
                with self._guard:
                    if self._closed:
                        raise RuntimeUnavailable('client closed')
                    self._sockets.add(sock)
                try:
                    sock.settimeout(remaining(deadline))
                    wire = request if request.get('op') == 'status' else {**request, 'remaining_seconds': remaining(deadline)}
                    sock.sendall(frame(wire))
                    buffer = bytearray()
                    while True:
                        sock.settimeout(remaining(deadline))
                        data = sock.recv(65536)
                        if not data:
                            raise RuntimeUnavailable('local worker disconnected or request cancelled')
                        buffer.extend(data)
                        reply = pop_frame(buffer)
                        if reply is not None:
                            break
                    remaining(deadline)
                finally:
                    with self._guard:
                        self._sockets.discard(sock)
        except socket.timeout:
            raise RuntimeDeadline('local runtime deadline expired') from None
        except OSError as exc:
            raise RuntimeUnavailable(f'local runtime transport failed: {type(exc).__name__}') from None
        if reply.get('error') == 'deadline':
            raise RuntimeDeadline(reply['message'])
        if reply.get('error') == 'invalid':
            raise ValueError(reply['message'])
        if reply.get('error'):
            raise RuntimeUnavailable(reply['message'])
        return reply['result']

    def status(self) -> dict:
        status = installation_status(self.cache_dir)
        status.update({'running': False, 'protocol': PROTOCOL_VERSION})
        try:
            return self._request({'op': 'status'}, time.monotonic() + 0.3, start=False)
        except (RuntimeUnavailable, RuntimeDeadline, ValueError, KeyError):
            return status

    def embed(self, texts: list[str], *, query: bool = False, deadline: float,
              priority: str = 'interactive') -> list[list[float]]:
        request = {'op': 'embed', 'texts': texts, 'query': query,
                   'deadline': deadline, 'priority': priority}
        validate(request)
        if not texts:
            return []
        return self._request(request, deadline)

    def rerank(self, query: str, documents: list[str], *, deadline: float,
               priority: str = 'interactive') -> list[float]:
        request = {'op': 'rerank', 'query': query, 'documents': documents,
                   'deadline': deadline, 'priority': priority}
        validate(request)
        if not documents:
            return []
        return self._request(request, deadline)

    def generate(self, prompt: str, *, deadline: float, max_tokens: int = 1024,
                 priority: str = 'interactive') -> str:
        request = {'op': 'generate', 'prompt': prompt, 'max_tokens': max_tokens,
                   'deadline': deadline, 'priority': priority}
        validate(request)
        return self._request(request, deadline)
