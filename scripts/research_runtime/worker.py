"""Private Unix-socket supervisor, bounded queue, one spawned inference child.

The supervisor never imports ML libraries. It remains responsive during model
loading/Metal calls, owns child handles (not a global PID search), and kills a
cancelled child before accepting more inference work. Inference roles switch
processes to release Torch/MLX allocators on the 18 GiB target.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import fcntl
import hashlib
import multiprocessing
import os
from pathlib import Path
import selectors
import signal
import socket
import stat
import time

from .config import MAX_PENDING, PROTOCOL_VERSION, installation_status
from .protocol import ChildChannel, RuntimeDeadline, RuntimeUnavailable, frame, pop_frame, validate, receive_deadline

POLL_SECONDS = 0.02
IDLE_SECONDS = 300.0


def socket_directory(cache_dir: Path) -> Path:
    key = hashlib.sha256(str(cache_dir.resolve()).encode()).hexdigest()[:20]
    # AF_UNIX paths have a small platform limit. Cache paths may be arbitrarily long.
    return Path('/tmp') / f'hgt-research-{os.getuid()}-{key}'


def secure_directory(path: Path) -> None:
    path.mkdir(mode=0o700, parents=True, exist_ok=True)
    info = path.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
        raise RuntimeUnavailable(f'runtime directory must be owned/private: {path}')


def _model_child(channel, cache_dir: str):
    from .adapters import LocalModels, enforce_offline
    import select
    import threading
    # If the broker dies even during a stuck kernel, exit this child alone.
    parent = multiprocessing.parent_process()
    if parent is not None:
        def watch_parent():
            select.select([parent.sentinel], [], [])
            os._exit(0)
        threading.Thread(target=watch_parent, daemon=True).start()
    enforce_offline()
    models = LocalModels(Path(cache_dir))
    try:
        while True:
            request = channel.recv()
            try:
                result = models.run(request)
                reply = {'result': result, 'devices': models.status()}
            except Exception as exc:
                kind = 'deadline' if isinstance(exc, RuntimeDeadline) else 'unavailable'
                reply = {'error': kind, 'message': f'local inference failed: {type(exc).__name__}',
                         'devices': models.status()}
            channel.send(reply)
    except (EOFError, BrokenPipeError):
        pass
    finally:
        channel.close()


@dataclass(eq=False)
class Peer:
    sock: socket.socket
    accepted: float = field(default_factory=time.monotonic)
    incoming: bytearray = field(default_factory=bytearray)
    outgoing: bytearray = field(default_factory=bytearray)
    request: dict | None = None
    sequence: int = 0


class WorkerServer:
    """Test injection is constructor-only; public wire never accepts code/commands."""
    def __init__(self, cache_dir: Path, *, child_target=_model_child, idle_seconds=IDLE_SECONDS):
        self.cache_dir = Path(cache_dir).resolve()
        self.directory = socket_directory(self.cache_dir)
        self.child_target = child_target
        self.idle_seconds = idle_seconds
        self.selector = selectors.DefaultSelector()
        self.peers = set()
        self.active = None
        self.child = None
        self.pipe = None
        self.child_outgoing = bytearray()
        self.child_incoming = bytearray()
        self.family = None
        self.devices = {}
        self.last_devices = {}
        self.sequence = 0
        self.stopping = False
        self.last_activity = time.monotonic()

    def _stop_child(self):
        child = self.child
        self.child_outgoing.clear()
        self.child_incoming.clear()
        if self.pipe is not None:
            self.pipe.close()
            self.pipe = None
        self.family = None
        self.devices = {}
        if child is not None:
            # A direct child handle, never killall/pkill or a PID read from stale metadata.
            if child.is_alive():
                child.terminate()
                child.join(0.15)
                if child.is_alive():
                    child.kill()
            child.join(5)
            if child.is_alive():
                # Never launch overlapping inference if the OS has not reaped the old child.
                self.stopping = True
                raise RuntimeUnavailable('inference child could not be reaped')
            child.close()
            self.child = None

    def _close(self, peer):
        if peer is self.active:
            self.active = None
            self._stop_child()
        self.peers.discard(peer)
        try:
            self.selector.unregister(peer.sock)
        except KeyError:
            pass
        peer.sock.close()

    def _reply(self, peer, reply):
        if peer not in self.peers:
            return
        try:
            peer.outgoing.extend(frame(reply))
        except (TypeError, ValueError):
            peer.outgoing.extend(frame({'error': 'unavailable', 'message': 'invalid model response'}))
        self.selector.modify(peer.sock, selectors.EVENT_READ | selectors.EVENT_WRITE, peer)

    def _status(self):
        status = installation_status(self.cache_dir)
        for role, device in self.devices.items():
            status['models'][role].update(device)
        status.update({'running': True, 'pid': os.getpid(), 'protocol': PROTOCOL_VERSION,
                       'child_pid': self.child.pid if self.child else None,
                       'active': self.active.request['op'] if self.active else None,
                       'pending': sum(p.request is not None and p.request['op'] != 'status'
                                      and not p.outgoing and p is not self.active
                                      for p in self.peers),
                       'last_devices': self.last_devices})
        return status

    def _read(self, peer):
        try:
            data = peer.sock.recv(65536)
            if not data:
                self._close(peer)
                return
            # Exactly one request per connection. EOF is cancellation.
            if peer.request is not None:
                self._close(peer)
                return
            peer.incoming.extend(data)
            request = pop_frame(peer.incoming)
            if request is None:
                return
            if peer.incoming:
                raise ValueError('one request per connection')
            request = receive_deadline(request)
            validate(request)
            peer.request = request
            self.sequence += 1
            peer.sequence = self.sequence
            if request['op'] == 'status':
                self._reply(peer, {'result': self._status()})
            elif request['op'] in ('embed', 'rerank') and not request.get(
                    'texts' if request['op'] == 'embed' else 'documents'):
                self._reply(peer, {'result': []})
        except RuntimeDeadline:
            self._reply(peer, {'error': 'deadline', 'message': 'request expired in queue'})
        except (ValueError, TypeError, KeyError):
            self._reply(peer, {'error': 'invalid', 'message': 'invalid runtime request'})
        except OSError:
            self._close(peer)

    def _write(self, peer):
        try:
            count = peer.sock.send(peer.outgoing)
            del peer.outgoing[:count]
            if not peer.outgoing:
                self._close(peer)
        except BlockingIOError:
            pass
        except OSError:
            self._close(peer)

    def _expire(self):
        now = time.monotonic()
        for peer in list(self.peers):
            if peer.outgoing:
                if now - peer.accepted > 602:
                    self._close(peer)
                continue
            if peer.request is None:
                if now - peer.accepted > 2:
                    self._close(peer)
            elif peer.request.get('deadline', now + 1) <= now:
                if peer is self.active:
                    self.active = None
                    self._stop_child()
                self._reply(peer, {'error': 'deadline', 'message': 'local runtime deadline expired'})

    def _schedule(self):
        pending = sorted((p for p in self.peers if p.request and not p.outgoing
                          and p is not self.active and p.request['op'] != 'status'),
                         key=lambda p: (p.request.get('priority', 'interactive') != 'interactive', p.sequence))
        if self.active and pending and self.active.request.get('priority') == 'enrichment' and (
                pending[0].request.get('priority', 'interactive') == 'interactive'):
            interrupted, self.active = self.active, None
            self._stop_child()
            self._reply(interrupted, {'error': 'unavailable', 'message': 'enrichment preempted by interactive search; retry later'})
        if self.active or not pending:
            return
        peer = pending[0]
        family = 'generation' if peer.request['op'] == 'generate' else 'search'
        try:
            if self.child is not None and (not self.child.is_alive() or self.family != family):
                self._stop_child()
            if self.child is None:
                parent, child_socket = socket.socketpair(socket.AF_UNIX, socket.SOCK_STREAM)
                parent.setblocking(False)
                child_pipe = ChildChannel(child_socket)
                self.child = multiprocessing.get_context('spawn').Process(
                    target=self.child_target, args=(child_pipe, str(self.cache_dir)), daemon=True)
                self.pipe = parent
                self.child.start()
                child_pipe.close()
                self.family = family
            self.child_outgoing.extend(frame(peer.request))
            self.active = peer
        except (OSError, EOFError, RuntimeError):
            self._stop_child()
            self._reply(peer, {'error': 'unavailable', 'message': 'unable to start local inference child'})

    def _collect(self):
        if self.active is None:
            return
        try:
            if self.child_outgoing:
                try:
                    sent = self.pipe.send(self.child_outgoing[:65536])
                    del self.child_outgoing[:sent]
                except BlockingIOError:
                    pass
            # Bounded nonblocking IPC, including incomplete messages from a stuck child.
            for _ in range(8):
                try:
                    data = self.pipe.recv(65536)
                except BlockingIOError:
                    break
                if not data:
                    raise EOFError
                self.child_incoming.extend(data)
                reply = pop_frame(self.child_incoming)
                if reply is not None:
                    peer, self.active = self.active, None
                    self.devices = reply.pop('devices', {})
                    self.last_devices.update(self.devices)
                    self._reply(peer, reply)
                    return
            if not self.child.is_alive():
                raise EOFError
        except (OSError, EOFError, ValueError, TypeError):
            peer, self.active = self.active, None
            self._stop_child()
            self._reply(peer, {'error': 'unavailable', 'message': 'local inference child exited or sent invalid output'})

    def serve(self):
        secure_directory(self.directory)
        lock = (self.directory / 'worker.lock').open('a')
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            lock.close()
            return  # Another supervisor owns this cache; do not touch its socket.
        sock_path = self.directory / 'worker.sock'
        listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            sock_path.unlink(missing_ok=True)
            listener.bind(str(sock_path))
            os.chmod(sock_path, 0o600)
            listener.listen(MAX_PENDING)
            listener.setblocking(False)
            self.selector.register(listener, selectors.EVENT_READ, None)
            while not self.stopping:
                for key, mask in self.selector.select(POLL_SECONDS):
                    if key.data is None:
                        sock, _ = listener.accept()
                        sock.setblocking(False)
                        if len(self.peers) >= MAX_PENDING:
                            sock.close()  # Explicit client RuntimeUnavailable, no unbounded queue.
                            continue
                        peer = Peer(sock)
                        self.peers.add(peer)
                        self.selector.register(sock, selectors.EVENT_READ, peer)
                        self.last_activity = time.monotonic()
                    else:
                        peer = key.data
                        if mask & selectors.EVENT_READ:
                            self._read(peer)
                        if peer in self.peers and mask & selectors.EVENT_WRITE:
                            self._write(peer)
                self._expire()
                self._collect()
                self._schedule()
                if self.peers:
                    self.last_activity = time.monotonic()
                elif time.monotonic() - self.last_activity > self.idle_seconds:
                    break
        finally:
            self._stop_child()
            for peer in list(self.peers):
                self._close(peer)
            listener.close()
            self.selector.close()
            sock_path.unlink(missing_ok=True)
            lock.close()


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument('--cache-dir', required=True, type=Path)
    args = parser.parse_args(argv)
    server = WorkerServer(args.cache_dir)
    def stop(_signum, _frame):
        server.stopping = True
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    server.serve()


if __name__ == '__main__':
    main()
