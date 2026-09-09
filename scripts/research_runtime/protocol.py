"""Bounded, length-framed JSON over private Unix sockets (never pickle)."""
from __future__ import annotations

import json
import math
import struct
import time

from .config import MAX_FRAME, MAX_ITEMS, MAX_SECONDS, MAX_TEXT, MAX_TOTAL_TEXT, MAX_TOKENS


class RuntimeUnavailable(RuntimeError):
    """Setup missing, worker busy/preempted, transport failure, or model failure."""


class RuntimeDeadline(TimeoutError):
    """Absolute monotonic deadline elapsed; request abandoned and cleaned up."""


def remaining(deadline: float) -> float:
    if isinstance(deadline, bool) or not isinstance(deadline, (int, float)) or not math.isfinite(deadline):
        raise ValueError('deadline must be a finite absolute time.monotonic value')
    left = deadline - time.monotonic()
    if left <= 0:
        raise RuntimeDeadline('local runtime deadline expired')
    return left


def frame(value: dict) -> bytes:
    raw = json.dumps(value, ensure_ascii=False, allow_nan=False, separators=(',', ':')).encode()
    if len(raw) > MAX_FRAME:
        raise ValueError('runtime frame exceeds byte limit')
    return struct.pack('!I', len(raw)) + raw


def pop_frame(buffer: bytearray):
    if len(buffer) < 4:
        return None
    size = struct.unpack('!I', buffer[:4])[0]
    if size > MAX_FRAME or not size:
        raise ValueError('invalid runtime frame size')
    if len(buffer) < size + 4:
        return None
    value = json.loads(buffer[4:size + 4])
    del buffer[:size + 4]
    if not isinstance(value, dict):
        raise ValueError('runtime message must be an object')
    return value


class ChildChannel:
    """Blocking child endpoint; supervisor uses raw nonblocking framed socket."""
    def __init__(self, sock):
        self.sock = sock
        self.buffer = bytearray()

    def send(self, message):
        self.sock.sendall(frame(message))

    def recv(self):
        while True:
            message = pop_frame(self.buffer)
            if message is not None:
                return message
            data = self.sock.recv(65536)
            if not data:
                raise EOFError
            self.buffer.extend(data)

    def close(self):
        self.sock.close()


def validate(request: dict) -> None:
    op = request.get('op')
    if op == 'status':
        return
    if op not in ('embed', 'rerank', 'generate'):
        raise ValueError('unknown runtime operation')
    if remaining(request.get('deadline')) > MAX_SECONDS + 1:
        raise ValueError(f'deadline may be at most {MAX_SECONDS:g} seconds ahead')
    if request.get('priority', 'interactive') not in ('interactive', 'enrichment'):
        raise ValueError('priority must be interactive or enrichment')
    items = request.get('texts' if op == 'embed' else 'documents', [])
    if not isinstance(items, list) or len(items) > MAX_ITEMS:
        raise ValueError(f'expected at most {MAX_ITEMS} texts')
    strings = list(items)
    if op == 'embed' and not isinstance(request.get('query', False), bool):
        raise ValueError('query must be boolean for embed')
    if op == 'rerank':
        strings.append(request.get('query'))
    if op == 'generate':
        strings.append(request.get('prompt'))
        count = request.get('max_tokens', 1024)
        if type(count) is not int or not 1 <= count <= MAX_TOKENS:
            raise ValueError(f'max_tokens must be between 1 and {MAX_TOKENS}')
    if any(not isinstance(s, str) or len(s) > MAX_TEXT for s in strings):
        raise ValueError(f'texts must be strings of at most {MAX_TEXT} characters')
    if sum(map(len, strings)) > MAX_TOTAL_TEXT:
        raise ValueError('request exceeds total text limit')
