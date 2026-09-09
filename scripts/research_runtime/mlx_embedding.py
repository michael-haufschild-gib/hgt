"""Qwen's original embedding weights through pinned MLX-LM base hidden states.

See licenses/NOTICE.md and upstream/MLX-LM-qwen3.py.txt (MIT). No converted
artifact, generation head, remote loader, or reduced precision is used here.
"""
from __future__ import annotations

import json
from pathlib import Path

from .config import BATCH_SIZE, CONTEXT_TOKENS
from .protocol import RuntimeUnavailable, remaining


class MLXEmbedding:
    def __init__(self, path: Path):
        import mlx.core as mx
        from mlx_lm.models.qwen3 import ModelArgs, Qwen3Model
        from transformers import AutoTokenizer

        if not mx.metal.is_available():
            raise RuntimeUnavailable('MLX embedding requires Apple Metal')
        self.tokenizer = AutoTokenizer.from_pretrained(
            str(path), local_files_only=True, trust_remote_code=False, padding_side='right')
        # The official embedding artifact has bare base-model keys. The generic
        # mlx-lm generation loader expects model.* keys and is inappropriate.
        self.model = Qwen3Model(ModelArgs.from_dict(json.loads((path/'config.json').read_text())))
        self.model.load_weights(str(path/'model.safetensors'), strict=True)
        self.model.eval()
        self.model.set_dtype(mx.float32)
        mx.eval(self.model.parameters())
        # Qwen3's attention/reshape code depends on Python shapes. Shapeless
        # compilation produced finite but incorrect vectors in the CPU audit.
        self.forward = mx.compile(self.model, shapeless=False)

    def embed(self, texts: list[str], *, deadline: float) -> list[list[float]]:
        import mlx.core as mx
        import numpy as np

        remaining(deadline)
        if not texts:
            return []
        tokens = self.tokenizer(texts, padding=False, truncation=True,
                                max_length=CONTEXT_TOKENS)['input_ids']
        if any(not ids for ids in tokens):
            raise ValueError('embedding text must contain at least one token')
        order = sorted(range(len(texts)), key=lambda i: len(tokens[i]))
        result = [None] * len(texts)
        for start in range(0, len(order), BATCH_SIZE):
            remaining(deadline)
            indices = order[start:start+BATCH_SIZE]
            x = self.tokenizer.pad({'input_ids': [tokens[i] for i in indices]},
                                   padding=True, pad_to_multiple_of=32,
                                   return_attention_mask=True, return_tensors='np')
            # Causal attention cannot see right padding after a valid token.
            # Pool each last valid token, never the last padded array position.
            hidden = self.forward(mx.array(x['input_ids']))
            pooled = hidden[mx.arange(len(indices)),
                            mx.array(x['attention_mask'].sum(axis=1)-1)].astype(mx.float32)
            vectors = pooled / mx.maximum(mx.linalg.norm(pooled, axis=1, keepdims=True), 1e-12)
            mx.eval(vectors)
            values = np.array(vectors)
            if not np.isfinite(values).all() or not np.allclose(
                    np.linalg.norm(values, axis=1), 1, atol=1e-5):
                raise RuntimeError('non-finite or zero-norm MLX embedding')
            for index, vector in zip(indices, values.tolist()):
                result[index] = vector
        remaining(deadline)
        return result
