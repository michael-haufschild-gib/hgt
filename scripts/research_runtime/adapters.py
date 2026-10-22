"""Local adapters derived from LeanExplore concepts; see upstream/NOTICE.md.

Qwen prompt/token procedures follow pinned official model cards, not the
LeanExplore reranker's true/false implementation. Heavy imports stay in child.
"""
from __future__ import annotations

import os
import socket
import sys
from pathlib import Path

from .config import (BATCH_SIZE, CONTEXT_TOKENS, DOCUMENT_TEMPLATE, EMBEDDING_DIMENSIONS,
                     GENERATION_CONTEXT, MLX_EMBEDDING_MODULE, QUERY_TEMPLATE,
                     installation_status, offline_environment)
from .protocol import RuntimeDeadline, RuntimeUnavailable, remaining

RERANK_PREFIX = ('<|im_start|>system\nJudge whether the Document meets the requirements '
                 'based on the Query and the Instruct provided. Note that the answer '
                 'can only be "yes" or "no".<|im_end|>\n<|im_start|>user\n')
RERANK_SUFFIX = '<|im_end|>\n<|im_start|>assistant\n<think>\n\n</think>\n\n'
# Qwen's reranker keeps its own instruction: it scores pairs and shares no
# vector space with the embedder, so its prompt is unrelated to Gemma's.
RERANK_INSTRUCTION = 'Find relevant Lean 4 math declarations'


def embedding_text(text: str, query: bool) -> str:
    return (QUERY_TEMPLATE if query else DOCUMENT_TEMPLATE).format(text=text)


def reranker_inputs(tokenizer, query: str, documents: list[str], max_length=CONTEXT_TOKENS):
    prefix = tokenizer.encode(RERANK_PREFIX, add_special_tokens=False)
    suffix = tokenizer.encode(RERANK_SUFFIX, add_special_tokens=False)
    budget = max_length - len(prefix) - len(suffix)
    if budget <= 0:
        raise ValueError('reranker token budget cannot fit official wrapper')
    pairs = [f'<Instruct>: {RERANK_INSTRUCTION}\n<Query>: {query}\n<Document>: {doc}' for doc in documents]
    inputs = tokenizer(pairs, padding=False, truncation='longest_first',
                       return_attention_mask=False, max_length=budget,
                       add_special_tokens=False)
    inputs['input_ids'] = [prefix + ids + suffix for ids in inputs['input_ids']]
    return tokenizer.pad(inputs, padding=True, return_tensors='pt', max_length=max_length)


def mean_pool(hidden, attention_mask):
    """Mean over real tokens only. EmbeddingGemma pools the mean, not the last
    token, so the mask is load-bearing: averaging pad positions in silently
    returns plausible, wrong vectors. Must stay identical to the batch runner."""
    mask = attention_mask.unsqueeze(-1).to(hidden.dtype)
    return (hidden * mask).sum(dim=1).float() / mask.sum(dim=1).clamp(min=1e-9).float()


def yes_no_ids(tokenizer) -> tuple[int, int]:
    ids = tuple(tokenizer.convert_tokens_to_ids(word) for word in ('no', 'yes'))
    for word, token in zip(('no', 'yes'), ids):
        if token is None or token == tokenizer.unk_token_id or tokenizer.encode(
                word, add_special_tokens=False) != [token]:
            raise RuntimeUnavailable(f'expected one official {word!r} token')
    if ids[0] == ids[1]:
        raise RuntimeUnavailable('yes/no token IDs must differ')
    return ids


def enforce_offline() -> None:
    """Defense in depth: HF flags plus deny INET sockets in inference process."""
    os.environ.update(offline_environment())

    def guard(event, args):
        if event == 'socket.__new__' and args[1] != socket.AF_UNIX:
            raise RuntimeUnavailable('network sockets prohibited in inference worker')
        if event in ('socket.getaddrinfo', 'socket.gethostbyname', 'socket.gethostbyaddr'):
            raise RuntimeUnavailable('network name resolution prohibited in inference worker')
        if event == 'subprocess.Popen':
            raise RuntimeUnavailable('subprocesses prohibited inside inference child')
    sys.addaudithook(guard)


class LocalModels:
    def __init__(self, cache_dir: Path):
        self.cache_dir = cache_dir
        self.loaded = {}
        self.devices = {}
        self.fallbacks = {}

    def status(self):
        return {role: {'loaded': True, 'device': self.devices[role],
                       'backend': 'mlx' if self.devices[role] == 'metal' else 'torch',
                       'dtype': '4bit' if role == 'generation' else 'float32',
                       'fallback_reason': self.fallbacks.get(role)} for role in self.loaded}

    def _path(self, role):
        status = installation_status(self.cache_dir)
        if not status['ready']:
            raise RuntimeUnavailable('pinned local models/environment not installed; run lean_research_setup.py')
        return status['models'][role]['path']

    def _torch_model(self, role, cpu=False):
        import torch
        from transformers import AutoConfig, AutoModel, AutoModelForCausalLM, AutoTokenizer

        if role in self.loaded:
            return self.loaded[role]
        path = self._path(role)
        device = 'mps' if not cpu and torch.backends.mps.is_available() else 'cpu'
        if device == 'cpu' and role not in self.fallbacks:
            self.fallbacks[role] = 'MPS unavailable; using CPU float32'
        torch.set_num_threads(2)
        tokenizer = AutoTokenizer.from_pretrained(path, local_files_only=True,
                                                  trust_remote_code=False,
                                                  padding_side='right' if role == 'embedding' else 'left')
        if role == 'embedding':
            # Retrieval uses the text tower alone. Building the vision and audio
            # towers would load 740M instead of 271M, and the audio tower has no
            # SDPA kernel at all, so requesting sdpa fails the whole load. The
            # 512->768 projection lives inside the text tower, which upstream
            # notes is equivalent to projecting after the mean pool.
            config = AutoConfig.from_pretrained(path, local_files_only=True)
            config.vision_config = None
            config.audio_config = None
            wrapper = AutoModel.from_pretrained(path, config=config, local_files_only=True,
                                                trust_remote_code=False, dtype=torch.float32,
                                                attn_implementation='sdpa').eval()
            model = getattr(wrapper, 'language_model', wrapper)
        else:
            model = AutoModelForCausalLM.from_pretrained(path, local_files_only=True, trust_remote_code=False,
                                                         dtype=torch.float32,
                                                         attn_implementation='sdpa').eval()
        # Record selected device before transfer so a failed MPS transfer can retry on CPU.
        self.devices[role] = device
        model = model.to(device)
        self.loaded[role] = (model, tokenizer)
        return model, tokenizer

    def _search(self, request, role):
        import torch
        model, tokenizer = self._torch_model(role)
        values = request['texts' if role == 'embedding' else 'documents']
        result = []
        # Right-padding + last-nonpad pooling permits real embedding batches on
        # MPS. Rerank must keep its last-position chat suffix, so use unpadded
        # single items there to avoid the MPS mixed-left-padding NaN path.
        batch_size = 1 if role == 'reranker' and self.devices[role] == 'mps' else BATCH_SIZE
        with torch.inference_mode():
            for start in range(0, len(values), batch_size):
                remaining(request['deadline'])
                batch = values[start:start + batch_size]
                if role == 'embedding':
                    inputs = tokenizer([embedding_text(t, request.get('query', False)) for t in batch],
                                       padding=True, truncation=True, max_length=CONTEXT_TOKENS,
                                       return_tensors='pt').to(self.devices[role])
                    hidden = model(**inputs, use_cache=False).last_hidden_state
                    if hidden.shape[-1] != EMBEDDING_DIMENSIONS:
                        raise RuntimeUnavailable(
                            f'embedding width {hidden.shape[-1]} is not the pinned '
                            f'{EMBEDDING_DIMENSIONS}; check models.json and the projection head')
                    pooled = mean_pool(hidden, inputs['attention_mask'])
                    output = torch.nn.functional.normalize(pooled, p=2, dim=1)
                else:
                    inputs = reranker_inputs(tokenizer, request['query'], batch).to(self.devices[role])
                    no, yes = yes_no_ids(tokenizer)
                    # Official last-position logits; avoid allocating all sequence vocabulary logits.
                    logits = model(**inputs, use_cache=False, logits_to_keep=1).logits[:, -1, :]
                    output = torch.softmax(logits[:, [no, yes]].float(), dim=1)[:, 1]
                if not torch.isfinite(output).all().item():
                    raise RuntimeError('non-finite inference output')
                result.extend(output.cpu().tolist())
        remaining(request['deadline'])
        return result

    def run(self, request):
        if request['op'] == 'generate':
            return self._generate(request)
        role = 'embedding' if request['op'] == 'embed' else 'reranker'
        if (role == 'embedding' and MLX_EMBEDDING_MODULE
                and self.devices.get(role) not in ('mps', 'cpu')):
            try:
                return self._mlx_embed(request)
            except RuntimeDeadline:
                raise
            except (ImportError, RuntimeError, OSError, ValueError) as exc:
                # Deadline/cancellation exceptions are never converted to a
                # fallback retry. Supervisor still enforces blocked kernels.
                reason = f'MLX failure ({type(exc).__name__}); using Torch fallback'
            self.loaded.pop(role, None)
            import gc
            gc.collect()
            mx = sys.modules.get('mlx.core')
            if mx is not None:
                mx.clear_cache()
            self.fallbacks[role] = reason
            remaining(request['deadline'])
        try:
            return self._search(request, role)
        except (RuntimeError, NotImplementedError) as exc:
            if self.devices.get(role) != 'mps':
                raise
            # Drop model and traceback references before loading CPU weights.
            failure = 'non-finite output' if str(exc) == 'non-finite inference output' else type(exc).__name__
            reason = f'MPS failure ({failure}); retried on CPU float32'
        self.loaded.pop(role, None)
        import gc
        import torch
        gc.collect()
        torch.mps.empty_cache()
        self.fallbacks[role] = reason
        remaining(request['deadline'])
        self._torch_model(role, cpu=True)
        return self._search(request, role)

    def _mlx_embed(self, request):
        from .mlx_embedding import MLXEmbedding
        remaining(request['deadline'])
        if 'embedding' not in self.loaded:
            self.loaded['embedding'] = MLXEmbedding(Path(self._path('embedding')))
            self.devices['embedding'] = 'metal'
        return self.loaded['embedding'].embed(
            [embedding_text(text, request.get('query', False)) for text in request['texts']],
            deadline=request['deadline'])

    def _generate(self, request):
        import mlx.core as mx
        from mlx_lm import load, stream_generate
        from mlx_lm.sample_utils import make_sampler

        if 'generation' not in installation_status(self.cache_dir)['models']:
            raise RuntimeUnavailable('no generation model is pinned; this runtime serves retrieval only')
        if 'generation' not in self.loaded:
            path = self._path('generation')  # Existence checked before mlx-lm's download branch.
            if not mx.metal.is_available():
                raise RuntimeUnavailable('MLX generation requires Apple Metal')
            self.loaded['generation'] = load(path, tokenizer_config={
                'local_files_only': True, 'trust_remote_code': False})
            self.devices['generation'] = 'metal'
        model, tokenizer = self.loaded['generation']
        tokens = tokenizer.apply_chat_template([{'role': 'user', 'content': request['prompt']}],
                                               tokenize=True, add_generation_prompt=True)
        if len(tokens) + request['max_tokens'] > GENERATION_CONTEXT:
            raise ValueError('generation prompt plus output exceeds 8192-token runtime limit')
        parts = []
        stream = stream_generate(model, tokenizer, prompt=tokens, max_tokens=request['max_tokens'],
                                 sampler=make_sampler(temp=0.0), prefill_step_size=256)
        try:
            for response in stream:
                remaining(request['deadline'])
                parts.append(response.text)
        finally:
            stream.close()
        return ''.join(parts)
