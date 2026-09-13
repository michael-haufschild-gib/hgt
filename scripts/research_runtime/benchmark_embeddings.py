"""Bounded offline comparison on fixed REAL corpus rows; no corpus writes.

Each backend runs in an owned child, preventing simultaneous model residency.
MLX loads original Qwen weights through pinned mlx-lm Qwen3Model, no conversion
or third-party quantized artifact. Only right-padding follows valid tokens;
causal attention ensures later padding cannot affect those hidden states.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import time

from .config import CONTEXT_TOKENS, DEFAULT_CACHE_DIR, RUNTIME_HOME, installation_status, offline_environment
from .processes import terminate_owned, cancellation_signals


def fixtures(cache_dir, selections=None):
    database = cache_dir/'corpus.sqlite3'
    con=sqlite3.connect(f'file:{database}?mode=ro',uri=True,timeout=1)
    con.execute('PRAGMA query_only=ON')
    groups={}
    metadata={}
    for label,view,long in (selections or [('statement','statement',False),('proof','proof',False),('long','proof',True)]):
        low,high=con.execute('SELECT min(id),max(id) FROM documents WHERE view=?',(view,)).fetchone()
        # Prose IDs are sparse clusters among declarations. Sample ordinal
        # positions in that view so ID gaps cannot repeat the same document.
        prose_ids = ([r[0] for r in con.execute('SELECT id FROM documents WHERE view=? ORDER BY id', (view,))]
                     if view == 'prose' else None)
        rows=[]
        seen=set()
        for i in range(32):
            target=low+(high-low)*i//32
            if prose_ids is not None:
                target = prose_ids[len(prose_ids)*i//32]
            extra=' AND length(text)>=4500' if long else ''
            row=con.execute('SELECT id,module,content_hash,text FROM documents WHERE view=? AND id>=?'+extra+
                            ' ORDER BY id LIMIT 1',(view,target)).fetchone()
            if row is None or row[0] in seen:
                raise RuntimeError('fixture sampling could not select 32 unique rows')
            seen.add(row[0]); rows.append(dict(zip(('id','module','content_hash','text'),row)))
        groups[label]=rows
        metadata[label]={'view':view,'count':32,'characters':sum(len(r['text']) for r in rows),
                         'min_chars':min(len(r['text']) for r in rows),'max_chars':max(len(r['text']) for r in rows)}
    con.close()
    result={'database':str(database),'sampling':'32 evenly spaced ID targets per view; long proof length >=4500',
            'groups':groups,'metadata':metadata,
            'queries':['Given a lower bound on a quadratic form, prove coercivity.',
                       'Find a theorem about continuity and convergence of a sequence.',
                       'Commutativity of addition for natural numbers.',
                       'Show that the measure of a union is at most the sum of the measures.']}
    return result


def child(backend, fixture, output, group=None):
    if backend == 'runtime':
        from lean_research_runtime import RuntimeClient
        data = json.loads(fixture.read_text())
        results = {}
        with RuntimeClient(DEFAULT_CACHE_DIR) as client:
            start = time.monotonic()
            client.embed(['theorem refl (n : ℕ) : n = n := rfl'], deadline=start+120)
            load_seconds = time.monotonic()-start
            for label, rows in data['groups'].items():
                if group and label != group:
                    continue
                start = time.monotonic()
                vectors = client.embed([r['text'] for r in rows], deadline=start+120)
                seconds = time.monotonic()-start
                results[label] = {'seconds': seconds, 'docs_per_second': len(rows)/seconds,
                                  'vectors': vectors}
                print(json.dumps({'backend': backend, 'group': label, 'seconds': seconds,
                                  'docs_per_second': len(rows)/seconds}), flush=True)
            queries = client.embed(data['queries'], query=True, deadline=time.monotonic()+120)
            status = client.status()
        output.write_text(json.dumps({'backend': backend, 'load_seconds': load_seconds,
                                     'results': results, 'queries': queries, 'status': status}))
        return
    from .adapters import embedding_text, enforce_offline
    enforce_offline()
    import numpy as np
    from transformers import AutoTokenizer
    path=Path(installation_status(DEFAULT_CACHE_DIR)['models']['embedding']['path'])
    data=json.loads(fixture.read_text())
    tokenizer=AutoTokenizer.from_pretrained(str(path),local_files_only=True,trust_remote_code=False,padding_side='right')
    start=time.monotonic()
    if backend in ('cpu','mps'):
        import torch
        from transformers import AutoModel
        torch.set_num_threads(2)
        model=AutoModel.from_pretrained(str(path),local_files_only=True,trust_remote_code=False,
                                       dtype=torch.float32,attn_implementation='sdpa').eval().to(backend)
        def encode(texts):
            x=tokenizer(texts,padding=True,truncation=True,max_length=CONTEXT_TOKENS,return_tensors='pt').to(backend)
            with torch.inference_mode():
                h=model(**x,use_cache=False).last_hidden_state
                v=h[torch.arange(h.shape[0],device=backend),x['attention_mask'].sum(dim=1)-1]
                return torch.nn.functional.normalize(v.float(),dim=1).cpu().numpy()
    else:
        import mlx.core as mx
        from mlx_lm.models.qwen3 import ModelArgs, Qwen3Model
        # Official embedding snapshot has bare base-model keys, not the
        # generative wrapper's model.* keys. Load its hidden-state model directly.
        model=Qwen3Model(ModelArgs.from_dict(json.loads((path/'config.json').read_text())))
        model.load_weights(str(path/'model.safetensors'),strict=True)
        model.eval()
        mx.eval(model.parameters())
        if backend.startswith('mlx-f32'):
            model.set_dtype(mx.float32)
            mx.eval(model.parameters())
        if backend.startswith('mlx-q8'):
            import mlx.nn as nn
            nn.quantize(model,group_size=64,bits=8)
            mx.eval(model.parameters())
        forward=mx.compile(model) if backend.endswith('compiled') else model
        def encode(texts):
            options={'pad_to_multiple_of':32} if backend.endswith('compiled') else {}
            x=tokenizer(texts,padding=True,truncation=True,max_length=CONTEXT_TOKENS,return_tensors='np',**options)
            ids=mx.array(x['input_ids'])
            h=forward(ids)
            v=h[mx.arange(len(texts)),mx.array(x['attention_mask'].sum(axis=1)-1)].astype(mx.float32)
            v=v/mx.maximum(mx.linalg.norm(v,axis=1,keepdims=True),1e-12)
            mx.eval(v)
            return np.array(v)
    load_seconds=time.monotonic()-start
    batch=8 if backend.endswith('sorted') else 4
    # One short warmup separates model load/kernel compilation from comparisons.
    encode(['theorem refl (n : ℕ) : n = n := rfl'])
    results={}
    for label, rows in data['groups'].items():
        if group and label != group:
            continue
        begin=time.monotonic()
        order=list(range(32))
        if backend.endswith(('sorted','compiled')):
            order.sort(key=lambda i:min(CONTEXT_TOKENS,len(tokenizer.encode(rows[i]['text']))))
        vectors=np.concatenate([encode([rows[j]['text'] for j in order[i:i+batch]]) for i in range(0,32,batch)])
        vectors=vectors[np.argsort(order)]
        seconds=time.monotonic()-begin
        if not np.isfinite(vectors).all():
            raise RuntimeError(f'{backend}/{label} non-finite output')
        results[label]={'seconds':seconds,'docs_per_second':32/seconds,'vectors':vectors.tolist()}
        print(json.dumps({'backend':backend,'group':label,'seconds':seconds,'docs_per_second':32/seconds}),flush=True)
    q=encode([embedding_text(q,True) for q in data['queries']])
    output.write_text(json.dumps({'backend':backend,'load_seconds':load_seconds,'batch_size':batch,
                                 'results':results,'queries':q.tolist()}))


@cancellation_signals()
def owned_run(command, seconds):
    process=subprocess.Popen(command,env=offline_environment(),start_new_session=True)
    try:
        code=process.wait(timeout=seconds)
        if code:
            raise RuntimeError(f'benchmark exited with {code}')
    finally:
        terminate_owned(process)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend',choices=('cpu','mps','mlx','mlx-f32','mlx-f32-sorted','mlx-q8-sorted','mlx-f32-compiled','runtime'))
    parser.add_argument('--child',action='store_true')
    parser.add_argument('--group', choices=('statement', 'proof', 'long', 'prose'))
    parser.add_argument('--fixtures-only',action='store_true')
    parser.add_argument('--prose-fixtures', action='store_true', help='append real prose without replacing existing samples')
    args=parser.parse_args()
    directory=RUNTIME_HOME/'cache'; directory.mkdir(exist_ok=True)
    fixture=directory/'real-embedding-fixtures.json'
    if args.prose_fixtures:
        data = json.loads(fixture.read_text())
        prose = fixtures(DEFAULT_CACHE_DIR, [('prose', 'prose', False)])
        data['groups'].update(prose['groups'])
        data['metadata'].update(prose['metadata'])
        fixture.write_text(json.dumps(data))
        print(json.dumps(prose['metadata']))
        return
    if args.fixtures_only:
        fixture.write_text(json.dumps(fixtures(DEFAULT_CACHE_DIR)))
        print(json.dumps(json.loads(fixture.read_text())['metadata']))
        return
    if args.child:
        suffix = '-'+args.group if args.group else ''
        child(args.backend,fixture,directory/f'embedding-{args.backend}{suffix}.json', args.group)
        return
    for backend in ([args.backend] if args.backend else ['cpu','mps','mlx']):
        command = [sys.executable,'-m','research_runtime.benchmark_embeddings','--child','--backend',backend]
        if args.group:
            command.extend(['--group', args.group])
        owned_run(command,300)


if __name__=='__main__': main()
