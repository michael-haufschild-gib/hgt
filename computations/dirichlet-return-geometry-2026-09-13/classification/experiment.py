import json, time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
import mpmath as m
import fold

def check(job):
    row, dps = job
    start = time.monotonic()
    m.mp.dps = dps
    params = json.loads(Path('parameters.json').read_text())[str(row['q'])]['120' if dps == 100 else '180']
    data, pieces = fold.evaluator(row['q'], row['direction'], params)
    t = m.mpf(row['t'])
    v = data(t)
    X, D, W = pieces(t)
    lam, kap = v['lam'], v['kappa']
    fk = lam**2 * W[0]
    fl = D[0] + 2*kap*lam*W[0]
    ftl = D[1] + 2*kap*lam*W[1]
    ftk = lam**2 * W[1]
    determinant = fl*ftk-fk*ftl
    values = dict(
        unfolding_determinant=determinant,
        determinant_identity_error=abs(determinant-lam**2*v['B']),
        kappa_second_from_derivative=m.diff(lambda x:data(x)['kappa_prime'],t),
        kappa_second_from_chart=m.diff(lambda x:data(x)['kappa'],t,2),
        lambda_prime=v['lambda_prime'],
    )
    return dict(t=row['t'], dps=dps, seconds=time.monotonic()-start,
                **{k:m.nstr(z,dps) for k,z in values.items()})

if __name__ == '__main__':
    rows=[json.loads(line) for line in Path('validation.jsonl').read_text().splitlines()]
    rows=[r for r in rows if r['dps']==160]
    with ProcessPoolExecutor(max_workers=4) as pool, open('classification.jsonl','w',buffering=1) as out:
        for future in as_completed([pool.submit(check,(row,dps)) for row in rows for dps in [100,160]]):
            out.write(json.dumps(future.result())+'\n')
