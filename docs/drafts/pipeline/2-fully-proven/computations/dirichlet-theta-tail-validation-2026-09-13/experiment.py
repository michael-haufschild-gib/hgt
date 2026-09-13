import json
import multiprocessing as mp
import time
from pathlib import Path
import carrier

if __name__=='__main__':
    start=time.monotonic()
    params=json.loads(Path('parameters.json').read_text())
    rows=[json.loads(s) for s in Path('validation.jsonl').read_text().splitlines() if json.loads(s)['dps']==160]
    jobs=[(r,params[str(r['q'])]['180'],offset,cutoff) for r in rows for offset in ['0','.125'] for cutoff in ['3.5','4']]
    with mp.Pool(14) as pool,open('tail-validation.jsonl','w',buffering=1) as out:
        for row in pool.imap_unordered(carrier.independent,jobs):out.write(json.dumps(row)+'\n')
    Path('summary.json').write_text(json.dumps(dict(rows=len(jobs),seconds=time.monotonic()-start),indent=2)+'\n')
