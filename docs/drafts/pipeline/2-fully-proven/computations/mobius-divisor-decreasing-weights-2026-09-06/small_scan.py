"""Refine the first finite failure; Runpod only."""
import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
from pathlib import Path
import json
import numpy as np
import search
ROOT=Path(__file__).resolve().parent
z=np.load('/root/rh-mobius-divisor-coordination-20260906/source.npz')
search.D=z['defect'][:1025];search.D[0]=0;search.MU=z['mu'][:1025]
small=[search.solve(M) for M in range(2,17)]
(ROOT/'small.json').write_text(json.dumps(small,indent=2)+'\n')
first=next(row for row in small if any(r.get('ratio',0)>1+1e-9 for r in row['orientations']))
print(json.dumps(first,indent=2))
