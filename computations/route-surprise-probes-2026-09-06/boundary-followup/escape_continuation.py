"""Follow optimizer mass toward infinity while retaining its first-moment excess."""
import os
for key in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from boundary_search import literal_moments, record
from tail_interventions import data_with_jets, atomic_jets


def run(spec):
    floor,best,gs = spec
    mp.mp.dps = 110
    a0 = (mp.pi if floor<4 else mp.mpf(6))+mp.mpf(str(best["x"][0]))
    t,l = mp.mpf(str(best["t"])),mp.mpf(str(best["l"]))
    c = sum(mp.mpf(str(w))*(mp.mpf(str(g))-3) for w,g in zip(best["weights"],best["nodes"]))
    g = mp.mpf(gs)
    epsilon = c/(g-3)
    x0 = mp.log(a0/mp.pi)/2
    mass = literal_moments(a0)[0]
    d = data_with_jets(x0+t,t,lambda x:atomic_jets(x,x0,mass,[mp.mpf(3),g],[1-epsilon,epsilon]))
    row = record(d,mass,epsilon,l)
    row.update(floor=str(floor),left_A=mp.nstr(a0,45),t=mp.nstr(t,45),g=gs,
        excess=mp.nstr(c,45),mass=mp.nstr(mass,45))
    return row


if __name__ == "__main__":
    start = time.monotonic()
    with open("interior-results.json") as f:
        raw = json.load(f)["results"]
    bests = [(floor,min((r["best"] for r in raw if r["spec"][1]==floor),key=lambda r:r["score"]))
        for floor in sorted(set(r["spec"][1] for r in raw))]
    specs = [(floor,best,"1e"+str(j)) for floor,best in bests for j in range(4,19)]
    with ProcessPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(run,specs))
    with open("escape-results.json","w") as f:
        json.dump(dict(seconds=time.monotonic()-start,rows=rows),f,indent=2)
    for row in rows:
        print(json.dumps({k:row[k] for k in ("floor","g","h2_scaled","c3_scaled","gates","counterexample")}),flush=True)
