"""Runpod-only independent finite-divisor/Hurwitz verification and diagnostics."""
import os
for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import concurrent.futures
import json
import math
import time
import mpmath as mp


def w_value(s, p, factor, order):
    u = mp.conj(s)
    head = max(40, int(mp.ceil(factor*mp.im(s)/p)))
    total = mp.mpc(0)
    for n in range(1,head+1):
        x = mp.mpf(p*n)
        remainder = -mp.zeta(u,x+1)-x**(1-u)/(1-u)-x**(-u)/2
        total += mp.mpf(n)**(-s)*remainder
    total *= mp.mpf(p)**(1-s)
    for k in range(1,order+1):
        coefficient = -mp.bernoulli(2*k)*mp.rf(u,2*k-1)/mp.factorial(2*k)
        total += coefficient*mp.mpf(p)**(2-2*mp.re(s)-2*k)*mp.zeta(2*mp.re(s)+2*k-1,head+1)
    return total


def divisor_phase(s, k, primes, factor, order):
    terms = [(1,1)]
    for q in primes[:k]:
        terms += [(d*q,-sign) for d,sign in terms]
    D = mp.conj(s)*(mp.conj(s)+1)
    return sum((sign*w_value(s,d,factor,order)/(d*D) for d,sign in terms),mp.mpc(0))


def task(spec):
    mp.mp.dps = 90
    index,k,kind,primes = spec
    s = mp.zetazero(index)
    a = divisor_phase(s,k,primes,4,16)
    b = divisor_phase(s,k,primes,7,24)
    result = {"index":index,"k":k,"kind":kind,"height":mp.nstr(mp.im(s),85),
        "zeta_abs":mp.nstr(abs(mp.zeta(s)),12),"phase_real":mp.nstr(mp.re(b),75),
        "phase_imag":mp.nstr(mp.im(b),75),"configuration_difference":mp.nstr(abs(a-b),12)}
    if kind == "K":
        c = divisor_phase(s,k+1,primes,7,24)
        result["next_phase_imag"] = mp.nstr(mp.im(c),75)
        result["phase_increment"] = mp.nstr(mp.im(c-b),75)
    return result


if __name__ == "__main__":
    started = time.time()
    data = json.load(open("results.json"))
    primes = data["primes"]
    js,ks = [],[]
    counts = []
    for row in data["results"]:
        c = row["controls"][1]
        for k in range(1,len(c["phases"])):
            js.append((c["phases"][k][1],row["index"],k))
        for k in range(1,len(c["phases"])-1):
            ks.append((c["phases"][k+1][1]-c["phases"][k][1],row["index"],k))
    _,ji,jk = max(js)
    _,ki,kk = min(ks)
    specs = [(9,0,"J",primes),(ji,jk,"J",primes),(ki,kk,"K",primes)]
    print(json.dumps({"selected":specs}),flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(task,specs))
    for k in range(len(primes)+1):
        phases = [r["controls"][1]["phases"][k][1] for r in data["results"]]
        counts.append({"k":k,"positive":sum(x>1e-9 for x in phases),
            "negative":sum(x < -1e-9 for x in phases),"min":min(phases),"max":max(phases)})
    out = {"digits":90,"seconds":time.time()-started,"method":"finite divisor sum of independent Hurwitz remainder evaluations",
        "configurations":[[4,16],[7,24]],"results":results,"scan_signs_by_k":counts,
        "warning":"Numerical diagnostics, not interval certificates or Lean counterexamples."}
    json.dump(out,open("verification.json","w"),indent=2)
    print(json.dumps(out,indent=2),flush=True)
