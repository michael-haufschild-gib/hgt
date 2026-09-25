"""Independent trial-factor/60-digit audit at the prescribed endpoint. Runpod only."""
import json
from pathlib import Path
import time
import mpmath as mp

ROOT = Path(__file__).resolve().parent


def trial_data(n):
    remaining, p, parity, squarefree, divisor_count = n, 2, 0, True, 1
    while p*p <= remaining:
        exponent = 0
        while remaining % p == 0:
            exponent += 1
            remaining //= p
        if exponent:
            parity += 1
            divisor_count *= exponent+1
            squarefree &= exponent == 1
        p += 1
    if remaining > 1:
        parity += 1
        divisor_count *= 2
    return ((-1)**parity if squarefree else 0), divisor_count


def audit():
    started = time.monotonic()
    mp.mp.dps = 60
    M = 4096
    values = [trial_data(n) for n in range(1,M+1)]
    mu = [0]+[v[0] for v in values]
    tau = [0]+[v[1] for v in values]
    roots = [mp.sqrt(n) for n in range(M+2)]
    D, A = [mp.mpf(0)], [mp.mpf(0)]
    log_factorial, divisor_sum = mp.mpf(0), 0
    for q in range(1,M+1):
        log_factorial += mp.log(q)
        divisor_sum += tau[q]
        D.append(log_factorial-divisor_sum+2*mp.euler*q)
        A.append(A[-1]+D[-1]/(roots[q+1]+roots[q]))
    lam = [mp.mpf(0) for _ in range(M+1)]
    for p in range(2,M+1):
        if tau[p] == 2:
            pk = p
            while pk <= M:
                lam[pk] = mp.log(p)
                pk *= p
    psi, direct = mp.mpf(0), mp.mpf(0)
    for k in range(1,M):
        psi += lam[k]
        direct += (psi-k+2*mp.euler)/(roots[k+1]+roots[k])
    direct /= M
    channels = [mp.mpf(0)]
    for d in range(1,M+1):
        q = M//d
        channels.append(mu[d]*(roots[d]*A[q-1]+D[q]*(M-d*q)/(roots[M]+roots[d*q]))/M)
    assert abs(sum(channels)-direct) < mp.mpf("1e-50")
    fibers = {}
    for y, primes in [(3,[2,3]),(5,[2,3,5])]:
        B = {}
        for d in range(1,M+1):
            if not mu[d]:
                continue
            r = d
            for p in primes:
                while r % p == 0:
                    r //= p
            B[r] = B.get(r,mp.mpf(0))+channels[d]
        fibers[y] = B
    Q = {y:sum(v*v for v in B.values()) for y,B in fibers.items()}
    B = fibers[3]
    cross = 2*sum(v*B.get(5*r,mp.mpf(0)) for r,v in B.items() if r%5)
    assert abs(Q[5]-Q[3]-cross) < mp.mpf("1e-50")
    data = json.loads((ROOT/"arithmetic-discovery.json").read_text())
    old = data["bands"][0]["rows"][0]
    assert old["M"] == M
    errors = {y:abs(mp.mpf(old["ensembles"][[1,2,3,5,11,31].index(y)])-Q[y]) for y in Q}
    assert max(errors.values()) < mp.mpf("1e-13")
    result = dict(M=M, dps=mp.mp.dps, source=mp.nstr(direct,55),
                  ensemble={str(y):mp.nstr(q,55) for y,q in Q.items()},
                  prime_five_change=mp.nstr(Q[5]-Q[3],55),
                  exact_merge_cross=mp.nstr(cross,55),
                  float_errors={str(y):mp.nstr(err,10) for y,err in errors.items()},
                  seconds=time.monotonic()-started)
    (ROOT/"audit.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    audit()
